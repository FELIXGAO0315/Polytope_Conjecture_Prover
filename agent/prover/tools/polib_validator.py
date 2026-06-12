"""
agent/tools/polib_validator.py

Post-formalization Polib.lean integrity check and auto-repair.

This module is the SINGLE place responsible for detecting and repairing all
known Polib.lean integrity issues.  After every formalization run, the
formalizer calls `PolibValidator.validate_and_repair()` before reporting
final results.  The contract is:

  * Either Polib builds cleanly when the method returns (success=True),
  * or all automatic repairs have been exhausted and `final_errors` describes
    what remains (success=False) — but the file is still in the best shape
    we can achieve automatically.

No manual intervention should ever be needed.

─────────────────────────────────────────────────────────────────────────────
KNOWN ISSUE TAXONOMY
─────────────────────────────────────────────────────────────────────────────

Phase 1 — Structural pre-flight  (no lake build required)
  1. Duplicate section headers
       Same node_id appears under two consecutive `-- === NodeId (status) ===`
       markers.  Happens when `PolibManager.save` re-saves code that was
       loaded from Polib (the loaded code already contains a section header,
       which then becomes part of the body of the new section).
       Fix: keep the section whose body contains the actual `lemma/theorem
       NodeId` declaration; remove any header-only duplicates.

  2. Empty sections
       A section header exists but no `lemma/theorem/def/abbrev NodeId`
       declaration follows before the next section.  Can arise from the same
       re-save bug or from a partial save that was aborted mid-write.
       Fix: remove the empty section.

  3. Embedded metadata in section body
       A `-- === ... (proved|partial) ===` or `-- quality_score:` line
       appears inside the body of a section (after its own header lines).
       Can happen when the duplicate-section scenario occurs across different
       node IDs.
       Fix: strip those lines from the body.

Phase 2 — Build verification loop  (requires lake)
  4. Inline sorry with trailing text
       `sorry [text]` or `sorry SomeName` — Lean 4 does not allow text
       after `sorry` on the same line (other than a `--` comment).
       Fix: split into `-- <text>` then `sorry` on the next line.

  5. Arbitrary build errors
       Any other hard `error:` emitted by lean when building Polib.lean.
       These arise from LLM-generated code that compiled in isolation but
       breaks when placed alongside existing Polib content.
       Fix attempt: inline-sorry repair first (covers a broad class of
       trailing-token errors); if that fails, remove the section entirely
       so the rest of Polib remains usable.

─────────────────────────────────────────────────────────────────────────────
THREAD-SAFETY
─────────────────────────────────────────────────────────────────────────────

`validate_and_repair()` is called once from the main thread after all worker
threads have finished.  No internal locking is needed.
"""
from __future__ import annotations

import os
import re
import subprocess
import time
import uuid
from collections import defaultdict
from dataclasses import dataclass, field
from pathlib import Path
from typing import Callable

# ─────────────────────────────────────────────────────────────────────────────
# Compiled regexes
# ─────────────────────────────────────────────────────────────────────────────

# Strip ANSI / VT100 colour codes that lake may emit even to pipes.
_ANSI_RE = re.compile(r'\x1b\[[0-9;]*[A-Za-z]|\x1b\][^\x07]*\x07')

# Matches the opening line of a node section: `-- === NodeId (proved|partial) ===`
# Requires a leading `\n` so we can anchor to top-level boundaries.
_SECTION_BOUNDARY_RE = re.compile(
    r'\n(-- === (\w+) \((proved|partial)\) ===\n)',
)

# Matches the same header at the very start of a line (for line-level scanning).
_SECTION_HEADER_LINE_RE = re.compile(
    r'^-- === (\w+) \((proved|partial)\) ===$'
)

# Matches the `-- quality_score:` metadata line produced by PolibManager.
_QUALITY_SCORE_LINE_RE = re.compile(
    r'^-- quality_score:[ \t][^\n]*$'
)

# Matches a `sorry` tactic followed by non-comment text on the SAME line.
# In Lean 4 tactic mode `sorry` closes the goal; anything that follows on the
# same line (other than a `--` comment) is a syntax error.
# IMPORTANT: uses [ \t]+ (not \s+) so it never crosses newlines —
# `sorry\n  ·` must NOT be treated as inline sorry.
_INLINE_SORRY_RE = re.compile(r'^(?P<indent>[ \t]*)sorry[ \t]+(?P<rest>[^-\n].*)$')

# Matches hard-error lines in `lake build Polib` output for Polib.lean.
# Lake may emit paths as `Polib.lean:`, `./Polib.lean:`, or with a leading
# `error: ` prefix, and the inner `error:` keyword before the message is
# sometimes present and sometimes omitted.  Mirror the flexible format used
# by LeanCompiler._ERROR_LINE_RE so we never miss a build error.
_POLIB_ERROR_RE = re.compile(
    r'^(?:error:\s+)?(?:[^:\n]*/)?Polib\.lean:(?P<line>\d+):(?P<col>\d+):\s+(?:error:\s+)?(?P<msg>.+)$'
)

# Declaration forms that count as "the target lemma" for a section.
_DECL_RE = re.compile(
    r'^(?:private\s+|noncomputable\s+|protected\s+)*'
    r'(?:lemma|theorem|def|abbrev)\s+'
)


# ─────────────────────────────────────────────────────────────────────────────
# Data classes
# ─────────────────────────────────────────────────────────────────────────────

@dataclass(frozen=True)
class PolibError:
    """One hard error parsed from `lake build Polib` output."""
    line: int    # 1-indexed line in Polib.lean
    col: int
    message: str

    def __str__(self) -> str:
        return f"Polib.lean:{self.line}:{self.col}: {self.message}"


@dataclass
class _Section:
    """
    One node section inside Polib.lean.

    `text` is the raw section content starting from `-- === NodeId …` through
    to (but not including) the `\n` that separates it from the next section.
    It does NOT include the leading `\n` that acts as the inter-section separator.
    """
    node_id: str
    status: str   # "proved" | "partial"
    text: str     # full text: header line + quality line + body

    def has_target_decl(self) -> bool:
        """True when the body contains `lemma/theorem/def/abbrev <node_id>`."""
        pattern = re.compile(
            r'^(?:private\s+|noncomputable\s+|protected\s+)*'
            r'(?:lemma|theorem|def|abbrev)\s+' + re.escape(self.node_id),
            re.MULTILINE,
        )
        return bool(pattern.search(self.text))

    def has_sorry(self) -> bool:
        return bool(re.search(r'\bsorry\b', self.text))


@dataclass
class PolibValidationResult:
    """
    Complete outcome of a single `validate_and_repair()` call.

    Attributes
    ----------
    success
        True when Polib.lean builds cleanly on return.
    deduped_sections
        Node IDs for which duplicate (header-only) section entries were removed.
    cleaned_sections
        Node IDs whose section bodies had embedded metadata lines stripped.
    removed_empty_sections
        Node IDs whose sections contained no target declaration and were removed.
    repaired_sections
        Node IDs whose sections were fixed in-place during the build loop
        (e.g. inline-sorry annotation corrected).
    removed_sections
        Node IDs whose sections were deleted during the build loop because no
        automatic repair applied.  Caller must downgrade these in session state.
    preamble_errors
        Errors in the preamble (before any node section).  These are structural
        and cannot be auto-repaired; they require manual intervention.
    repair_rounds
        Number of build-loop repair iterations performed (0 = already clean).
    final_errors
        Remaining build errors when success is False.
    """
    success: bool
    deduped_sections: list[str] = field(default_factory=list)
    cleaned_sections: list[str] = field(default_factory=list)
    removed_empty_sections: list[str] = field(default_factory=list)
    repaired_sections: list[str] = field(default_factory=list)
    removed_sections: list[str] = field(default_factory=list)
    preamble_errors: list[PolibError] = field(default_factory=list)
    repair_rounds: int = 0
    final_errors: list[PolibError] = field(default_factory=list)

    @property
    def all_removed(self) -> list[str]:
        """Union of all node IDs removed from Polib for any reason."""
        return self.removed_empty_sections + self.removed_sections


# ─────────────────────────────────────────────────────────────────────────────
# Validator
# ─────────────────────────────────────────────────────────────────────────────

class PolibValidator:
    """
    Validates and repairs Polib.lean after formalization completes.

    Usage
    -----
    ::
        validator = PolibValidator(
            polib_lean=Path("polib/Polib.lean"),
            workspace=Path("polib"),
            log_fn=lambda msg: print(msg),
        )
        result = validator.validate_and_repair()
        for nid in result.all_removed:
            session.mark_pending(nid, 0, "removed by Polib validator")
    """

    MAX_REPAIR_ROUNDS: int = 5

    def __init__(
        self,
        polib_lean: Path,
        workspace: Path,
        log_fn: Callable[[str], None] | None = None,
        build_timeout: int = 120,
    ):
        """
        Parameters
        ----------
        polib_lean
            Absolute path to Polib.lean.
        workspace
            Root of the Polib lake package (the directory containing
            `lakefile.lean`).  `lake build Polib` is executed here.
        log_fn
            Optional single-argument callable for progress messages.
        build_timeout
            Seconds before a `lake build Polib` call is killed.
        """
        self._polib_lean = Path(polib_lean)
        self._workspace = Path(workspace)
        self._log: Callable[[str], None] = log_fn or (lambda _: None)
        self._timeout = build_timeout

    # ─────────────────────────────────────────────────────────────────────
    # Public API
    # ─────────────────────────────────────────────────────────────────────

    def validate_and_repair(self) -> PolibValidationResult:
        """
        Run all checks and repairs.  Returns a `PolibValidationResult`.
        Check `result.success` to know whether Polib is clean on return.
        """
        result = PolibValidationResult(success=False)

        # ── Phase 1: structural pre-flight ────────────────────────────
        structural_changed = self._phase1_structural(result)
        if structural_changed:
            self._log("  [polib-validate] structural repairs applied — rebuilding")

        # ── Phase 2: build verification loop ──────────────────────────
        ok, errors = self._build()
        if ok:
            result.success = True
            if not structural_changed:
                self._log("  [polib-validate] Polib builds cleanly — no repairs needed")
            else:
                self._log("  [polib-validate] Polib builds cleanly after structural repair")
            return result

        result_errors_initial = list(errors)
        self._log(
            f"  [polib-validate] {len(errors)} build error(s) — "
            f"starting repair loop (max {self.MAX_REPAIR_ROUNDS} rounds)"
        )

        for round_num in range(self.MAX_REPAIR_ROUNDS):
            result.repair_rounds += 1
            content = self._polib_lean.read_text(encoding="utf-8")
            section_map = self._build_line_section_map(content)

            section_errors: dict[str | None, list[PolibError]] = {}
            for err in errors:
                owner = section_map.get(err.line)
                section_errors.setdefault(owner, []).append(err)

            # Preamble errors — record once, cannot be attributed to a node.
            if None in section_errors:
                new_pe = [e for e in section_errors[None] if e not in result.preamble_errors]
                result.preamble_errors.extend(new_pe)
                self._log(
                    f"  [polib-validate] round {round_num + 1}: "
                    f"{len(section_errors[None])} preamble error(s) — "
                    f"manual intervention required"
                )

            sections_with_errors = [s for s in section_errors if s is not None]
            if not sections_with_errors:
                break  # only preamble errors remain; nothing more to do

            made_change = False
            for node_id in sections_with_errors:
                errs = section_errors[node_id]
                repaired = self._try_repair_section(content, node_id, errs)
                if repaired is not None:
                    content = repaired
                    result.repaired_sections.append(node_id)
                    self._log(
                        f"  [polib-repaired] {node_id}: "
                        f"{len(errs)} error(s) fixed in-place"
                    )
                else:
                    content = self._remove_section_by_id(content, node_id)
                    result.removed_sections.append(node_id)
                    self._log(
                        f"  [polib-removed] {node_id}: section deleted "
                        f"(no auto-repair for: "
                        + "; ".join(str(e) for e in errs[:3])
                        + ("…" if len(errs) > 3 else "")
                        + ")"
                    )
                made_change = True

            if made_change:
                self._atomic_write(content)

            ok, errors = self._build()
            if ok:
                result.success = True
                self._log(
                    f"  [polib-validate] Polib builds cleanly after "
                    f"{result.repair_rounds} repair round(s) — "
                    f"repaired={result.repaired_sections}, "
                    f"removed={result.removed_sections}"
                )
                return result

            self._log(
                f"  [polib-validate] round {round_num + 1}: "
                f"{len(errors)} error(s) remain"
            )

        result.final_errors = list(errors)
        self._log(
            f"  [polib-validate] FAILED: {len(result.final_errors)} error(s) remain "
            f"after {result.repair_rounds} repair round(s) — manual intervention required"
        )
        for e in result.final_errors:
            self._log(f"    {e}")
        return result

    # ─────────────────────────────────────────────────────────────────────
    # Phase 1 — Structural pre-flight
    # ─────────────────────────────────────────────────────────────────────

    def _phase1_structural(self, result: PolibValidationResult) -> bool:
        """
        Apply all structural repairs that do not require a lake build.

        Returns True if any change was written to disk.
        """
        content = self._polib_lean.read_text(encoding="utf-8")
        preamble, sections = self._parse_sections(content)
        original_count = len(sections)
        changed = False

        # 1. Strip embedded Polib metadata from section bodies.
        sections, cleaned = self._strip_embedded_metadata(sections)
        if cleaned:
            result.cleaned_sections.extend(cleaned)
            changed = True
            self._log(
                f"  [polib-structural] stripped embedded metadata from: {cleaned}"
            )

        # 2. Remove duplicate section headers (keep the one with the declaration).
        sections, deduped = self._dedup_sections(sections)
        if deduped:
            result.deduped_sections.extend(deduped)
            changed = True
            self._log(
                f"  [polib-structural] removed duplicate headers for: {deduped}"
            )

        # 3. Remove sections that have no target declaration (empty/stub sections).
        sections, empty_removed = self._remove_empty_sections(sections)
        if empty_removed:
            result.removed_empty_sections.extend(empty_removed)
            changed = True
            self._log(
                f"  [polib-structural] removed empty (no-declaration) sections: {empty_removed}"
            )

        if changed:
            new_content = self._reassemble(preamble, sections)
            self._atomic_write(new_content)

        return changed

    def _strip_embedded_metadata(
        self, sections: list[_Section]
    ) -> tuple[list[_Section], list[str]]:
        """
        For each section, strip any `-- === ... (proved|partial) ===` or
        `-- quality_score:` lines that appear *inside the proof body*
        (i.e., after the section's own two header lines).

        These lines are Polib bookkeeping metadata — they are never valid Lean
        and should never appear in the body.
        """
        cleaned_ids: list[str] = []
        result: list[_Section] = []

        for sec in sections:
            lines = sec.text.splitlines(keepends=True)

            # The header block is always exactly the first 1-2 lines:
            #   line 0: -- === NodeId (status) ===
            #   line 1: -- quality_score: ...   (always present)
            # Everything after that is the body.  We must NOT scan further,
            # because additional -- === / -- quality_score: lines in the body
            # are precisely the embedded metadata we want to strip.
            header_end = 0
            if lines and _SECTION_HEADER_LINE_RE.match(lines[0].rstrip("\n")):
                header_end = 1
                if len(lines) > 1 and _QUALITY_SCORE_LINE_RE.match(lines[1].rstrip("\n")):
                    header_end = 2

            # Scan the body for embedded metadata lines.
            body_lines = lines[header_end:]
            clean_body = []
            had_embedded = False
            for line in body_lines:
                stripped = line.rstrip("\n")
                if _SECTION_HEADER_LINE_RE.match(stripped) or _QUALITY_SCORE_LINE_RE.match(stripped):
                    had_embedded = True
                    continue
                clean_body.append(line)

            if had_embedded:
                new_text = "".join(lines[:header_end] + clean_body)
                result.append(_Section(sec.node_id, sec.status, new_text))
                cleaned_ids.append(sec.node_id)
            else:
                result.append(sec)

        return result, cleaned_ids

    def _dedup_sections(
        self, sections: list[_Section]
    ) -> tuple[list[_Section], list[str]]:
        """
        Remove duplicate section entries for the same node_id.

        Strategy: among all sections sharing a node_id, keep exactly one:
          - prefer the section that contains the actual `lemma/theorem NodeId`
            declaration;
          - if none has it (all are header-only stubs), keep the last one
            (most recently appended, highest quality score).
        The relative order of the surviving sections is preserved.
        """
        # Map node_id → list of (original index, section)
        by_node: dict[str, list[tuple[int, _Section]]] = defaultdict(list)
        for i, sec in enumerate(sections):
            by_node[sec.node_id].append((i, sec))

        to_remove: set[int] = set()
        deduped_ids: list[str] = []

        for node_id, entries in by_node.items():
            if len(entries) <= 1:
                continue

            # Find the canonical section: the one with the target declaration.
            canonical_idx = None
            for orig_i, sec in entries:
                if sec.has_target_decl():
                    canonical_idx = orig_i
                    break

            if canonical_idx is None:
                # None has the declaration — keep the last entry.
                canonical_idx = entries[-1][0]

            # Mark all others for removal.
            for orig_i, _ in entries:
                if orig_i != canonical_idx:
                    to_remove.add(orig_i)

            deduped_ids.append(node_id)

        surviving = [sec for i, sec in enumerate(sections) if i not in to_remove]
        return surviving, deduped_ids

    def _remove_empty_sections(
        self, sections: list[_Section]
    ) -> tuple[list[_Section], list[str]]:
        """
        Remove sections that contain no `lemma/theorem/def/abbrev NodeId`
        declaration.  These are header-only stubs with no proof content.
        """
        kept: list[_Section] = []
        removed_ids: list[str] = []

        for sec in sections:
            if sec.has_target_decl():
                kept.append(sec)
            else:
                removed_ids.append(sec.node_id)

        return kept, removed_ids

    # ─────────────────────────────────────────────────────────────────────
    # Phase 2 — Build verification helpers
    # ─────────────────────────────────────────────────────────────────────

    def _build(self) -> tuple[bool, list[PolibError]]:
        """
        Run `lake build Polib` and return (success, errors).

        `success` is True only when exit code is 0 AND no hard-error lines
        are found (handles the rare zero-exit-with-errors case).
        """
        start = time.monotonic()
        try:
            from agent.procutil import set_pdeathsig
            proc = subprocess.run(
                ["lake", "build", "Polib"],
                cwd=self._workspace,
                capture_output=True,
                text=True,
                timeout=self._timeout,
                preexec_fn=set_pdeathsig,
            )
        except subprocess.TimeoutExpired:
            elapsed = time.monotonic() - start
            self._log(f"  [polib-validate] lake build timed out after {elapsed:.1f}s")
            return False, [PolibError(0, 0, "lake build Polib timed out")]

        combined = _ANSI_RE.sub("", proc.stdout + "\n" + proc.stderr)
        errors = self._parse_errors(combined)
        return proc.returncode == 0 and not errors, errors

    def _parse_errors(self, output: str) -> list[PolibError]:
        """
        Extract hard `error:` lines that reference Polib.lean.
        Generic lake summary lines are ignored.
        """
        errors: list[PolibError] = []
        seen: set[tuple[int, int, str]] = set()

        for raw in output.splitlines():
            m = _POLIB_ERROR_RE.match(raw.strip())
            if not m:
                continue
            msg = m.group("msg").strip()
            if msg in ("build failed", "Lean exited with code 1"):
                continue
            ln, col = int(m.group("line")), int(m.group("col"))
            key = (ln, col, msg[:120])
            if key in seen:
                continue
            seen.add(key)
            errors.append(PolibError(ln, col, msg))

        return errors

    def _build_line_section_map(self, content: str) -> dict[int, str | None]:
        """
        Return a dict mapping every 1-indexed line number to its owning node
        ID, or `None` for lines in the preamble (before the first section).
        """
        owner_map: dict[int, str | None] = {}
        current_owner: str | None = None

        for i, line in enumerate(content.splitlines(), start=1):
            m = _SECTION_HEADER_LINE_RE.match(line.strip())
            if m:
                current_owner = m.group(1)
            owner_map[i] = current_owner

        return owner_map

    def _try_repair_section(
        self,
        content: str,
        node_id: str,
        errors: list[PolibError],
    ) -> str | None:
        """
        Attempt in-place repair of all build errors in `node_id`'s section.

        Processes errors from highest to lowest line number so that inserting
        an extra line for one fix does not shift the indices of earlier errors.

        Returns repaired content string on full success, None if any error
        could not be handled (caller should remove the section instead).
        """
        lines = content.splitlines(keepends=True)
        patched = list(lines)

        for err in sorted(errors, key=lambda e: e.line, reverse=True):
            ln = err.line  # 1-indexed
            if ln < 1 or ln > len(lines):
                return None
            fixed = self._repair_inline_sorry(lines[ln - 1])
            if fixed is not None:
                patched[ln - 1] = fixed
            else:
                return None  # no repair available → signal caller to remove

        return "".join(patched)

    def _repair_inline_sorry(self, line_text: str) -> str | None:
        """
        Fix `<indent>sorry <non-comment text>` → two-line replacement:

            <indent>-- <trailing text>
            <indent>sorry<original line ending>

        Returns the replacement string or None if the line does not match.
        """
        stripped = line_text.rstrip("\n")
        m = _INLINE_SORRY_RE.match(stripped)
        if not m:
            return None
        indent = m.group("indent")
        rest = m.group("rest").strip()
        ending = "\n" if line_text.endswith("\n") else ""
        return f"{indent}-- {rest}\n{indent}sorry{ending}"

    def _remove_section_by_id(self, content: str, node_id: str) -> str:
        """
        Remove the proved/partial section for `node_id` from `content`.
        Uses the same regex semantics as `PolibManager._remove_node_section`.
        """
        pattern = re.compile(
            r"\n-- === " + re.escape(node_id) + r" \((?:proved|partial)\) ===\n"
            r".*?"
            r"(?=\n-- === |\Z)",
            re.DOTALL,
        )
        return pattern.sub("", content)

    # ─────────────────────────────────────────────────────────────────────
    # Section parsing / reassembly
    # ─────────────────────────────────────────────────────────────────────

    def _parse_sections(self, content: str) -> tuple[str, list[_Section]]:
        """
        Split Polib.lean into (preamble, sections).

        The preamble is everything up to (not including) the `\n` that
        precedes the first `-- === NodeId (status) ===` header.

        Each section's `text` field contains the header line, the quality
        line, and the body — but NOT the leading `\n` separator.
        """
        matches = list(_SECTION_BOUNDARY_RE.finditer(content))
        if not matches:
            return content, []

        # Preamble: everything before the '\n' that starts the first section.
        preamble = content[: matches[0].start()]

        sections: list[_Section] = []
        for i, m in enumerate(matches):
            # Section text starts right after the leading '\n' separator.
            sec_start = m.start() + 1
            # Section text ends at the '\n' that starts the next section,
            # or at EOF.
            sec_end = matches[i + 1].start() if i + 1 < len(matches) else len(content)
            text = content[sec_start:sec_end]
            sections.append(_Section(m.group(2), m.group(3), text))

        return preamble, sections

    def _reassemble(self, preamble: str, sections: list[_Section]) -> str:
        """
        Reconstruct Polib.lean content from preamble + sections.

        Each section is preceded by a `\n` separator, matching the format
        that `PolibManager.save` produces.
        """
        parts = [preamble]
        for sec in sections:
            parts.append("\n")
            parts.append(sec.text)
        return "".join(parts)

    # ─────────────────────────────────────────────────────────────────────
    # Atomic file I/O
    # ─────────────────────────────────────────────────────────────────────

    def _atomic_write(self, content: str) -> None:
        """Write `content` to Polib.lean via a rename-into-place."""
        tmp = self._polib_lean.with_name(
            self._polib_lean.stem
            + f"_{uuid.uuid4().hex[:8]}"
            + self._polib_lean.suffix
            + ".tmp"
        )
        try:
            tmp.write_text(content, encoding="utf-8")
            os.replace(tmp, self._polib_lean)
        except Exception:
            try:
                tmp.unlink(missing_ok=True)
            except OSError:
                pass
            raise
