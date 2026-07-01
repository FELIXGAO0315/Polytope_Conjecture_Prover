"""Output file assembly (mixin for FormalizerAgent).

Single method ``_write_complete_proof_file`` gathers every proved node's
Lean source into one ``output/{subdir}/{stem}.lean`` per run.  Under the
no-new-sorry policy there is no ``partial`` status; every emitted section
is either fully proved or comes from a dependency the prover-agent pulled
in transitively.

Relies on ``self._config``, ``self._proof_subdir`` (``"complete_proof"``
for FormalizerAgent, ``"conjecture_proof"`` for ProverAgent),
``self._run_codes`` (per-run code collected by the node loop), and
``self._polib_store``.
"""
from __future__ import annotations

import difflib
import re
from datetime import datetime, timezone
from pathlib import Path


_SECTION_RE = re.compile(r"^-- === (.+?) \((proved|partial|failed)\) ===$")
_DECL_RE = re.compile(
    r'^(?:private\s+|protected\s+|noncomputable\s+)*'
    r'(?:lemma|theorem|def|abbrev)\s+(\w+)',
)
_IDENT_RE = re.compile(r'\b([A-Z][A-Za-z0-9_]+)\b')

_STRIP_PREFIXES = ("import ", "-- Output/", "-- generated_at:", "-- compile:")


def _strip_boilerplate(code: str) -> list[str]:
    return [
        ln for ln in code.splitlines()
        if not any(ln.startswith(p) for p in _STRIP_PREFIXES)
    ]


def _has_section_header(code_lines: list[str]) -> bool:
    return any(ln.startswith("-- === ") for ln in code_lines[:5])


def _decl_names(code_lines: list[str]) -> list[str]:
    out: list[str] = []
    for ln in code_lines:
        m = _DECL_RE.match(ln)
        if m:
            out.append(m.group(1))
    return out


def _norm(s: str) -> str:
    return s.lower().replace("_", "").replace(" ", "")


class ProofAssemblyMixin:
    def _write_complete_proof_file(
        self,
        output_stem: str,
        theorem_name: str,
        nodes_proved: list[str],
        nodes_failed: list[str],
    ) -> tuple[Path, list[str], int]:
        """Write ``output/{proof_subdir}/{output_stem}.lean`` for this run.

        Returns ``(out_path, code_missing, actual_sorry_count)`` where:

        * ``code_missing`` — proved node IDs whose Lean code could not be
          located (real assembly failure; should be empty on a clean run).
        * ``actual_sorry_count`` — sorry occurrences in the assembled
          output (always 0 on a clean run; non-zero means a stale section
          slipped in from Polib and the user should investigate).
        """
        out_dir = self._output_root / self._proof_subdir
        out_dir.mkdir(parents=True, exist_ok=True)
        out_path = out_dir / f"{output_stem}.lean"

        polib_lean = Path(self._config.polib_path) / "Polib.lean"
        header_lines, polib_sections = self._parse_polib(polib_lean)

        ts = datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")
        lines: list[str] = [
            f"-- Complete formalization: {output_stem}",
            f"-- Theorem: {theorem_name}",
            f"-- Generated: {ts}",
            f"-- Proved ({len(nodes_proved)}): {', '.join(nodes_proved) or 'none'}",
        ]
        if nodes_failed:
            lines.append(f"-- Failed ({len(nodes_failed)}): {', '.join(nodes_failed)}")
        lines += ["", *header_lines, ""]

        # ── Section reuse / dedup state ────────────────────────────────
        run_codes = dict(self._run_codes)                # snapshot
        output_root = self._output_root / "Output"
        code_missing: list[str] = []
        output_decl_names: set[str] = set()
        included_sections: set[str] = set()

        # name lookup: Lean identifier → Polib section name (for transitive deps)
        lean_id_to_section: dict[str, str] = {}
        for sec, sec_lines in polib_sections.items():
            for name in _decl_names(sec_lines):
                lean_id_to_section.setdefault(name, sec)

        def _fuzzy_find(node_id: str) -> str | None:
            """Match a node_id against a Polib section name by substring / similarity."""
            nid = _norm(node_id)
            for sec in polib_sections:
                if _norm(sec) == nid:
                    return sec
            for sec in polib_sections:
                if nid in _norm(sec):
                    return sec
            for sec in polib_sections:
                if _norm(sec) in nid and len(_norm(sec)) > 5:
                    return sec
            best_sec, best_score = None, 0.0
            for sec in polib_sections:
                score = difflib.SequenceMatcher(None, nid, _norm(sec)).ratio()
                if score > best_score:
                    best_score, best_sec = score, sec
            return best_sec if best_score >= 0.62 else None

        def _pull_transitive_deps(code_lines_in: list[str]) -> None:
            """Emit any not-yet-included Polib sections that *code_lines_in* references."""
            local_decls = {m.group(1) for ln in code_lines_in
                           for m in [_DECL_RE.match(ln)] if m}
            for ln in code_lines_in:
                stripped = ln.strip()
                if stripped.startswith("--") or stripped.startswith("/-"):
                    continue
                for m in _IDENT_RE.finditer(ln):
                    ident = m.group(1)
                    if ident in local_decls:
                        continue
                    dep_sec = lean_id_to_section.get(ident)
                    if dep_sec and dep_sec not in included_sections and dep_sec in polib_sections:
                        included_sections.add(dep_sec)  # mark first to break cycles
                        lines.append(f"-- === {dep_sec} (proved) === [auto-dep]")
                        _include_section(dep_sec, polib_sections[dep_sec])
                        lines.append("")

        def _include_section(sec_name: str, sec_lines: list[str]) -> None:
            """Emit a polib section, deduplicating by declared Lean name."""
            code_block = _strip_boilerplate("\n".join(sec_lines[1:]))  # skip header
            for ln in code_block:
                m = _DECL_RE.match(ln)
                if m and m.group(1) in output_decl_names:
                    return  # whole block is a duplicate
            included_sections.add(sec_name)
            _pull_transitive_deps(code_block)
            # Re-check dedup after recursive deps
            for ln in code_block:
                m = _DECL_RE.match(ln)
                if m and m.group(1) in output_decl_names:
                    return
            for ln in code_block:
                m = _DECL_RE.match(ln)
                if m:
                    output_decl_names.add(m.group(1))
            lines.extend(code_block)

        # ── Emit each proved node's code (P1 live → P2 polib exact → P3 fuzzy → P4 fallback file)
        for node_id in nodes_proved:
            emitted = self._emit_node_code(
                node_id, run_codes, polib_sections,
                _fuzzy_find, _include_section, _pull_transitive_deps,
                lines, output_decl_names, included_sections,
                output_root, code_missing,
            )
            if emitted and node_id not in code_missing:
                lines.append("")

        out_path.write_text("\n".join(lines), encoding="utf-8")

        actual_sorry_count = sum(
            1 for ln in lines
            if not ln.strip().startswith("--") and re.search(r"\bsorry\b", ln)
        )
        return out_path, code_missing, actual_sorry_count

    # ------------------------------------------------------------------
    # Helpers
    # ------------------------------------------------------------------

    def _parse_polib(
        self, polib_lean: Path,
    ) -> tuple[list[str], dict[str, list[str]]]:
        """Return (header_lines, section_map) where section_map[node_id] is the
        section's raw line list (including its ``-- === ... ===`` header).
        """
        header: list[str] = []
        sections: dict[str, list[str]] = {}
        if not polib_lean.exists():
            return header, sections
        current_node: str | None = None
        current_section: list[str] = []
        in_header = True
        for line in self._polib_store.read().splitlines():
            if in_header:
                if line.startswith("-- === BEGIN PROVED CONTENT ==="):
                    in_header = False
                else:
                    header.append(line)
                continue
            m = _SECTION_RE.match(line)
            if m:
                if current_node is not None:
                    sections[current_node] = current_section
                current_node = m.group(1)
                current_section = [line]
            elif current_node is not None:
                current_section.append(line)
        if current_node is not None:
            sections[current_node] = current_section
        return header, sections

    def _emit_node_code(
        self,
        node_id: str,
        run_codes: dict[str, str],
        polib_sections: dict[str, list[str]],
        fuzzy_find,
        include_section,
        pull_transitive_deps,
        lines: list[str],
        output_decl_names: set[str],
        included_sections: set[str],
        output_root: Path,
        code_missing: list[str],
    ) -> bool:
        """Try the 4 source priorities; return True iff a section was emitted."""
        # P1: live code collected this run
        if node_id in run_codes and run_codes[node_id]:
            code_lines = _strip_boilerplate(run_codes[node_id])
            first_decl = next((_DECL_RE.match(ln) for ln in code_lines if _DECL_RE.match(ln)), None)
            if first_decl and first_decl.group(1) in output_decl_names:
                return True       # already emitted under another name
            if not _has_section_header(code_lines):
                lines.append(f"-- === {node_id} (proved) ===")
            pull_transitive_deps(code_lines)
            already = any(
                _DECL_RE.match(ln) and _DECL_RE.match(ln).group(1) in output_decl_names
                for ln in code_lines if _DECL_RE.match(ln)
            )
            if not already:
                for ln in code_lines:
                    m = _DECL_RE.match(ln)
                    if m:
                        output_decl_names.add(m.group(1))
                lines += code_lines
            return True

        # P2: exact match in Polib.lean
        if node_id in polib_sections:
            if node_id not in included_sections:
                decls_before = len(output_decl_names)
                lines.append(f"-- === {node_id} (proved) ===")
                include_section(node_id, polib_sections[node_id])
                return len(output_decl_names) > decls_before
            return True

        # P3: fuzzy match in Polib.lean
        matched = fuzzy_find(node_id)
        if matched is not None:
            if matched not in included_sections:
                decls_before = len(output_decl_names)
                lines.append(f"-- === {node_id} (proved) === [matched as {matched}]")
                include_section(matched, polib_sections[matched])
                return len(output_decl_names) > decls_before
            return True

        # P4: output/Output/{node_id}.lean fallback
        fallback = output_root / f"{node_id}.lean"
        if not fallback.exists():
            code_missing.append(node_id)
            return False
        fb_text = fallback.read_text(encoding="utf-8")
        if any(re.search(r"\bsorry\b", ln) for ln in fb_text.splitlines()
               if not ln.strip().startswith("--")):
            # Sorry-tainted fallback for a proved node → treat as missing.
            code_missing.append(node_id)
            return False
        fb_lines = _strip_boilerplate(fb_text)
        first_decl = next((_DECL_RE.match(ln) for ln in fb_lines if _DECL_RE.match(ln)), None)
        if first_decl and first_decl.group(1) in output_decl_names:
            return True
        lines.append(f"-- === {node_id} (proved) ===")
        pull_transitive_deps(fb_lines)
        already = any(
            _DECL_RE.match(ln) and _DECL_RE.match(ln).group(1) in output_decl_names
            for ln in fb_lines if _DECL_RE.match(ln)
        )
        if not already:
            for ln in fb_lines:
                m = _DECL_RE.match(ln)
                if m:
                    output_decl_names.add(m.group(1))
            lines += fb_lines
        return True
