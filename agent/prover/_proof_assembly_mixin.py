"""Output file assembly (mixin for FormalizerAgent).

Single method ``_write_complete_proof_file`` that gathers every node\'s
saved Polib source into one ``output/{subdir}/{stem}.lean`` per run,
adds a generated-by header, and counts the actual sorry occurrences in the
assembled output (which may differ from the per-node sorry count after the
prover\'s post-save validator runs).

Relies on ``self._config`` (polib path / store path), ``self._proof_subdir``
(``"complete_proof"`` for FormalizerAgent, ``"conjecture_proof"`` for
ProverAgent), ``self._run_codes`` (per-run code collected during the node
loop), ``self._polib_store``, ``self._session``, and ``self._sorry_inc``.
"""
from __future__ import annotations

import re
from datetime import datetime, timezone
from pathlib import Path

from agent.prover import lean_codegen


class ProofAssemblyMixin:
    def _write_complete_proof_file(
        self,
        tex_path: str,
        theorem_name: str,
        nodes_proved: list[str],
        nodes_partial: list[str],
        nodes_failed: list[str],
        total_sorry_count: int,
    ) -> tuple[Path, list[str], int]:
        """Write output/complete_proof/{stem}.lean with the full formalization for this run.

        Returns (out_path, code_missing, actual_sorry_count) where:
        - code_missing: proved/partial node IDs whose Lean code could not be located
        - actual_sorry_count: number of real sorry occurrences in the assembled output
        """
        import re as _re
        from datetime import datetime, timezone

        _SECTION_RE = _re.compile(r"^-- === (.+?) \((proved|partial|failed)\) ===$")

        out_dir = self._output_root / self._proof_subdir
        out_dir.mkdir(parents=True, exist_ok=True)
        out_path = out_dir / f"{Path(tex_path).stem}.lean"

        # ── Parse Polib.lean header + sections ─────────────────────────
        polib_lean = Path(self._config.polib_path) / "Polib.lean"
        header_lines: list[str] = []
        polib_sections: dict[str, list[str]] = {}

        if polib_lean.exists():
            current_node: str | None = None
            current_section: list[str] = []
            in_header = True
            for line in self._polib_store.read().splitlines():
                if in_header:
                    if line.startswith("-- === BEGIN PROVED CONTENT ==="):
                        in_header = False
                    else:
                        header_lines.append(line)
                    continue
                m = _SECTION_RE.match(line)
                if m:
                    if current_node is not None:
                        polib_sections[current_node] = current_section
                    current_node = m.group(1)
                    current_section = [line]
                elif current_node is not None:
                    current_section.append(line)
            if current_node is not None:
                polib_sections[current_node] = current_section

        # ── Build output ────────────────────────────────────────────────
        ts = datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")
        lines: list[str] = [
            f"-- Complete formalization: {Path(tex_path).stem}.tex",
            f"-- Theorem: {theorem_name}",
            f"-- Generated: {ts}",
            f"-- Proved — 0 new sorry ({len(nodes_proved)}): {', '.join(nodes_proved) or 'none'}",
        ]
        if nodes_partial:
            lines.append(f"-- Partial — has new sorry ({len(nodes_partial)}): {', '.join(nodes_partial)}")
        if nodes_failed:
            lines.append(f"-- Failed ({len(nodes_failed)}): {', '.join(nodes_failed)}")
        lines += [f"-- New sorry count: {total_sorry_count}", ""]

        # ── Sorry report (only new sorries — Inventory.lean sorries are pre-approved) ──
        if total_sorry_count > 0:
            lines += [
                "-- ════════════════════════════════════════════════════════════════════",
                f"-- SORRY REPORT  ({total_sorry_count} new sorry(s) from Partial nodes — each must be justified below)",
                "-- Inventory.lean sorries are foundational axioms and are NOT counted here.",
                "-- ════════════════════════════════════════════════════════════════════",
            ]
            # Collect sorry details from run_codes (partial nodes)
            _sorry_re = re.compile(r"\bsorry\b")
            _anno_re  = re.compile(r"^[ \t]*--\s*\[SORRY\]\s*(\w+)\s*:\s*(.*)", re.MULTILINE)
            for nid in nodes_partial:
                node_code = self._run_codes.get(nid, "")
                if not node_code or not lean_codegen.has_sorry(node_code):
                    continue
                lines.append(f"--")
                lines.append(f"-- Node: {nid}")
                # Extract every [SORRY] annotation block
                node_lines = node_code.splitlines()
                sorry_n = 0
                for i, ln in enumerate(node_lines):
                    if ln.strip().startswith("--"):
                        continue
                    if not _sorry_re.search(ln):
                        continue
                    sorry_n += 1
                    j = i - 1
                    anno: dict[str, str] = {}
                    while j >= 0 and re.match(r"^[ \t]*--\s*\[SORRY\]", node_lines[j]):
                        m = re.match(r"^[ \t]*--\s*\[SORRY\]\s*(\w+)\s*:\s*(.*)",
                                     node_lines[j])
                        if m:
                            anno[m.group(1).lower()] = m.group(2).strip()
                        j -= 1
                    cls    = anno.get("class",          "unclassified")
                    reason = anno.get("reason",         "(no reason given)")
                    nxt    = anno.get("suggested_next", "(none)")
                    impact = anno.get("impact",         "(unknown)")
                    lines += [
                        f"--   Sorry #{sorry_n}:",
                        f"--     class          : {cls}",
                        f"--     reason         : {reason}",
                        f"--     suggested_next : {nxt}",
                        f"--     impact         : {impact}",
                    ]
            lines += [
                "-- ════════════════════════════════════════════════════════════════════",
                "",
            ]

        lines += header_lines
        lines.append("")

        _STRIP = {"import ", "-- Output/", "-- generated_at:", "-- compile:"}

        def _strip_boilerplate(code: str) -> list[str]:
            return [ln for ln in code.splitlines()
                    if not any(ln.startswith(p) for p in _STRIP)]

        def _has_section_header(code_lines: list[str]) -> bool:
            return any(ln.startswith("-- === ") for ln in code_lines[:5])

        output_root = self._output_root / "Output"
        run_codes = dict(self._run_codes)  # snapshot

        # Build a fallback map: normalised name → polib section name (for fuzzy skip-node lookup)
        def _norm(s: str) -> str:
            return s.lower().replace("_", "").replace(" ", "")

        def _fuzzy_find(node_id: str) -> str | None:
            """Return best-matching polib section name using substring then similarity."""
            import difflib
            nid = _norm(node_id)
            # Exact normalised match
            for sec in polib_sections:
                if _norm(sec) == nid:
                    return sec
            # node_id is a substring of section name (e.g. P6GenusG ⊂ ThmP6GenusG)
            for sec in polib_sections:
                if nid in _norm(sec):
                    return sec
            # section name is a substring of node_id (e.g. KGonMaxOccupy ⊂ KGonMaxOccupancy)
            for sec in polib_sections:
                if _norm(sec) in nid and len(_norm(sec)) > 5:
                    return sec
            # Best difflib similarity (threshold lowered from 0.75 to 0.62)
            best_sec, best_score = None, 0.0
            for sec in polib_sections:
                score = difflib.SequenceMatcher(None, nid, _norm(sec)).ratio()
                if score > best_score:
                    best_score, best_sec = score, sec
            if best_score >= 0.62:
                return best_sec
            return None

        # Extract top-level declared names from a block of code lines
        _decl_re = _re.compile(
            r'^(?:private\s+|protected\s+|noncomputable\s+)*'
            r'(?:lemma|theorem|def|abbrev)\s+(\w+)',
        )

        def _decl_names(code_lines: list[str]) -> list[str]:
            names = []
            for ln in code_lines:
                m = _decl_re.match(ln)
                if m:
                    names.append(m.group(1))
            return names

        # Build map: polib section_name → declared Lean identifier names (for dep resolution)
        _section_decl_names: dict[str, list[str]] = {
            sec: _decl_names(sec_lines)
            for sec, sec_lines in polib_sections.items()
        }
        # Reverse map: Lean identifier → section name
        _lean_id_to_section: dict[str, str] = {}
        for sec, names in _section_decl_names.items():
            for n in names:
                if n not in _lean_id_to_section:
                    _lean_id_to_section[n] = sec

        code_missing: list[str] = []
        # Track already-output Lean declaration names to deduplicate
        output_decl_names: set[str] = set()
        # Track already-included polib sections (by section name) for dep resolution
        included_sections: set[str] = set()

        def _include_section(sec_name: str, sec_lines: list[str]) -> None:
            """Emit a polib section, deduplicating by declared Lean name."""
            # _strip_boilerplate returns a list[str]
            code_block: list[str] = _strip_boilerplate("\n".join(sec_lines[1:]))  # skip header line
            for ln in code_block:
                m = _decl_re.match(ln)
                if m and m.group(1) in output_decl_names:
                    return  # entire block is a duplicate — skip it
            # Mark self BEFORE pulling deps to prevent self-referential loops
            # (the section's own lemma name appears in the declaration line and would
            # otherwise trigger a recursive _include_section for itself)
            included_sections.add(sec_name)
            _pull_transitive_deps(code_block)
            # Re-check dedup: a recursive dep pull may have emitted this section already
            for ln in code_block:
                m = _decl_re.match(ln)
                if m and m.group(1) in output_decl_names:
                    return
            for ln in code_block:
                m = _decl_re.match(ln)
                if m:
                    output_decl_names.add(m.group(1))
            lines.extend(code_block)

        def _pull_transitive_deps(code_lines_in: list[str], local_decls: set[str] | None = None) -> None:
            """For any Lean identifier in code_lines_in that maps to a polib section
            not yet included, emit that section first (recursively).

            local_decls: names declared IN code_lines_in itself (skip self-references).
            If None, it is computed automatically from code_lines_in.
            """
            if local_decls is None:
                local_decls = {m.group(1) for ln in code_lines_in
                               for m in [_decl_re.match(ln)] if m}
            ident_re = _re.compile(r'\b([A-Z][A-Za-z0-9_]+)\b')
            for ln in code_lines_in:
                stripped = ln.strip()
                if stripped.startswith("--") or stripped.startswith("/-"):
                    continue
                for m in ident_re.finditer(ln):
                    ident = m.group(1)
                    if ident in local_decls:
                        continue  # skip self-references
                    if ident in _lean_id_to_section:
                        dep_sec = _lean_id_to_section[ident]
                        if dep_sec not in included_sections and dep_sec in polib_sections:
                            included_sections.add(dep_sec)  # mark first to break cycles
                            lines.append(f"-- === {dep_sec} (proved) === [auto-dep]")
                            _include_section(dep_sec, polib_sections[dep_sec])
                            lines.append("")

        for node_id in nodes_proved + nodes_partial:
            status = "proved" if node_id in nodes_proved else "partial"
            _p2_emitted = False  # set True when P1/P2/P3 successfully emits a declaration

            # Priority 1: live code collected this run
            if node_id in run_codes and run_codes[node_id]:
                code_lines = _strip_boilerplate(run_codes[node_id])
                # Deduplicate: skip if the first declaration was already output
                skip_block = False
                for ln in code_lines:
                    m = _decl_re.match(ln)
                    if m:
                        if m.group(1) in output_decl_names:
                            skip_block = True
                        break  # only inspect first declaration
                if not skip_block:
                    if not _has_section_header(code_lines):
                        lines.append(f"-- === {node_id} ({status}) ===")
                    _pull_transitive_deps(code_lines)
                    # Re-check: a transitive dep pull may have emitted this block already
                    already_emitted = any(
                        _decl_re.match(ln) and _decl_re.match(ln).group(1) in output_decl_names
                        for ln in code_lines if _decl_re.match(ln)
                    )
                    if not already_emitted:
                        for ln in code_lines:
                            m = _decl_re.match(ln)
                            if m:
                                output_decl_names.add(m.group(1))
                        lines += code_lines
                        _p2_emitted = True
                elif skip_block:
                    _p2_emitted = True  # already emitted under a different name — not missing

            # Priority 2: exact match in Polib.lean sections
            elif node_id in polib_sections:
                decls_before = len(output_decl_names)
                if node_id not in included_sections:
                    lines.append(f"-- === {node_id} ({status}) ===")
                    _include_section(node_id, polib_sections[node_id])
                _p2_emitted = len(output_decl_names) > decls_before

            # Priority 3: fuzzy match in Polib.lean (handles P6GenusG ↔ ThmP6GenusG etc.)
            elif (matched := _fuzzy_find(node_id)) is not None:
                decls_before = len(output_decl_names)
                if matched not in included_sections:
                    lines.append(f"-- === {node_id} ({status}) === [matched as {matched}]")
                    _include_section(matched, polib_sections[matched])
                _p2_emitted = len(output_decl_names) > decls_before

            else:
                _p2_emitted = False

            # Priority 4: output/Output/ fallback — also runs when P2/P3 emitted nothing
            if not _p2_emitted and node_id not in code_missing:
                fallback = output_root / f"{node_id}.lean"
                if fallback.exists():
                    fb_text = fallback.read_text(encoding="utf-8")
                    # Reject fallback files that contain sorry for proved nodes — they are
                    # stale partial attempts and would silently corrupt the output.
                    _fb_sorry_re = _re.compile(r'\bsorry\b')
                    fb_has_sorry = any(
                        _fb_sorry_re.search(ln)
                        for ln in fb_text.splitlines()
                        if not ln.strip().startswith("--")
                    )
                    if fb_has_sorry and status == "proved":
                        self._log(verbose, f"  [warn] {node_id} Output file has sorry — treating as missing")
                        code_missing.append(node_id)
                    else:
                        fb_lines = _strip_boilerplate(fb_text)
                        skip_block = False
                        for ln in fb_lines:
                            m = _decl_re.match(ln)
                            if m:
                                if m.group(1) in output_decl_names:
                                    skip_block = True
                                break  # only inspect first declaration
                        if not skip_block:
                            lines.append(f"-- === {node_id} ({status}) ===")
                            _pull_transitive_deps(fb_lines)
                            already_emitted = any(
                                _decl_re.match(ln) and _decl_re.match(ln).group(1) in output_decl_names
                                for ln in fb_lines if _decl_re.match(ln)
                            )
                            if not already_emitted:
                                for ln in fb_lines:
                                    m = _decl_re.match(ln)
                                    if m:
                                        output_decl_names.add(m.group(1))
                                lines += fb_lines
                else:
                    # No code found anywhere — record as missing (real failure)
                    code_missing.append(node_id)

            if node_id not in code_missing:
                lines.append("")

        out_path.write_text("\n".join(lines), encoding="utf-8")

        # Count actual sorrys in the assembled output (non-comment lines only)
        _sorry_re = _re.compile(r'\bsorry\b')
        actual_sorry_count = sum(
            1 for ln in lines
            if not ln.strip().startswith("--") and _sorry_re.search(ln)
        )

        return out_path, code_missing, actual_sorry_count
