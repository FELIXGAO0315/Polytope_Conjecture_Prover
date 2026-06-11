from __future__ import annotations

import json
import os
import re
import threading
import uuid
from datetime import datetime, timezone
from pathlib import Path

from agent.exceptions import PolibSaveError
from agent.prover.tools.blueprint import BlueprintNode
from agent.prover.tools.latex_parser import ParsedTheorem
from agent.prover.tools.quality_checker import QualityReport
from agent.prover.tools.search import SavedEntry


# Catches indented and modifier-prefixed forms too (`  axiom`, `private axiom`,
# `noncomputable axiom`) — Lean accepts leading whitespace/modifiers on commands.
_AXIOM_RE = re.compile(
    r"^\s*(?:private\s+|protected\s+|noncomputable\s+|unsafe\s+|partial\s+)*axiom\s",
    re.MULTILINE,
)
# Matches `sorry` used as a tactic with trailing non-comment text on the same line.
# e.g. `  sorry [SORRY] ...` is invalid Lean — the annotation must be a `--` comment.
# Rules:
#   - Anchored to line start (^) to avoid matching `sorry` inside comments or strings.
#   - Uses [ \t]+ (not \s+) so it never crosses newlines — `sorry\n  ·` must NOT match.
#   - Excludes lines that start with `--` via the anchor (a comment line starts with
#     optional whitespace then `--`, so `^[ \t]*sorry` won't match it).
_INLINE_SORRY_RE = re.compile(r"^[ \t]*\bsorry\b[ \t]+[^-\n]", re.MULTILINE)

# Matches a sorry tactic line (not inside a comment).
_SORRY_TACTIC_RE = re.compile(r"^[ \t]*sorry\b", re.MULTILINE)
# Matches a structured [SORRY] class annotation.
_SORRY_CLASS_RE  = re.compile(r"--\s*\[SORRY\]\s*class\s*:", re.IGNORECASE)

VALID_SORRY_CLASSES = {
    "mathlib_gap",           # needed Mathlib lemma does not exist
    "structure_gap",         # requires new foundational lemma in Inventory.lean
    "missing_theorem",       # depends on another conjecture's lemma not yet in Polib
    "complex_combinatorics", # combinatorial argument beyond current proof attempt
    "missing_figure_definition",  # external figure/diagram reference
}


def _check_sorry_annotations(lean_code: str, node_id: str) -> None:
    """Raise PolibSaveError if any sorry tactic lacks a structured [SORRY] annotation.

    Every `sorry` in conjecture proofs MUST have:
      -- [SORRY] class: <one of VALID_SORRY_CLASSES>
      -- [SORRY] reason: <one sentence>
      -- [SORRY] suggested_next: <what is needed to close this>
      -- [SORRY] impact: blocks <downstream node>
    within 6 lines above the sorry line.
    """
    lines = lean_code.splitlines()
    for i, line in enumerate(lines):
        stripped = line.strip()
        if stripped.startswith("--"):
            continue
        if not re.match(r"^[ \t]*sorry\b", line):
            continue
        # Look back up to 6 lines for [SORRY] class annotation
        context_start = max(0, i - 6)
        context = "\n".join(lines[context_start:i])
        if not _SORRY_CLASS_RE.search(context):
            raise PolibSaveError(
                f"Node '{node_id}': unannotated sorry at line {i + 1}. "
                f"Every sorry MUST have structured annotations immediately above it:\n"
                f"  -- [SORRY] class: <{'|'.join(sorted(VALID_SORRY_CLASSES))}>\n"
                f"  -- [SORRY] reason: <one sentence explaining what is missing>\n"
                f"  -- [SORRY] suggested_next: <specific lemma / approach needed>\n"
                f"  -- [SORRY] impact: blocks <downstream node name>"
            )

# Known proposition field names that must NEVER appear inside SimplyCon3ConnectedMap.
# The structure is allowed only data fields: m, p_i, v, e, total_occ.
_BANNED_STRUCT_FIELDS = {
    "euler_formula", "handshake", "regularity",
    "kgon_occupation_bound", "quad_adj_constraint", "quad_occ_reduction",
    "p_range", "occupation_conservation", "occupation_bound", "equality_family",
    "quad_occ_cancellation", "IsMap",
}

def _check_no_prop_fields_in_struct(lean_code: str, node_id: str) -> None:
    """Raise PolibSaveError if lean_code redefines SimplyCon3ConnectedMap with proposition fields."""
    m = re.search(r"structure\s+SimplyCon3ConnectedMap\b(.*?)^end\s+SimplyCon3ConnectedMap",
                  lean_code, re.DOTALL | re.MULTILINE)
    if not m:
        return
    struct_body = m.group(1)
    for field in _BANNED_STRUCT_FIELDS:
        if re.search(rf"^\s+{re.escape(field)}\s*:", struct_body, re.MULTILINE):
            raise PolibSaveError(
                f"Node '{node_id}': proposition field '{field}' found inside "
                f"SimplyCon3ConnectedMap. Structure must contain ONLY data fields. "
                f"Move '{field}' to a standalone sorried lemma."
            )
_SECTION_MARKER = "-- === BEGIN PROVED CONTENT ===\n"

# Matches the start of any `private` declaration (lemma / def / theorem / abbrev)
_PRIVATE_DECL_RE = re.compile(
    r"^private\s+(?:lemma|def|theorem|abbrev)\s+(\w+)\b",
    re.MULTILINE,
)


def _iso_now() -> str:
    return datetime.now(timezone.utc).isoformat()


def _strip_duplicate_private_decls(body: str, existing_content: str) -> str:
    """Remove private declarations from *body* that are already defined in *existing_content*.

    Each private block runs from its `private ...` line up to (but not including)
    the next top-level declaration or end-of-string.  We drop the entire block to
    avoid duplicate-definition errors from Lean.
    """
    existing_names = set(_PRIVATE_DECL_RE.findall(existing_content))
    if not existing_names:
        return body

    # Split body into top-level blocks separated by blank lines before declarations.
    # Strategy: find each `private` declaration in body; if its name is already
    # known, remove the entire declaration block (up to the next blank-line +
    # top-level keyword boundary).
    _TOP_LEVEL_RE = re.compile(
        r"(?=^(?:private\s+)?(?:lemma|def|theorem|abbrev|structure|namespace|end|section|#)\b)",
        re.MULTILINE,
    )
    parts = _TOP_LEVEL_RE.split(body)
    kept = []
    for part in parts:
        m = _PRIVATE_DECL_RE.match(part.lstrip())
        if m and m.group(1) in existing_names:
            continue  # drop duplicate
        kept.append(part)
    return "".join(kept)


def _remove_node_section(content: str, node_id: str) -> str:
    """Remove any existing proved or partial section for node_id from Polib.lean content."""
    pattern = re.compile(
        r"\n-- === " + re.escape(node_id) + r" \((?:proved|partial)\) ===\n"
        r".*?"
        r"(?=\n-- === |\Z)",
        re.DOTALL,
    )
    return pattern.sub("", content)


def _atomic_write(path: Path, content: str) -> None:
    tmp = path.with_name(path.stem + f"_{uuid.uuid4().hex[:8]}" + path.suffix + ".tmp")
    try:
        tmp.write_text(content, encoding="utf-8")
        os.replace(tmp, path)
    except Exception:
        try:
            tmp.unlink(missing_ok=True)
        except OSError:
            pass
        raise


def _get_file_lock(registry: dict, meta: threading.Lock, path: Path) -> threading.Lock:
    """Return a shared lock for the given file path (one lock per resolved path)."""
    key = str(path.resolve())
    with meta:
        if key not in registry:
            registry[key] = threading.Lock()
        return registry[key]


class StoreManager:
    """Single JSON file owning all agent state: polib index, session, dep graph, cache."""

    _DEFAULTS: dict = {
        "polib_index": [],
        "session": {"session_id": "", "started_at": "", "nodes": {}},
        "dep_graph": {"nodes": {}, "edges": []},
        "goals": {},
        "blueprints": {},
    }

    _lock_registry: dict[str, threading.Lock] = {}
    _lock_registry_meta: threading.Lock = threading.Lock()

    def __init__(self, store_path: Path):
        self._path = Path(store_path)
        self._lock = _get_file_lock(
            StoreManager._lock_registry, StoreManager._lock_registry_meta, self._path
        )
        self._data = self._load()

    def _load(self) -> dict:
        if self._path.exists():
            try:
                return json.loads(self._path.read_text(encoding="utf-8"))
            except Exception:
                pass
        import copy
        return copy.deepcopy(self._DEFAULTS)

    def get(self, section: str):
        with self._lock:
            import copy
            return copy.deepcopy(self._data.get(section, self._DEFAULTS.get(section)))

    def update(self, section: str, value) -> None:
        with self._lock:
            self._data = self._load()
            self._data[section] = value
            _atomic_write(self._path, json.dumps(self._data, indent=2))

    def update_in(self, section: str, key: str, value) -> None:
        import copy
        with self._lock:
            self._data = self._load()
            if section not in self._data:
                self._data[section] = copy.deepcopy(self._DEFAULTS.get(section, {}))
            self._data[section][key] = value
            _atomic_write(self._path, json.dumps(self._data, indent=2))

    def update_nested(self, section: str, outer_key: str, inner_key: str, value) -> None:
        """Atomically set self._data[section][outer_key][inner_key] = value."""
        import copy
        with self._lock:
            self._data = self._load()
            if section not in self._data:
                self._data[section] = copy.deepcopy(self._DEFAULTS.get(section, {}))
            self._data[section].setdefault(outer_key, {})[inner_key] = value
            _atomic_write(self._path, json.dumps(self._data, indent=2))

    def delete_nested(self, section: str, outer_key: str, inner_key: str) -> None:
        """Atomically remove self._data[section][outer_key][inner_key]."""
        with self._lock:
            self._data = self._load()
            self._data.get(section, {}).get(outer_key, {}).pop(inner_key, None)
            _atomic_write(self._path, json.dumps(self._data, indent=2))


def _extract_sorry_summary(lean_code: str, node_id: str) -> list[str]:
    """Return formatted comment lines summarising every [SORRY] block in lean_code.

    Each sorry block looks like:
      -- [SORRY] class: X
      -- [SORRY] reason: Y
      -- [SORRY] suggested_next: Z
      -- [SORRY] impact: blocks W
      sorry
    Returns lines like:
      --   [SORRY #1] class: X | reason: Y | suggested_next: Z | impact: W
    ready to embed in a section header.
    """
    lines = lean_code.splitlines()
    summary: list[str] = []
    idx = 0
    sorry_n = 0
    while idx < len(lines):
        line = lines[idx]
        if not line.strip().startswith("--") and re.match(r"^[ \t]*sorry\b", line):
            # Collect [SORRY] annotation lines immediately preceding this sorry
            j = idx - 1
            anno_lines: list[str] = []
            while j >= 0 and re.match(r"^[ \t]*--\s*\[SORRY\]", lines[j]):
                anno_lines.insert(0, lines[j].strip())
                j -= 1
            sorry_n += 1
            fields: dict[str, str] = {}
            for al in anno_lines:
                m = re.match(r"--\s*\[SORRY\]\s*(\w+)\s*:\s*(.*)", al, re.IGNORECASE)
                if m:
                    fields[m.group(1).lower()] = m.group(2).strip()
            parts = []
            for key in ("class", "reason", "suggested_next", "impact"):
                if key in fields:
                    parts.append(f"{key}: {fields[key]}")
            summary.append(f"-- [SORRY #{sorry_n}] " + " | ".join(parts) if parts
                           else f"-- [SORRY #{sorry_n}] (unannotated — see line {idx + 1})")
        idx += 1
    if summary:
        summary = ["-- ── Sorry details (" + node_id + ") ──"] + summary
    return summary


class PolibManager:
    """Appends proved/partial Lean content to a single Polib.lean file."""

    _lock_registry: dict[str, threading.Lock] = {}
    _lock_registry_meta: threading.Lock = threading.Lock()

    def __init__(self, package_root: Path, polib_search=None, dep_graph_manager=None):
        self._root = Path(package_root)
        self._search = polib_search
        self._graph = dep_graph_manager
        self._polib_lean = self._root / "Polib.lean"
        self._lock = _get_file_lock(
            PolibManager._lock_registry, PolibManager._lock_registry_meta, self._polib_lean
        )

    def save(
        self,
        node: BlueprintNode,
        lean_code: str,
        report: QualityReport,
        category: str,
        parsed: ParsedTheorem,
    ) -> SavedEntry:
        if "import Mathlib" not in lean_code:
            raise PolibSaveError(
                f"Node '{node.node_id}': lean_code must contain 'import Mathlib'"
            )
        if _AXIOM_RE.search(lean_code):
            raise PolibSaveError(
                f"Node '{node.node_id}': axiom declarations are not allowed in polib"
            )
        # Inline-sorry check removed: _verify_polib_builds() and PolibValidator
        # (step 5) are the right place to catch build failures.  Pre-rejecting
        # compiled code here causes false-positive PolibSaveErrors for patterns
        # like `sorry [SORRY: reason]` that Lean 4 actually accepts.
        _check_no_prop_fields_in_struct(lean_code, node.node_id)

        # If sorry(s) present, every one must have a structured [SORRY] annotation.
        # Unannotated bare `sorry` is rejected so the agent is forced to retry.
        if report.sorry_count > 0:
            _check_sorry_annotations(lean_code, node.node_id)

        # Reject sorry-free nodes that failed the quality check: saving them as
        # "proved" would record a semantically wrong proof in Polib.
        # For intermediate nodes the quality checker already uses is_main_target=False
        # (only sorry-audit applies), so report.passed is reliable for both cases.
        if report.sorry_count == 0 and not report.passed:
            raise PolibSaveError(
                f"Node '{node.node_id}': quality check failed (score={report.score:.2f}, "
                f"passed={report.passed}) — refusing to save as proved"
            )

        status = "proved" if report.sorry_count == 0 else "partial"
        now = _iso_now()

        # Strip import lines, struct definitions, and any Polib section-metadata
        # headers that may be present when lean_code was loaded from Polib.lean.
        # Without this stripping, re-saving loaded code embeds the old section
        # header inside the new section body, creating duplicate headers.
        body = lean_code
        body = re.sub(r"^import\s+\S+\s*\n?", "", body, flags=re.MULTILINE)
        body = re.sub(r"^-- === \S+ \((?:proved|partial)\) ===[ \t]*\n?", "", body, flags=re.MULTILINE)
        body = re.sub(r"^-- quality_score:[ \t][^\n]*\n?", "", body, flags=re.MULTILINE)
        body = re.sub(
            r"structure SimplyCon3ConnectedMap.*?^end SimplyCon3ConnectedMap\n?",
            "",
            body,
            flags=re.DOTALL | re.MULTILINE,
        )
        body = re.sub(
            r"^namespace SimplyCon3ConnectedMap\b.*?^end SimplyCon3ConnectedMap\n?",
            "",
            body,
            flags=re.DOTALL | re.MULTILINE,
        )
        body = body.strip()

        # Build sorry summary lines for partial entries (inserted into section header).
        sorry_summary_lines: list[str] = []
        if status == "partial":
            sorry_summary_lines = _extract_sorry_summary(body, node.node_id)

        def _make_section(body_text: str) -> str:
            header = (
                f"\n-- === {node.node_id} ({status}) ===\n"
                f"-- quality_score: {report.score:.3f} | sorry_count: {report.sorry_count}"
                f" | saved_at: {now}\n"
            )
            if sorry_summary_lines:
                header += "\n".join(sorry_summary_lines) + "\n"
            return header + body_text + "\n"

        with self._lock:
            existing = self._polib_lean.read_text(encoding="utf-8") if self._polib_lean.exists() else ""
            existing = _remove_node_section(existing, node.node_id)
            body = _strip_duplicate_private_decls(body, existing)
            _atomic_write(self._polib_lean, existing + _make_section(body))

        mathlib_imports = re.findall(r"^import\s+(Mathlib\.\S+)", lean_code, re.MULTILINE)
        polib_imports = ["Polib"]

        entry = SavedEntry(
            node_id=node.node_id,
            theorem_name=node.node_id,
            category=category,
            lean_file_path="Polib.lean",
            status=status,
            sorry_count=report.sorry_count,
            quality_score=report.score,
            saved_at=now,
            latex_hash=parsed.latex_hash,
            mathlib_imports=mathlib_imports,
            polib_imports=polib_imports,
            description=node.description,
        )

        if self._search is not None:
            self._search.register(entry)

        if self._graph is not None:
            self._graph.record_node(entry, report, parsed)

        return entry

    def remove(self, node_id: str) -> None:
        """Remove the Polib.lean section for node_id (rollback after failed verification)."""
        with self._lock:
            if not self._polib_lean.exists():
                return
            existing = self._polib_lean.read_text(encoding="utf-8")
            cleaned = _remove_node_section(existing, node_id)
            if cleaned != existing:
                _atomic_write(self._polib_lean, cleaned)


class DepGraphManager:
    """Dependency graph backed by store.json."""

    def __init__(self, store: StoreManager):
        self._store = store

    @property
    def data(self) -> dict:
        return self._store.get("dep_graph")

    def record_node(
        self, entry: SavedEntry, report: QualityReport, parsed: ParsedTheorem
    ) -> None:
        dg = self._store.get("dep_graph")
        dg.setdefault("nodes", {})[entry.node_id] = {
            "id": entry.node_id,
            "theorem_name": entry.theorem_name,
            "node_type": "theorem",
            "status": entry.status,
            "category": entry.category,
            "lean_file": entry.lean_file_path,
            "quality_score": entry.quality_score,
            "sorry_count": entry.sorry_count,
            "latex_hash": entry.latex_hash,
            "saved_at": entry.saved_at,
        }
        self._store.update("dep_graph", dg)

    def record_edges(
        self, from_id: str, lean_code: str, parsed: ParsedTheorem
    ) -> None:
        rows: list[dict] = []

        for step in parsed.proof_steps:
            for ref in step.references:
                rows.append({
                    "from": from_id, "to": ref,
                    "edge_type": "cited", "origin": "latex",
                    "latex_line": step.latex_text[:80],
                })

        apply_pattern = re.compile(r"\b(?:apply|exact|have\s+\w+\s*:=)\s+([\w.]+)")
        for m in apply_pattern.finditer(lean_code):
            name = m.group(1)
            if name.startswith("Polib."):
                rows.append({"from": from_id, "to": name, "edge_type": "used", "origin": "lean"})
            elif name.startswith("Mathlib."):
                rows.append({"from": from_id, "to": name, "edge_type": "external", "origin": "lean"})

        sorry_block_re = re.compile(
            r"--\s*\[SORRY\].*?\n.*?--\s*\[SORRY\].*?\n.*?--\s*\[SORRY\]\s*impact:\s*blocks\s*(\S+)",
            re.MULTILINE,
        )
        for m in sorry_block_re.finditer(lean_code):
            rows.append({
                "from": from_id, "to": m.group(1),
                "edge_type": "missing", "origin": "lean",
            })

        if not rows:
            return
        dg = self._store.get("dep_graph")
        dg.setdefault("edges", []).extend(rows)
        self._store.update("dep_graph", dg)

    def save(self) -> None:
        pass  # store.json is always up to date


class SessionState:
    """Session progress backed by store.json."""

    def __init__(self, store: StoreManager):
        self._store = store
        self._ensure_init()

    def _ensure_init(self) -> None:
        session = self._store.get("session")
        if not session.get("session_id"):
            self._store.update("session", {
                "session_id": str(uuid.uuid4()),
                "started_at": _iso_now(),
                "nodes": {},
            })

    def _get(self) -> dict:
        return self._store.get("session")

    def is_done(self, node_id: str) -> bool:
        s = self._get()
        return s.get("nodes", {}).get(node_id, {}).get("status") == "proved"

    def is_partial(self, node_id: str) -> bool:
        s = self._get()
        return s.get("nodes", {}).get(node_id, {}).get("status") == "partial"

    # Infrastructure failures carry no information about the proof approach —
    # injecting them as "previous failed attempts — do NOT repeat" only adds
    # noise to the generation prompt.
    _INFRA_ERROR_MARKERS = (
        "claude CLI timed out",
        "unresolved deps:",
        "call aborted: stop_event",
    )

    def mark_pending(self, node_id: str, rounds_used: int, last_error: str, failed_code: str | None = None) -> None:
        # Accumulate cross-run failure records so retries can learn from prior attempts.
        # Only keep the most recent 3 — older attempts are stale baggage that misleads
        # the LLM (the failure mode has usually evolved past them).
        current = self._get().get("nodes", {}).get(node_id, {})
        errors = list(current.get("cross_run_errors", []))
        is_infra = any(m in last_error for m in self._INFRA_ERROR_MARKERS)
        if not is_infra:
            errors.append({
                "error": last_error[:400],
                "code_snippet": failed_code[:600] if failed_code else "",
            })
        errors = errors[-3:]
        self._store.update_nested("session", "nodes", node_id, {
            "status": "pending",
            "rounds_used": rounds_used,
            "last_error": last_error,
            "cross_run_errors": errors,
        })

    def get_cross_run_errors(self, node_id: str) -> list[dict]:
        """Return accumulated cross-run failure records for a node."""
        return self._get().get("nodes", {}).get(node_id, {}).get("cross_run_errors", [])

    def mark_partial(self, node_id: str, rounds_used: int, reason: str = "") -> None:
        """Mark a node as partial (compiled with sorrys). Distinct from pending
        so that is_partial() correctly detects it on the next retry."""
        self._store.update_nested("session", "nodes", node_id, {
            "status": "partial",
            "rounds_used": rounds_used,
            "reason": reason,
            "updated_at": _iso_now(),
        })

    def mark_done(self, node_id: str, status: str) -> None:
        self._store.update_nested("session", "nodes", node_id, {
            "status": status,
            "saved_at": _iso_now(),
        })

    def reset_node(self, node_id: str) -> None:
        self._store.delete_nested("session", "nodes", node_id)

    def save(self) -> None:
        pass  # store.json is always up to date

    @property
    def data(self) -> dict:
        return self._get()
