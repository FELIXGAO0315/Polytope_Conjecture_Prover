from __future__ import annotations

import hashlib
import json
import re
import threading
from concurrent.futures import ThreadPoolExecutor, as_completed
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path

from agent.claude_sdk import ClaudeSDKClient
from agent.config import Config
from agent.exceptions import (
    BlueprintError,
    GoalTamperedError,
    PolibSaveError,
)
from agent.prover.prompts.lean_generation import (
    FIX_LOOP_POLIB_REF,
    LEAN_GENERATION_PROMPT,
    LEAN_GENERATION_SYSTEM_PROMPT,
    LEAN_PREAMBLE,
    SHARED_MODULE_CONTENT,
    _GOAL_CONTEXT_INTERMEDIATE,
    _GOAL_CONTEXT_MAIN,
    _GOAL_INSTR_INTERMEDIATE,
    _GOAL_INSTR_MAIN,
)
from agent.prover.tools.blueprint import Blueprint, BlueprintDecomposer, BlueprintNode
from agent.prover.tools.formalization_logger import FormalizationLogger
from agent.prover.tools.goal_lock import GoalExtractor, GoalLock, GoalValidator, LockedGoal
from agent.prover.tools.latex_parser import LatexParser, ParsedTheorem
from agent.prover.tools.lean_compiler import LeanCompiler
from agent.prover.tools.polib_manager import DepGraphManager, PolibManager, SessionState, StoreManager
from agent.prover.tools.quality_checker import QualityChecker, QualityReport
from agent.prover.tools.search import CombinedHintGenerator, GitHubLean4Search, MathlibSearch, PolibSearch
from agent.prover.tools.prompt_optimizer import extract_signature, filter_dep_imports_to_direct
from agent.prover.tools.output_search import OutputSearch
from agent.prover.tools.llm_hint_generator import LLMHintGenerator, FailureRecord


_LAST_DECL_RE = re.compile(
    r"^(?:private\s+)?(?:lemma|theorem|def|abbrev)\s+(\w+)",
    re.MULTILINE,
)


def _rename_last_decl(code: str, expected_name: str) -> str:
    """If the last top-level declaration in *code* is not named *expected_name*, rename it.

    Only the declaration identifier itself is renamed; any docstring, helper lemmas,
    or references inside the proof body are left untouched (renaming references would
    require full parsing and is out of scope — the declaration name is what Lean exports).
    """
    matches = list(_LAST_DECL_RE.finditer(code))
    if not matches:
        return code
    last = matches[-1]
    actual_name = last.group(1)
    if actual_name == expected_name:
        return code
    # Replace only the identifier in the last declaration header.
    start, end = last.span(1)
    new_code = code[:start] + expected_name + code[end:]
    # Ensure the declaration is private to avoid polluting the global namespace
    # and to prevent duplicate non-private declarations across generated files.
    full_span_start, full_span_end = last.span(0)
    full_decl = code[full_span_start:full_span_end]
    if not full_decl.strip().startswith("private"):
        # Insert 'private ' at the start of the declaration
        insert_pos = full_span_start
        new_code = new_code[:insert_pos] + "private " + new_code[insert_pos:]
    return new_code


@dataclass
class FormalizationResult:
    theorem_name: str
    status: str  # "success" | "partial" | "failed"
    nodes_proved: list[str]
    nodes_partial: list[str]
    nodes_failed: list[str]
    total_sorry_count: int
    error: str | None
    dep_graph_path: str
    session_state_path: str

    @property
    def success(self) -> bool:
        return self.status == "success"

    def to_dict(self) -> dict:
        return {
            "theorem_name": self.theorem_name,
            "status": self.status,
            "nodes_proved": self.nodes_proved,
            "nodes_partial": self.nodes_partial,
            "nodes_failed": self.nodes_failed,
            "total_sorry_count": self.total_sorry_count,
            "error": self.error,
            "dep_graph_path": self.dep_graph_path,
            "session_state_path": self.session_state_path,
        }


class StagnationDetector:
    """Tracks per-round error hashes to detect when the compile-fix loop is stuck.

    Uses hash-based counting (Fix 4) instead of string comparison so that errors
    with different line numbers or different hallucinated identifier names but the
    same underlying class are treated as identical stagnation.
    """

    THRESHOLD = 3

    def __init__(self) -> None:
        self.error_counts: dict[str, int] = {}
        self.tried_strategies: set[str] = set()

    def record(self, error_hash: str) -> bool:
        """Record one occurrence of error_hash. Returns True when threshold is hit."""
        self.error_counts[error_hash] = self.error_counts.get(error_hash, 0) + 1
        return self.error_counts[error_hash] >= self.THRESHOLD

    def mark_strategy(self, strategy: str) -> None:
        self.tried_strategies.add(strategy)

    def has_tried(self, strategy: str) -> bool:
        return strategy in self.tried_strategies

    def reset(self) -> None:
        self.error_counts.clear()


class FormalizerAgent:
    _proof_subdir: str = "complete_proof"  # overrideable by subclasses

    # Class-level Polib locks: one lock per Polib.lean path, shared across all instances.
    # Guards the entire save→verify→remove sequence atomically so no two threads can
    # interleave their Polib writes (which would cause false TOCTOU "broken" detections).
    _polib_locks: dict[str, threading.Lock] = {}
    _polib_locks_meta: threading.Lock = threading.Lock()

    # Class-level in-memory cache for Polib.lean content.
    # Shared across all agent instances for the same path so parallel workers benefit.
    # Invalidated inside _polib_lock after every write, so readers always get fresh data.
    _polib_content_cache: dict[str, str] = {}
    _polib_content_cache_lock: threading.Lock = threading.Lock()

    @classmethod
    def _get_polib_content(cls, polib_lean: "Path") -> str:
        """Return Polib.lean content from the in-memory cache, reading disk only on miss."""
        key = str(polib_lean.resolve())
        with cls._polib_content_cache_lock:
            cached = cls._polib_content_cache.get(key)
            if cached is not None:
                return cached
            if not polib_lean.exists():
                return ""  # don't cache missing file — it may be created shortly
            content = polib_lean.read_text(encoding="utf-8")
            cls._polib_content_cache[key] = content
            return content

    def _format_dep_signatures_block(self, dep_ids: list[str]) -> str:
        """Return a prompt block with exact signatures of proved deps, so fix-loop
        LLM cannot hallucinate argument counts. Empty string if none found.
        """
        lines: list[str] = []
        for dep_id in dep_ids:
            entry = self._polib_search.find_by_node_id(dep_id)
            if entry is None:
                continue
            lean_name = entry.theorem_name or dep_id
            sig = self._extract_polib_signature(lean_name)
            if not sig:
                continue
            lines.append(f"### `{lean_name}` — call with EXACTLY these arguments:")
            lines.append("```lean")
            lines.append(sig)
            lines.append("```")
        if not lines:
            return ""
        return "## Proved-dependency signatures (DO NOT pass extra arguments)\n" + "\n".join(lines) + "\n\n"

    def _extract_polib_signature(self, lean_name: str) -> str:
        """Extract the type signature (declaration up to `:= by`) for a proved dep
        from Polib.lean. Returns "" if not found.

        Looks for `theorem|lemma|def <lean_name>` at start of a line, then captures
        until `:= by` or `:= sorry`. The LLM uses this to know the exact call API
        (param count, hypothesis names, types) instead of guessing.
        """
        try:
            content = self._get_polib_content(self._polib_lean_path)
        except Exception:
            return ""
        if not content:
            return ""
        # Match the declaration line: `<kw> <lean_name>` possibly with whitespace
        decl_re = re.compile(
            rf"^(theorem|lemma|def|noncomputable\s+def)\s+{re.escape(lean_name)}\b",
            re.MULTILINE,
        )
        m = decl_re.search(content)
        if not m:
            return ""
        start = m.start()
        tail = content[start:]
        # Scope the search to this declaration only — otherwise a term-mode proof
        # (`:= ⟨…⟩` on the same line) would let the end-of-signature search run
        # into the NEXT declaration's `:= by` and leak its proof body.
        next_decl = re.compile(
            r"^(?:private\s+)?(?:noncomputable\s+)?(?:theorem|lemma|def|abbrev)\s",
            re.MULTILINE,
        ).search(tail, 1)
        scope = tail[:next_decl.start()] if next_decl else tail
        # Find the end of the signature: first `:= by`, `:= sorry`, or `:=` at EOL
        end_match = re.search(r":=\s*by\b|:=\s*sorry\b|:=\s*$", scope, re.MULTILINE)
        if end_match:
            sig = scope[:end_match.start()].rstrip()
        else:
            # term-mode proof (`:= <term>` on the same line): cut at the first `:=`
            eq = scope.find(":=")
            if eq == -1:
                return scope.split("\n", 1)[0]  # fallback: first line only
            sig = scope[:eq].rstrip()
        # Trim if signature is unreasonably long (safety)
        if len(sig) > 1200:
            sig = sig[:1200] + " …"
        return sig

    @classmethod
    def _invalidate_polib_content(cls, polib_lean: "Path") -> None:
        """Evict cached Polib.lean content. Call inside _polib_lock after any write."""
        key = str(polib_lean.resolve())
        with cls._polib_content_cache_lock:
            cls._polib_content_cache.pop(key, None)

    @classmethod
    def _get_polib_lock(cls, polib_lean_path: "Path") -> threading.Lock:
        key = str(polib_lean_path.resolve())
        with cls._polib_locks_meta:
            if key not in cls._polib_locks:
                cls._polib_locks[key] = threading.Lock()
            return cls._polib_locks[key]

    def __init__(self, config: Config):
        self._config = config

        # Claude Code SDK client — no API key needed
        self._sdk = ClaudeSDKClient(model=config.model_main)
        self._sdk_fast = ClaudeSDKClient(model=config.model_fast)

        polib_path = Path(config.polib_path)
        store_path = Path(config.store_path)

        self._store = StoreManager(store_path)

        self._parser = LatexParser()
        self._extractor = GoalExtractor(self._sdk_fast, config.model_fast)
        self._validator = GoalValidator(self._sdk_fast, config.model_fast)
        self._decomposer = BlueprintDecomposer(self._sdk_fast, config.model_fast)
        self._polib_search = PolibSearch(self._store)
        self._mathlib_search = MathlibSearch()
        self._hint_generator = CombinedHintGenerator(
            client=self._sdk_fast,
            model=config.model_fast,
            timeout=8,
            max_hints=16,
        )
        from agent.prover.tools.search import LLMProofReasoningHintGenerator
        self._reasoning_hint_generator = LLMProofReasoningHintGenerator(
            client=self._sdk,
            polib_path=config.polib_path,
        )
        self._llm_hint_generator = LLMHintGenerator(
            client=self._sdk_fast,
            model=config.model_fast,
        )
        self._github_search = GitHubLean4Search(
            timeout=10,
            max_results=2,
        ) if self._config.enable_github_search else None
        self._compiler = LeanCompiler(
            polib_path,
            config.compile_timeout_seconds,
            keep_on_failure=config.keep_temp_on_failure,
            lake_binary=config.lake_binary,
        )
        self._quality = QualityChecker(self._sdk_fast, config.model_fast)
        self._dep_graph = DepGraphManager(self._store)
        try:
            from agent.prover.tools.loogle_validator import LoogleValidator
            self._loogle_validator: 'LoogleValidator | None' = LoogleValidator(timeout=8, max_batch=20)
        except ImportError:
            self._loogle_validator = None
        self._polib_mgr = PolibManager(polib_path, self._polib_search, self._dep_graph)
        self._session = SessionState(self._store)
        # Resolve the actual Polib.lean file (polib_path may be a directory).
        _polib_file = polib_path if polib_path.is_file() else polib_path / "Polib.lean"
        self._polib_lean_path = _polib_file

        # Output directory — Lake project for user inspection
        self._output_root = polib_path.parent / "output"
        self._output_root.mkdir(parents=True, exist_ok=True)

        # Search compiled output files for reference snippets
        self._output_search = OutputSearch(self._output_root)

        # Ensure Polib.lean exists before any compilation
        self._ensure_polib_lean(polib_path)

        # Formalization logger (set in formalize())
        self._flog: FormalizationLogger | None = None

        # Shared sorry counter for parallel nodes
        self._sorry_count = 0
        self._sorry_lock = threading.Lock()

        # Thread-local storage for pending decompose specs (one per thread)
        self._thread_local = threading.local()

        # Locks protecting shared file-write state
        self._save_lock = threading.Lock()   # dep_graph + session saves
        # Class-level lock: shared across ALL agent instances for the same Polib.lean.
        # Covers save→verify→remove atomically to prevent TOCTOU races in parallel mode.
        self._polib_lock = self._get_polib_lock(
            Path(config.polib_path) / "Polib.lean"
        )
        self._output_lock = threading.Lock() # output file writes

        # Per-run code collection: blueprint node_id → final Lean code
        self._run_codes: dict[str, str] = {}
        self._run_codes_lock = threading.Lock()
        # Per-run quality reports: blueprint node_id → QualityReport
        self._run_quality_reports: dict[str, QualityReport] = {}
        # Nodes loaded from Polib (skipped, already proved) — shown as "Retrying..." in quality step
        self._run_skipped_nodes: set[str] = set()

    # ------------------------------------------------------------------
    # Shared sorry counter callbacks
    # ------------------------------------------------------------------

    def _sorry_get(self) -> int:
        with self._sorry_lock:
            return self._sorry_count

    def _sorry_inc(self) -> int:
        with self._sorry_lock:
            self._sorry_count += 1
            return self._sorry_count

    # ------------------------------------------------------------------
    # Helpers
    # ------------------------------------------------------------------

    @staticmethod
    def _ensure_polib_lean(polib_path: Path) -> None:
        """Create polib/Polib.lean if missing, and ensure Polib/_Temp exists.
        Inventory.lean is hand-crafted and never touched here.
        Polib.lean only needs imports — foundational content lives in Inventory.lean."""
        from agent.prover.tools.polib_manager import _SECTION_MARKER
        polib_lean = polib_path / "Polib.lean"
        (polib_path / "Polib" / "_Temp").mkdir(parents=True, exist_ok=True)

        header = (
            "-- Polib.lean\n"
            "-- Dynamic proof accumulation — auto-managed by FormalizerAgent.\n"
            "-- Foundational axioms are in Inventory.lean; proved conjectures are appended here.\n"
            "import Mathlib\n"
            "import Inventory\n\n"
        )

        if not polib_lean.exists():
            polib_lean.write_text(header + _SECTION_MARKER, encoding="utf-8")
            return

        existing = polib_lean.read_text(encoding="utf-8")
        if _SECTION_MARKER in existing:
            proved_part = existing[existing.index(_SECTION_MARKER):]
        else:
            proved_part = _SECTION_MARKER

        if not existing.startswith(header):
            polib_lean.write_text(header + proved_part, encoding="utf-8")
            FormalizerAgent._invalidate_polib_content(polib_lean)

    def _write_output(self, lean_code: str, module_name: str, success: bool) -> None:
        pass

    def _local_refs_block(self, node: BlueprintNode) -> str:
        """Return a formatted reference block from compiled output files, or ''."""
        refs = self._output_search.find_references(node)
        if not refs:
            return ""
        return (
            "\n## Reference Lean 4 proofs from this project (compiled OK) — "
            "study the helper lemma structure, tactic choices, and Finset API usage:\n"
            "```lean\n"
            + "\n\n---\n\n".join(refs)
            + "\n```\n"
        )

    # ── Fix 2: structured error formatter ────────────────────────────────────

    @staticmethod
    def _format_errors_for_prompt(errors: list, max_chars: int = 3000) -> str:
        """Format up to the first 2 structured LeanErrors for a fix prompt.

        Uses parsed fields (line, column, error_class, raw_message, lean_excerpt)
        instead of truncating raw stderr, which can bury the real error in build noise.
        """
        if not errors:
            return "build failed (no structured errors parsed)"
        parts = []
        for e in errors[:2]:
            header = f"Line {e.line}:{e.column} [class {e.error_class}]: {e.raw_message}"
            if e.lean_excerpt:
                parts.append(f"{header}\n  > {e.lean_excerpt}")
            else:
                parts.append(header)
        if len(errors) > 2:
            parts.append(f"... and {len(errors) - 2} more error(s)")
        return "\n".join(parts)[:max_chars]

    # ── Fix 4: error hash for stagnation detection ────────────────────────────

    @staticmethod
    def _hash_primary_error(errors: list) -> str:
        """Return an 8-char MD5 of the primary error after normalising line/col
        numbers and quoted identifiers, so the same logical error hashes identically
        regardless of source position or which identifier the LLM hallucinated.
        """
        if not errors:
            return "no_error"
        e = errors[0]
        msg = e.raw_message
        msg = re.sub(r":\d+:\d+:", ":LINE:COL:", msg)
        msg = re.sub(r"[`']([^`']+)[`']", "IDENTIFIER", msg)
        return hashlib.md5(f"{e.error_class}:{msg}".encode()).hexdigest()[:8]

    # ── Fix 3 + Fix 6: error-class-specific hints with live Loogle search ────

    def _get_error_specific_hints(self, errors: list) -> str:
        """Return a prompt section with hints tailored to the error class(es) present.

        For class-C errors (unknown identifier) also queries Loogle to suggest
        real Mathlib names close to the hallucinated identifier (Fix 6).
        """
        if not errors:
            return ""
        parts: list[str] = []
        classes = {e.error_class for e in errors}
        all_msgs = " ".join(e.raw_message for e in errors)

        if "B" in classes or "type mismatch" in all_msgs:
            parts.append(
                "## Type Mismatch — Cast Hints\n"
                "- ℕ↔ℤ: `Int.ofNat`, `Int.toNat`, `Nat.cast`, `Int.natCast_nonneg`\n"
                "- ℤ↔ℝ: `Int.cast`, `algebraMap ℤ ℝ`\n"
                "- Push casts through sums/products: `push_cast`, `Nat.cast_sum`, `Nat.cast_mul`\n"
                "- Close after casting: `norm_cast`, `exact_mod_cast`, `apply_mod_cast`"
            )

        if "C" in classes or "unknown identifier" in all_msgs:
            safe_tactics = (
                "## Unknown Identifier — Safe Alternatives\n"
                "- Avoid guessing names; use: `omega`, `ring`, `simp`, `norm_num`, `linarith`\n"
                "- Finset sums: `Finset.sum_congr`, `Finset.sum_add_distrib`, `Finset.card_eq_sum_ones`\n"
                "- ℕ linear arithmetic: `omega` closes almost all goals"
            )
            # Fix 6: live Loogle search for each unknown identifier
            lv = getattr(self, "_loogle_validator", None)
            if lv is not None:
                identifiers = re.findall(r"`([^`]+)`", all_msgs)
                loogle_lines: list[str] = []
                for ident in dict.fromkeys(identifiers):  # deduplicate, preserve order
                    hits = lv.search_by_fragment(ident, max_results=4)
                    if hits:
                        loogle_lines.append(f"  - `{ident}` not found; Loogle suggests: " + ", ".join(f"`{h}`" for h in hits))
                    else:
                        loogle_lines.append(f"  - `{ident}` not found in Mathlib; use omega/simp/ring instead")
                if loogle_lines:
                    safe_tactics += "\n## Loogle — Real Mathlib Names (from live search)\n" + "\n".join(loogle_lines)
            parts.append(safe_tactics)

        if "D" in classes or "synthesize" in all_msgs or "instance" in all_msgs:
            parts.append(
                "## Instance Synthesis — Typeclass Hints\n"
                "- Missing `DecidableEq`: add `[DecidableEq α]` to hypotheses\n"
                "- Missing `Fintype`: add `[Fintype α]` or use `Finset.univ`\n"
                "- Missing `AddCommMonoid`: most numeric types provide this automatically\n"
                "- Explicit witness: `haveI : Fintype ... := inferInstance`"
            )

        return ("\n\n".join(parts) + "\n\n") if parts else ""

    def _generate_lean(
        self,
        node: BlueprintNode,
        goal: LockedGoal,
        hints: list[str],
        proven_deps: list[str],
        proven_dep_imports: dict[str, str] | None = None,
        existing_code: str | None = None,
        cross_run_errors: list[dict] | None = None,
    ) -> str:
        """Generate Lean 4 code for `node`.

        proven_dep_imports maps node_id → Lean import path (e.g.
        "Polib.Polytope.DefOccupiedEdge") for deps that are already saved in
        polib.  Deps without an entry are mentioned by name only.

        existing_code: if provided (non-trivial prior attempt), include it as
        context so Claude can see the proof structure and fix the sorrys.
        If None, generate completely from scratch.
        """
        _m = re.search(r"\btheorem\s+(\w+)", goal.lean_signature)
        theorem_name = _m.group(1) if _m else "ThmMain"
        dep_imports_map = proven_dep_imports or {}

        if node.is_main_target:
            goal_context = _GOAL_CONTEXT_MAIN.format(lean_signature=goal.lean_signature)
            goal_instruction = _GOAL_INSTR_MAIN
        else:
            goal_context = _GOAL_CONTEXT_INTERMEDIATE.format(
                theorem_name=theorem_name,
                node_id=node.node_id,
                node_type=node.node_type,
                parent_signature=goal.lean_signature,
            )
            goal_instruction = _GOAL_INSTR_INTERMEDIATE.format(
                node_id=node.node_id,
                node_type=node.node_type,
                theorem_name=theorem_name,
            )

        # Build dep import block and dep detail block
        # All proved deps live in Polib.lean — one import covers everything
        # Tier 1: only list direct dependencies in the prompt (not transitive)
        direct_imports_map = filter_dep_imports_to_direct(node.dependencies, dep_imports_map)
        seen_imports: set[str] = set()
        dep_import_lines: list[str] = []
        dep_detail_lines: list[str] = []
        partial_inline_blocks: list[str] = []  # code bodies for partial direct deps
        for dep_id in proven_deps:
            if dep_id in direct_imports_map:
                imp = direct_imports_map[dep_id]
                if imp not in seen_imports:
                    dep_import_lines.append(f"import {imp}")
                    seen_imports.add(imp)
                # Look up the actual Lean identifier (may differ from blueprint node_id)
                polib_entry = self._polib_search.find_by_node_id(dep_id)
                actual_name = polib_entry.theorem_name if polib_entry and polib_entry.theorem_name != dep_id else None
                entry_status = polib_entry.status if polib_entry else "proved"
                status_note = " — partial, has sorry" if entry_status == "partial" else ""
                lean_name = actual_name or dep_id
                # Extract the actual signature from Polib.lean so the LLM sees the
                # exact API (param count, types, hypotheses) and cannot hallucinate args.
                dep_sig = self._extract_polib_signature(lean_name)
                if actual_name:
                    head = f"  - `{dep_id}` → Lean identifier: `{actual_name}` (available via import {imp}{status_note})"
                else:
                    head = f"  - `{dep_id}` (available via import {imp}{status_note})"
                dep_detail_lines.append(head)
                if dep_sig:
                    dep_detail_lines.append(f"    Signature (call with EXACTLY these arguments):")
                    for sline in dep_sig.splitlines():
                        dep_detail_lines.append(f"      {sline}")
            elif dep_id in node.dependencies:
                # Partial direct dep: inline its code so the LLM can reference it by name
                partial_code = self._get_partial_dep_code(dep_id)
                if partial_code:
                    # Tier 2: strip proof bodies — dep only needs signatures in context
                    partial_inline_blocks.append(extract_signature(partial_code))
                    dep_detail_lines.append(
                        f"  - `{dep_id}` (partial — included inline below; reference it by name directly)"
                    )
                else:
                    dep_detail_lines.append(f"  - `{dep_id}` (proved in this session, not yet in polib)")
            else:
                dep_detail_lines.append(f"  - `{dep_id}` (proved in this session, not yet in polib)")

        dep_imports_str = ("\n".join(dep_import_lines) + "\n") if dep_import_lines else ""
        dep_details_str = "\n".join(dep_detail_lines) if dep_detail_lines else "  (none)"

        # GitHub reference snippets (structural reference only)
        github_snippets_text = ""
        if self._github_search is not None:
            try:
                github_snippets = self._github_search.search(node)
                if github_snippets:
                    github_snippets_text = (
                        "\n## Reference Lean 4 formalizations from GitHub"
                        " (structural reference only — do NOT copy verbatim):\n"
                        + "\n---\n".join(github_snippets)
                        + "\n"
                    )
            except Exception:
                pass

        # Partial dependency inline blocks — included before the file body
        partial_inline_str = ""
        if partial_inline_blocks:
            partial_inline_str = (
                "\n## Partial dependencies (include these verbatim BEFORE your lemma — they "
                "compile with sorry but let you reference them by name):\n"
                "```lean\n"
                + "\n\n".join(partial_inline_blocks)
                + "\n```\n"
            )

        # Cross-run failure memory: previous attempts that failed across retries
        cross_run_str = ""
        if cross_run_errors:
            lines = ["\n## Previous failed attempts across retries — do NOT repeat these approaches:\n"]
            for i, rec in enumerate(cross_run_errors, 1):
                lines.append(f"### Failed attempt {i}:")
                lines.append(f"Error: {rec['error']}")
                if rec.get("code_snippet"):
                    lines.append(f"```lean\n{rec['code_snippet']}\n```")
            cross_run_str = "\n".join(lines) + "\n"

        # Prior attempt context — included only when a non-trivial partial exists
        if existing_code is not None:
            prior_context = (
                cross_run_str
                + partial_inline_str
                + "\n## Prior attempt (this compiled but has sorrys — fix the sorrys):\n"
                f"```lean\n{existing_code}\n```\n"
            )
        else:
            prior_context = cross_run_str + partial_inline_str

        prompt = LEAN_GENERATION_PROMPT.format(
            node_id=node.node_id,
            node_type=node.node_type,
            description=node.description,
            latex_fragment=node.latex_fragment,
            goal_context=goal_context,
            dep_imports=dep_imports_str,
            dep_details=dep_details_str,
            mathlib_hints="\n".join(f"  - {h}" for h in hints) or "  (none)",
            goal_instruction=goal_instruction,
            github_snippets=github_snippets_text,
            local_references=self._local_refs_block(node),
            prior_context=prior_context,
        )
        raw = self._sdk._call(prompt, fast_model=self._config.model_fast,
                              system=LEAN_GENERATION_SYSTEM_PROMPT)
        code = self._normalize_lean(self._strip_markdown(raw))
        code = self._ensure_preamble(code)
        if not node.is_main_target:
            code = _rename_last_decl(code, node.node_id)
        return code

    def _targeted_fix(
        self,
        lean_code: str,
        result: "CompileResult",
        node: BlueprintNode,
        hints: list[str],
        round_num: int,
        banned_ids: set[str] | None = None,
    ) -> str:
        """Send structured errors + full source to Claude and ask for a targeted fix."""
        error_block = self._format_errors_for_prompt(result.errors)
        hints_str = "\n".join(f"  - {h}" for h in hints) or "  (none)"
        local_refs = self._local_refs_block(node)
        specific_hints = self._get_error_specific_hints(result.errors)
        banned_block = ""
        if banned_ids:
            banned_list = ", ".join(f"`{x}`" for x in sorted(banned_ids))
            banned_block = (
                f"## ⛔ IDENTIFIERS THAT DO NOT EXIST — NEVER USE THESE\n"
                f"The following names were rejected by Lean as unknown. They do NOT exist\n"
                f"in Lean, Mathlib, or Inventory. Do NOT use any of them:\n"
                f"  {banned_list}\n"
                f"Instead use the geometric axiom lemmas (standalone, not structure fields;\n"
                f"hM : IsMap maps comes from the theorem's hypotheses):\n"
                f"  euler_formula maps hM, handshake maps hM, regularity maps hM,\n"
                f"  kgon_occupation_bound maps hM, occupation_bound maps hM, equality_family n\n\n"
            )
        dep_sigs_block = self._format_dep_signatures_block(node.dependencies)
        prompt = (
            f"Fix this Lean 4 compilation error. Round {round_num + 1}.\n\n"
            f"## Node\n{node.node_id}: {node.description}\n\n"
            f"## Compilation Error\n```\n{error_block}\n```\n\n"
            f"## Current Lean 4 Source\n```lean\n{lean_code}\n```\n\n"
            + dep_sigs_block
            + local_refs
            + banned_block
            + specific_hints
            + FIX_LOOP_POLIB_REF + "\n"
            + f"## Available Mathlib Lemmas\n{hints_str}\n\n"
            f"## Lean 4 Finset API — verified correct names:\n"
            f"- Split Finset.Ico sum at midpoint: `Finset.sum_Ico_consecutive` (needs a ≤ b, b ≤ c)\n"
            f"- Combine disjoint sums: `Finset.sum_union` (needs `Disjoint s t`)\n"
            f"- Prove Ico disjointness: `simp [Finset.disjoint_left, Finset.mem_Ico]; omega`\n"
            f"- Ico membership: `Finset.mem_Ico`, filter membership: `Finset.mem_filter`\n"
            f"- Cast in sums: `push_cast`, `Nat.cast_mul`, `Nat.cast_sum`\n"
            f"- ⚠ DOES NOT EXIST — NEVER USE: `Finset.disjoint_Ico_Ico`, "
            f"`Finset.Ico_disjoint_Ico.mpr`, `Finset.sum_Ico_split`\n\n"
            f"Instructions:\n"
            f"- Read the error message carefully and locate the exact problem\n"
            f"- Make the minimal targeted change to fix it\n"
            f"- Do NOT change the theorem statement or its type signature\n"
            f"- ALWAYS use `import Mathlib` (umbrella). NEVER use specific submodule\n"
            f"  paths like `import Mathlib.Algebra.BigOperators.Basic` — they are\n"
            f"  version-dependent and will break the build\n"
            f"- ⚡ If you cannot fix the error, try using Inventory lemmas:\n"
            f"  P6EdgeCountEquation, P6InequalityPart, Juc_EulerFormula (see Inventory reference above).\n"
            f"- Do NOT write sorry — the system rejects sorry and will ask you to fix it.\n"
            f"- Return ONLY the complete corrected Lean 4 file inside a ```lean fence.\n"
            f"  Do not write any prose or explanation outside the fence."
        )
        raw = self._sdk_fast._call(prompt)
        fixed = self._normalize_lean(self._strip_markdown(raw))
        fixed = self._ensure_preamble(fixed)
        return fixed if fixed.strip() else lean_code

    def _escalation_phase(self, round_num: int) -> int:
        if round_num < self._ESCALATION_HINT_REFRESH: return 0
        elif round_num < self._ESCALATION_DECOMPOSE:  return 1
        elif round_num < self._ESCALATION_DECIDE:     return 2
        else:                                          return 3

    def _targeted_fix_sorry_removal(
        self,
        lean_code: str,
        node: BlueprintNode,
        hints: list[str],
        round_num: int,
    ) -> str:
        """Ask Claude to remove all sorry from successfully-compiled code by using Inventory lemmas.

        Called when the code compiles but contains sorry that the prover refuses to accept.
        """
        sorry_blocks = self._find_sorry_blocks(lean_code)
        n_sorry = len(sorry_blocks)
        hints_str = "\n".join(f"  - {h}" for h in hints) or "  (none)"
        sorry_list = "\n".join(
            f"  {i+1}. {b['desc'][:300]}" for i, b in enumerate(sorry_blocks)
        )
        local_refs = self._local_refs_block(node)
        dep_sigs_block = self._format_dep_signatures_block(node.dependencies)
        prompt = (
            f"This Lean 4 code compiles successfully but contains {n_sorry} sorry(s). "
            f"The system requires zero sorry in the final proof. "
            f"Your job: REMOVE ALL sorry by replacing them with real proofs.\n\n"
            f"## Node\n{node.node_id}: {node.description}\n\n"
            f"## Sorry blocks to fix (must ALL be replaced)\n{sorry_list}\n\n"
            f"## Current Lean 4 Source (compiles, but has sorry)\n```lean\n{lean_code}\n```\n\n"
            + dep_sigs_block
            + local_refs
            + FIX_LOOP_POLIB_REF + "\n"
            + f"## Key Inventory lemmas to use instead of sorry (hM : IsMap maps required):\n"
            f"- `P6EdgeCountEquation maps hM`   (proved): 3*p₃ = 12*(1-g) - 2*p₄ - p₅ + Σ_{{k≥7}}(k-6)*p_k\n"
            f"  → rearranges to: 3*p₃ + 2*p₄ + p₅ = 12*(1-g) + Σ_{{k≥7}}(k-6)*p_k\n"
            f"  → call: `have h := P6EdgeCountEquation maps hM; linarith`\n"
            f"- `Juc_EulerFormula maps hM`      (proved, g=0): 3*p₃ = 12 - 2*p₄ - p₅ + Σ_{{k≥7}}(k-6)*p_k\n"
            f"- `P6InequalityPart maps hM hm`   (PROVED): 3*p₆ ≥ 12*(1-g) - 2*p₄ - 3*p₅ + Σ_{{k≥7}}((k+1)/2-6)*p_k\n"
            f"  → hm : maps.m ≥ 6 is required; derive from hypotheses or add as hypothesis\n"
            f"- `Juc_InequalityPart maps hM hm` (PROVED, g=0): same bound\n"
            f"- `euler_formula maps hM`, `handshake maps hM`, `regularity maps hM` (axioms)\n"
            f"- `occupation_conservation maps hM hm`, `occupation_bound maps hM k hk`, "
            f"`quad_occ_cancellation maps hM hm` (axioms; hm : maps.m ≥ 6)\n\n"
            f"## Strategy\n"
            f"1. For each sorry, identify what fact is needed.\n"
            f"2. Find an Inventory lemma that provides it (see list above).\n"
            f"3. Replace `sorry` with `have h := <Inventory lemma>; linarith` or `exact h`.\n"
            f"4. Calling Inventory lemmas is NOT a new sorry — they are the accepted axiom base.\n"
            f"5. ⛔ NEVER fix a sorry by writing a NEW sorried helper — the axiom base is closed; "
            f"such files are rejected.\n\n"
            f"## Available Mathlib Lemmas\n{hints_str}\n\n"
            f"## Instructions\n"
            f"- Replace EVERY sorry with a real proof or Inventory lemma call\n"
            f"- Do NOT write any new sorry under any circumstances\n"
            f"- Do NOT change the theorem statement or its type signature\n"
            f"- Return ONLY the complete Lean 4 file inside a ```lean fence."
        )
        raw = self._sdk._call(prompt, timeout=180)
        fixed = self._normalize_lean(self._strip_markdown(raw))
        fixed = self._ensure_preamble(fixed)
        return fixed if fixed.strip() else lean_code

    def _targeted_fix_strict(
        self,
        lean_code: str,
        result: "CompileResult",
        node: BlueprintNode,
        hints: list[str],
        round_num: int,
        banned_ids: set[str] | None = None,
    ) -> str:
        """Phase 1: strict fix — only verified hint names, Sonnet for higher accuracy."""
        error_block = self._format_errors_for_prompt(result.errors)
        hints_str = "\n".join(f"  - {h}" for h in hints) or "  (none)"
        local_refs = self._local_refs_block(node)
        specific_hints = self._get_error_specific_hints(result.errors)
        banned_block = ""
        if banned_ids:
            banned_list = ", ".join(f"`{x}`" for x in sorted(banned_ids))
            banned_block = (
                f"## ⛔ IDENTIFIERS THAT DO NOT EXIST — NEVER USE THESE\n"
                f"These names do NOT exist anywhere in Lean/Mathlib/Inventory:\n"
                f"  {banned_list}\n"
                f"Use only names from the verified list below or the structure fields.\n\n"
            )
        dep_sigs_block = self._format_dep_signatures_block(node.dependencies)
        prompt = (
            f"CRITICAL: Only use lemma names from the verified list below. "
            f"When uncertain, use omega/simp/linarith/ring instead of guessing names.\n\n"
            f"Fix this Lean 4 compilation error. Round {round_num + 1}.\n\n"
            f"## Node\n{node.node_id}: {node.description}\n\n"
            f"## Compilation Error\n```\n{error_block}\n```\n\n"
            f"## Current Lean 4 Source\n```lean\n{lean_code}\n```\n\n"
            + dep_sigs_block
            + local_refs
            + banned_block
            + specific_hints
            + FIX_LOOP_POLIB_REF + "\n"
            + f"## Verified Mathlib Lemmas (ONLY use names from this list)\n{hints_str}\n\n"
            f"Instructions:\n"
            f"- ONLY reference lemma names that appear in the Inventory reference or verified list above\n"
            f"- You MAY also use lemma names that appear verbatim in the Reference proofs above\n"
            f"- When you cannot find the right lemma, use omega, simp, linarith, or ring\n"
            f"- Do NOT invent or guess lemma names\n"
            f"- Do NOT change the theorem statement or its type signature\n"
            f"- ⚡ If the proof cannot be fixed with standard tactics, try Inventory lemmas:\n"
            f"  P6EdgeCountEquation, P6InequalityPart, Juc_EulerFormula, etc.\n"
            f"- Do NOT write sorry — the system rejects sorry and will ask you to fix it.\n"
            f"- Return ONLY the complete corrected Lean 4 file inside a ```lean fence."
        )
        raw = self._sdk._call(prompt, timeout=150)
        fixed = self._normalize_lean(self._strip_markdown(raw))
        fixed = self._ensure_preamble(fixed)
        return fixed if fixed.strip() else lean_code

    def _targeted_fix_decompose(
        self,
        lean_code: str,
        result: "CompileResult",
        node: BlueprintNode,
        hints: list[str],
        round_num: int,
        banned_ids: set[str] | None = None,
    ) -> str:
        """Phase 2: rewrite proof as a chain of `have` sub-steps, each closed by one tactic."""
        error_block = self._format_errors_for_prompt(result.errors)
        hints_str = "\n".join(f"  - {h}" for h in hints) or "  (none)"
        local_refs = self._local_refs_block(node)
        specific_hints = self._get_error_specific_hints(result.errors)
        banned_block = ""
        if banned_ids:
            banned_list = ", ".join(f"`{x}`" for x in sorted(banned_ids))
            banned_block = (
                f"## ⛔ IDENTIFIERS THAT DO NOT EXIST — NEVER USE THESE\n"
                f"Lean rejected these names as unknown. They do NOT exist:\n"
                f"  {banned_list}\n"
                f"Do NOT use them in any `have` step. Use only structure fields and the\n"
                f"verified lemmas listed below.\n\n"
            )
        dep_sigs_block = self._format_dep_signatures_block(node.dependencies)
        prompt = (
            f"Rewrite this Lean 4 proof as a chain of `have` sub-steps where each step "
            f"is provable by a single tactic (omega / simp / linarith / ring / norm_num).\n\n"
            f"## Node\n{node.node_id}: {node.description}\n\n"
            f"## Compilation Error\n```\n{error_block}\n```\n\n"
            f"## Current Lean 4 Source\n```lean\n{lean_code}\n```\n\n"
            + dep_sigs_block
            + local_refs
            + banned_block
            + specific_hints
            + FIX_LOOP_POLIB_REF + "\n"
            + f"## Available Mathlib Lemmas\n{hints_str}\n\n"
            f"Instructions:\n"
            f"- Break the proof body into small `have h : ... := by ...` steps\n"
            f"- Each step must be dischargeable by exactly one tactic: omega, simp, linarith, ring, or norm_num\n"
            f"- Use the Inventory geometric axiom lemmas listed above as building blocks\n"
            f"- You MAY reuse helper lemmas shown verbatim in the Reference proofs above\n"
            f"- Do NOT change the theorem statement or type signature\n"
            f"- ALWAYS use `import Mathlib` (umbrella), never specific submodule paths\n"
            f"- Return ONLY the complete Lean 4 file inside a ```lean fence."
        )
        raw = self._sdk._call(prompt, timeout=150)
        fixed = self._normalize_lean(self._strip_markdown(raw))
        fixed = self._ensure_preamble(fixed)
        return fixed if fixed.strip() else lean_code

    def _insert_sorry(
        self,
        lean_code: str,
        result: "CompileResult",
        node: BlueprintNode,
    ) -> str:
        """Replace the first failing tactic with a structured sorry block as last resort."""
        raw_msg = result.errors[0].raw_message[:120] if result.errors else "build failed"
        err_class = result.errors[0].error_class if result.errors else "A"

        # Replace the entire proof body of the target declaration with sorry.
        # Patching a single line is unreliable when there are multiple errors
        # (e.g. several unknown identifiers). Replacing the whole body guarantees
        # the sorry'd file compiles cleanly.
        # Lazy .*? with DOTALL matches through multi-line signatures (which contain `:`)
        # without stopping at the first colon like [^:=\n]* would.
        # Group 3 captures the old proof body so the lambda can drop it.
        _decl_re = re.compile(
            r"^((?:(?:private|noncomputable|protected)\s+)*(?:lemma|theorem|def|abbrev)\s+"
            + re.escape(node.node_id)
            + r"\b.*?)"
            r"(\s*:=\s*by\b)(.*)",
            re.DOTALL | re.MULTILINE,
        )
        sorry_body = (
            f"  -- [SORRY] class: {err_class}\n"
            f"  -- [SORRY] reason: {raw_msg.replace(chr(10), ' ')}\n"
            f"  -- [SORRY] impact: blocks {node.node_id}\n"
            f"  -- [SORRY] suggested_next: fix compilation error then remove sorry\n"
            f"  sorry"
        )
        # Try to replace the body of the named declaration
        replaced = _decl_re.sub(
            lambda m: m.group(1) + " := by\n" + sorry_body + "\n",
            lean_code,
            count=1,
        )
        if replaced != lean_code:
            return replaced

        # Fallback: find the FIRST `:= by` after the declaration header (not rfind,
        # which would land inside a `have` clause and produce broken code).
        _decl_start_re = re.compile(
            r"^(?:(?:private|noncomputable|protected)\s+)*(?:lemma|theorem|def|abbrev)\s+"
            + re.escape(node.node_id)
            + r"\b",
            re.MULTILINE,
        )
        _m = _decl_start_re.search(lean_code)
        if _m:
            _after = lean_code[_m.start():]
            _idx = _after.find(":= by")
            if _idx != -1:
                _cut = _m.start() + _idx
                return lean_code[:_cut] + ":= by\n" + sorry_body + "\n"

        # Last resort: replace everything after the first `:= by` with sorry
        idx = lean_code.find(":= by")
        if idx != -1:
            return lean_code[:idx] + ":= by\n" + sorry_body + "\n"

        # Final fallback: append sorry as a standalone lemma
        return lean_code + f"\n{sorry_body}\n"

    @staticmethod
    def _strip_named_declaration(code: str, name: str) -> str:
        """Remove the definition of `name` from `code`.

        Handles lemma/theorem/def/abbrev declarations that span multiple lines by finding
        the next top-level declaration after `name`'s header and deleting everything in between.
        Preserves all other content unchanged.
        """
        lines = code.splitlines()
        # Pattern: a top-level declaration starting with optional 'private ' then
        # lemma/theorem/def/abbrev followed by the exact name.
        start_re = re.compile(
            r"^(?:private\s+)?(?:lemma|theorem|def|abbrev)\s+" + re.escape(name) + r"\b"
        )
        # Pattern: any NEW top-level declaration (to find end of current one)
        next_decl_re = re.compile(
            r"^(?:private\s+)?(?:lemma|theorem|def|abbrev|structure|namespace|end|section|#)\s"
        )
        start_line = None
        for i, line in enumerate(lines):
            if start_re.match(line.strip()):
                start_line = i
                break
        if start_line is None:
            return code  # name not found, nothing to strip

        # Find where the declaration ends: the next top-level declaration after start_line
        end_line = len(lines)
        for i in range(start_line + 1, len(lines)):
            stripped = lines[i].strip()
            if stripped and next_decl_re.match(stripped):
                end_line = i
                break

        # Remove the declaration block (including any doc comment lines immediately before it)
        doc_start = start_line
        for i in range(start_line - 1, -1, -1):
            stripped = lines[i].strip()
            if stripped.startswith("/--") or stripped.startswith("--") or not stripped:
                doc_start = i
            else:
                break

        kept = lines[:doc_start] + lines[end_line:]
        return "\n".join(kept)

    @staticmethod
    def _strip_markdown(text: str) -> str:
        """Extract Lean code from LLM response, stripping markdown fences and prose."""
        for pattern in (r"```lean\s*\n(.*?)```", r"```\s*\n(.*?)```"):
            m = re.search(pattern, text, re.DOTALL)
            if m:
                return m.group(1).strip()
        # Treat text as raw code only if it starts with `import Mathlib` (no prose prefix).
        # Prose responses that mention "import" mid-sentence are not code.
        stripped = text.strip()
        if stripped.startswith("import Mathlib"):
            return stripped
        return ""

    @staticmethod
    def _strip_inline_shared_struct(code: str) -> str:
        """Remove any inlined SimplyCon3ConnectedMap structure definition.

        Uses line-by-line scanning to correctly handle the case where a comment
        contains 'end SimplyCon3ConnectedMap'.
        """
        lines = code.splitlines()
        result: list[str] = []
        depth = 0
        inside = False

        for line in lines:
            stripped = line.strip()
            if not inside:
                if stripped.startswith("structure SimplyCon3ConnectedMap") or \
                   stripped.startswith("namespace SimplyCon3ConnectedMap"):
                    inside = True
                    depth = 1
                    continue
                result.append(line)
            else:
                # Count real (non-comment) end keywords
                if not stripped.startswith("--"):
                    if stripped == "end SimplyCon3ConnectedMap":
                        depth -= 1
                        if depth == 0:
                            inside = False
                        continue
                result.append(line)

        return "\n".join(result)

    @staticmethod
    def _normalize_lean(code: str) -> str:
        """Post-process LLM-generated Lean code to fix common version-dependent issues.

        1. Collapses `import Mathlib.X.Y` → `import Mathlib` (umbrella only).
        2. Fixes `∑ x in s` → `∑ x ∈ s` (Lean 4 Mathlib requires ∈, not the keyword in).
        3. Removes `axiom` declarations (not allowed in polib).
        4. Removes any inlined SimplyCon3ConnectedMap definition.
        """
        # Collapse specific Mathlib sub-imports into the umbrella import
        code = re.sub(r"^import Mathlib\.\S+", "import Mathlib", code, flags=re.MULTILINE)
        # Deduplicate `import Mathlib`
        lines = code.splitlines()
        seen_mathlib = False
        result = []
        for line in lines:
            if line.strip() == "import Mathlib":
                if not seen_mathlib:
                    result.append(line)
                    seen_mathlib = True
            else:
                result.append(line)
        code = "\n".join(result)
        # Fix sum notation: `∑ <var> in <set>` → `∑ <var> ∈ <set>`
        code = re.sub(r"(∑[^∈\n,]*?)\s+\bin\b\s+", r"\1 ∈ ", code)
        # Strip axiom declarations (polib rejects them; replace with sorry stubs)
        code = re.sub(r"^axiom\s+[^\n]*\n?", "", code, flags=re.MULTILINE)
        # Remove any inlined SimplyCon3ConnectedMap definition
        code = FormalizerAgent._strip_inline_shared_struct(code)
        return code

    @staticmethod
    def _ensure_preamble(code: str) -> str:
        """Guarantee that import Mathlib + import Inventory.Shared are at the top.

        If the code is empty or already has the shared import, return as-is.
        Otherwise strip stale import lines and prepend the canonical two-line header.
        Also strips any inline SimplyCon3ConnectedMap definition (it lives in Shared now).
        """
        if not code.strip():
            return LEAN_PREAMBLE
        # Strip any inlined shared structure definition
        code = FormalizerAgent._strip_inline_shared_struct(code)
        if "import Inventory.Shared" in code:
            return code
        # Remove stale import lines and prepend canonical preamble
        code = re.sub(r"^import Mathlib[^\n]*\n?", "", code, flags=re.MULTILINE)
        code = re.sub(r"^import Inventory\.Basic[^\n]*\n?", "", code, flags=re.MULTILINE)
        return LEAN_PREAMBLE + "\n" + code.lstrip()

    @staticmethod
    def _has_sorry(code: str) -> bool:
        """Return True if code contains any sorry tactic (not in comments)."""
        sorry_re = re.compile(r"\bsorry\b")
        for line in code.splitlines():
            if line.strip().startswith("--"):
                continue
            if sorry_re.search(line):
                return True
        return False

    @staticmethod
    def _find_sorry_blocks(code: str) -> list[dict]:
        """Return a list of sorry blocks, each as {start, end, desc}.

        Detects both `exact sorry` and bare `sorry` tactic lines.
        Skips comment lines. Each block includes preceding `-- [SORRY]` annotations.
        """
        sorry_re = re.compile(r"\bsorry\b")
        lines = code.splitlines()
        blocks: list[dict] = []
        for i, line in enumerate(lines):
            if line.strip().startswith("--"):
                continue
            if not sorry_re.search(line):
                continue
            start = i
            j = i - 1
            while j >= 0 and lines[j].strip().startswith("-- [SORRY]"):
                start = j
                j -= 1
            blocks.append({
                "start": start,
                "end": i,
                "desc": "\n".join(lines[start : i + 1]),
            })
        return blocks

    # ── Mechanical tactic closer ──────────────────────────────────────────────

    _ESCALATION_HINT_REFRESH = 4
    _ESCALATION_DECOMPOSE    = 7
    _ESCALATION_DECIDE       = 10

    # After this many total failed rounds, ask LLM whether to decompose.
    # Set above max_rounds_per_node so decompose never fires during the main loop.
    _DECOMPOSE_CHECK_AFTER = 10

    _MECHANICAL_TACTICS: list[str] = [
        "decide",
        "trivial",
        "aesop",
        "omega",
        "norm_num",
        "simp",
        "tauto",
        "ring",
    ]

    def _try_mechanical_tactics(
        self,
        lean_code: str,
        node_id: str,
        verbose: bool = True,
    ) -> str | None:
        """Replace 'exact sorry' with each mechanical tactic in turn.

        Returns the first version of lean_code that compiles successfully,
        or None if no mechanical tactic closes all sorrys.
        This runs BEFORE any Claude API call in the sorry-elimination loop,
        saving API budget for genuinely hard goals.
        """
        sorry_re = re.compile(r"\bexact\s+sorry\b|\bsorry\b")

        def has_sorry(code: str) -> bool:
            return any(
                sorry_re.search(line)
                for line in code.splitlines()
                if not line.strip().startswith("--")
            )

        if not has_sorry(lean_code):
            return lean_code  # Already clean

        for tactic in self._MECHANICAL_TACTICS:
            candidate = re.sub(
                r"(?m)^(\s*)--\s*\[SORRY\].*\n(?:.*--\s*\[SORRY\].*\n)*\s*exact\s+sorry",
                lambda m: m.group(1) + tactic,
                lean_code,
            )
            # Also replace bare sorry not in a block
            candidate = re.sub(r"\bexact\s+sorry\b", tactic, candidate)
            candidate = re.sub(r"(?<!\w)sorry(?!\w)", tactic, candidate)

            try:
                result = self._compiler.compile(
                    self._normalize_lean(candidate),
                    node_id + f"_mech_{tactic}",
                )
                if result.success:
                    self._log(
                        verbose,
                        f"  [mechanical] {node_id}: sorry closed by `{tactic}`",
                    )
                    return candidate
            except Exception:
                continue

        return None

    # Inventory-based proof templates tried before LLM generation.
    # Each entry is a tactic block injected after `:= by`.
    _INVENTORY_TEMPLATES: list[str] = [
        # Single lemma + linarith (most common pattern)
        "  have h := P6EdgeCountEquation maps hM\n  push_cast\n  linarith",
        "  have h := Juc_EulerFormula maps hM\n  push_cast\n  linarith",
        "  have h := P6InequalityPart maps hM hm\n  linarith",
        "  have h := Juc_InequalityPart maps hM hm\n  linarith",
        # Combinations
        "  have h1 := P6EdgeCountEquation maps hM\n  have h2 := P6InequalityPart maps hM hm\n  push_cast\n  linarith",
        "  have h1 := Juc_EulerFormula maps hM\n  have h2 := Juc_InequalityPart maps hM hm\n  linarith",
        # Three axioms
        "  have he := euler_formula maps hM\n  have hh := handshake maps hM\n  have hr := regularity maps hM\n  push_cast\n  linarith",
        # JucovicTheorem direct
        "  exact (JucovicTheorem maps hM h1).1",
        # omega variant
        "  have h := P6EdgeCountEquation maps hM\n  push_cast at *\n  omega",
        # edge count + euler
        "  have h1 := P6EdgeCountEquation maps hM\n  have he := euler_formula maps hM\n  have hh := handshake maps hM\n  push_cast\n  linarith",
    ]

    def _inventory_template_probe(
        self, lean_code: str, node_id: str, verbose: bool
    ) -> tuple[str, bool]:
        """Try to prove this node using Inventory lemma templates compiled in parallel.

        Takes the LLM-generated code, finds where the proof body starts (':= by'),
        replaces it with each template, and compiles all candidates concurrently.
        Returns (proved_code, True) on first success, (lean_code, False) if all fail.
        """
        import re as _re

        # Find the last ':= by' — that is where the main declaration's proof body starts.
        by_matches = list(_re.finditer(r':=\s*by\b', lean_code))
        if not by_matches:
            return lean_code, False
        last_by = by_matches[-1]
        before_proof = lean_code[:last_by.end()]

        candidates = [
            (before_proof + "\n" + tmpl + "\n", tmpl)
            for tmpl in self._INVENTORY_TEMPLATES
        ]

        # Compile all candidates in parallel
        with ThreadPoolExecutor(max_workers=min(len(candidates), 4)) as pool:
            futures = {
                pool.submit(self._compiler.compile, code, node_id + "_inv"): (code, tmpl)
                for code, tmpl in candidates
            }
            for fut in as_completed(futures):
                code, tmpl = futures[fut]
                try:
                    result = fut.result()
                except Exception:
                    continue
                if result.success and not self._has_sorry(code):
                    self._log(verbose,
                        f"  [inv-probe] {node_id}: proved by Inventory template "
                        f"({tmpl.strip()[:60]}...)")
                    return code, True

        return lean_code, False

    def _partial_solver(
        self,
        node: "BlueprintNode",
        goal_lock: "GoalLock",
        hints: list[str],
        proven_node_ids: list[str],
        proven_dep_imports: dict[str, str],
        category: str,
        node_id: str,
        verbose: bool,
        existing_code: str | None = None,
        cross_run_errors: list[dict] | None = None,
    ) -> tuple[str, bool, list]:
        """Generate a fresh proof, compile through the fix loop, and return."""
        lean_code = self._generate_lean(
            node, goal_lock.goal, hints, proven_node_ids,
            proven_dep_imports=proven_dep_imports,
            existing_code=existing_code,
            cross_run_errors=cross_run_errors,
        )

        # Fast Inventory-first probe: try simple Inventory lemma + linarith templates
        # before entering the full fix loop.  No LLM call needed — pure compilation.
        probe_code, probe_ok = self._inventory_template_probe(lean_code, node_id, verbose)
        if probe_ok:
            return probe_code, True, []

        lean_code, compile_ok, last_errors = self._compile_loop(
            lean_code, node, hints, node_id, verbose,
            goal_signature=goal_lock.goal.lean_signature,
        )

        return lean_code, compile_ok, last_errors

    def _log(self, verbose: bool, msg: str) -> None:
        if verbose:
            print(msg)

    # ------------------------------------------------------------------
    # Cache helpers (goal lock + blueprint keyed by LaTeX hash)
    # ------------------------------------------------------------------

    def _cache_key(self, parsed: ParsedTheorem) -> str:
        import hashlib
        content = f"{parsed.name}|{'|'.join(parsed.hypotheses)}|{parsed.conclusion}"
        return hashlib.sha256(content.encode()).hexdigest()[:16]

    def _goal_cache_key(self, parsed: ParsedTheorem) -> str:
        # Use the raw-LaTeX hash so the cached goal survives across runs on the
        # same file even when the LLM extracts hypotheses/conclusion differently.
        return getattr(parsed, 'latex_hash', None) or self._cache_key(parsed)

    def _blueprint_cache_key(self, parsed: ParsedTheorem, goal_lock: GoalLock) -> str:
        import hashlib
        latex_key = getattr(parsed, 'latex_hash', None) or self._cache_key(parsed)
        # Hash the shared structure definition — invalidate when SimplyCon3ConnectedMap
        # fields change (e.g. new axioms added), so the blueprint is regenerated with
        # the updated field set in scope.
        # NOTE: polib_hash intentionally excluded — new proved lemmas are always
        # available via `import Inventory` without needing a blueprint regeneration.
        # Including it caused blueprint churn (different strategy each run → worse results).
        from agent.prover.prompts.lean_generation import SHARED_MODULE_CONTENT
        struct_hash = hashlib.sha256(SHARED_MODULE_CONTENT.encode()).hexdigest()[:8]
        return f"{latex_key}:{struct_hash}"

    def _load_cached_goal(self, parsed: ParsedTheorem, verbose: bool = True) -> GoalLock | None:
        key = self._goal_cache_key(parsed)
        goals = self._store.get("goals") or {}
        data = goals.get(key)
        if data is None:
            return None
        try:
            locked = LockedGoal.from_dict(data)
            # Don't reuse a goal that was never confirmed — re-extract so the
            # updated validator gets a chance to confirm (or improve) the signature.
            if not locked.validator_confirmed:
                self._log(verbose, f"      [cache skip] goal was unconfirmed — re-extracting")
                return None
            goal_lock = GoalLock(locked)
            self._log(verbose, f"      [cache hit] goal loaded from store (key={key})")
            return goal_lock
        except Exception:
            return None

    def _save_cached_goal(self, parsed: ParsedTheorem, goal_lock: GoalLock) -> None:
        key = self._goal_cache_key(parsed)
        self._store.update_in("goals", key, goal_lock.goal.to_dict())

    def _load_cached_blueprint(self, parsed: ParsedTheorem, goal_lock: GoalLock, verbose: bool = True) -> Blueprint | None:
        key = self._blueprint_cache_key(parsed, goal_lock)
        blueprints = self._store.get("blueprints") or {}
        data = blueprints.get(key)
        if data is None:
            return None
        try:
            bp = Blueprint.from_dict(data)
            self._log(False, f"      [cache hit] blueprint loaded from store (key={key})")
            return bp
        except Exception:
            return None

    def _save_cached_blueprint(self, parsed: ParsedTheorem, goal_lock: GoalLock, blueprint: Blueprint) -> None:
        key = self._blueprint_cache_key(parsed, goal_lock)
        self._store.update_in("blueprints", key, blueprint.to_dict())

    # ------------------------------------------------------------------
    # Parallel level computation
    # ------------------------------------------------------------------

    def _compute_parallel_levels(self, blueprint: Blueprint) -> list[list[str]]:
        """Group topo_order into parallel levels based on dependencies.

        All nodes at the same level have all their dependencies at lower levels
        and can therefore be compiled concurrently.
        """
        node_level: dict[str, int] = {}
        for node_id in blueprint.topo_order:
            node = blueprint.get_node(node_id)
            if not node.dependencies:
                node_level[node_id] = 0
            else:
                missing_deps = [dep for dep in node.dependencies if dep not in node_level]
                if missing_deps:
                    raise BlueprintError(
                        f"_compute_parallel_levels: node '{node_id}' has dependencies "
                        f"{missing_deps} that were not assigned a level. "
                        f"This indicates a topological sort failure."
                    )
                node_level[node_id] = max(
                    (node_level[dep] for dep in node.dependencies),
                    default=0,
                ) + 1

        max_level = max(node_level.values(), default=0)
        levels: list[list[str]] = [[] for _ in range(max_level + 1)]
        for node_id in blueprint.topo_order:
            levels[node_level[node_id]].append(node_id)
        return levels

    def _verify_polib_builds(self, node_id: str, verbose: bool) -> bool:
        """Compile a minimal file importing Polib to check the package still builds cleanly.

        Must actually `import Polib`: compile() goes through `lake build`, which
        rebuilds the (just-modified) Polib.lean — a save that broke Polib fails
        here and triggers rollback. (The previous version only imported
        Inventory, so this gate was vacuous and broken saves persisted until
        the end-of-run PolibValidator.)"""
        _result = self._compiler.compile(
            "import Mathlib\nimport Inventory\nimport Polib\n", f"_polib_verify_{node_id}"
        )
        if not _result.success:
            err = (_result.errors[0].raw_message[:80] if _result.errors
                   else (_result.stderr or "build failed")[:80])
            self._log(verbose, f"  [polib-broken] {node_id}: Polib.lean build failed: {err}")
            return False
        return True

    def _try_sorry_save(
        self,
        lean_code: str,
        node: "BlueprintNode",
        node_id: str,
        parsed: "ParsedTheorem",
        goal_lock: "GoalLock",
        category: str,
        verbose: bool,
        reason: str,
    ) -> "str | None":
        """Insert sorry into lean_code, try to save to Polib, verify build.

        Returns "partial" on success, None on failure.
        Used as a fallback when a compiled proof breaks the Polib build.
        """
        from agent.prover.tools.lean_compiler import CompileResult as _CR
        _dummy = _CR(
            success=False, exit_code=1, stdout="", stderr=reason,
            errors=[], warnings=[], compile_time_seconds=0.0, module_name=node_id,
        )
        _sorried = self._insert_sorry(lean_code, _dummy, node)
        _sr = self._compiler.compile(_sorried, node_id)
        if not _sr.success:
            self._log(verbose, f"  [sorry-save-err] {node_id}: sorry'd version also failed to compile")
            return None
        try:
            _sr_report = self._quality.check(parsed, goal_lock.goal, _sorried, is_main_target=node.is_main_target)
            with self._polib_lock:
                self._polib_mgr.save(node, _sorried, _sr_report, category, parsed)
                if not self._verify_polib_builds(node_id, verbose):
                    self._polib_mgr.remove(node_id)
                    self._log(verbose, f"  [sorry-save-err] {node_id}: sorry'd version also broke Polib")
                    self._invalidate_polib_content(self._polib_mgr._polib_lean)
                    return None
                self._invalidate_polib_content(self._polib_mgr._polib_lean)
            self._session.mark_partial(node_id, self._config.max_rounds_per_node, f"sorry-fallback: {reason}")
            with self._run_codes_lock:
                self._run_codes[node_id] = _sorried
            if self._flog:
                self._flog.finish_node(node_id, "partial", sorry_count=_sr_report.sorry_count)
            self._log(verbose, f"  [sorry-saved] {node_id}: saved sorry fallback to Polib (partial)")
            return "partial"
        except Exception as _se:
            self._log(verbose, f"  [sorry-save-err] {node_id}: {_se}")
            return None

    # ------------------------------------------------------------------
    # Single-node processing (safe to call from multiple threads)
    # ------------------------------------------------------------------

    # Patterns: (keywords_in_description, extra_hint_lines)
    _PROOF_PATTERNS: list[tuple[list[str], list[str]]] = [
        # Hexagon occupation lower bound — any lemma proving 3*p₆ ≥ ... via occupation
        (["hexagon", "occupation_conservation", "total_occ", "3 * (maps.p_i 6",
          "3*p_6", "p_6 ≥", "p₆", "hexagon lower bound", "hexagon count"],
         ["CRITICAL: any lemma proving a hexagon lower bound via occupation_conservation "
          "MUST declare `(hm : maps.m ≥ 6)` — without it the lemma is false "
          "(occupation_conservation forces p₃=0 for m≤3, and hexagons don't exist for m<6). "
          "Always add `(hm : maps.m ≥ 6)` to the lemma signature.",
          "FIRST: check whether `P6InequalityPart maps hM hm` / `Juc_InequalityPart maps hM hm` "
          "(both PROVED in Inventory) already give the bound — `have h := ...; linarith`.",
          "Use Finset.add_sum_erase to extract k=6 from `occupation_conservation maps hM hm`: "
          "`rw [← Finset.add_sum_erase _ _ h6mem] at hcons` where "
          "`h6mem : (6:ℕ) ∈ Finset.Ico 4 (maps.m+1) := by simp [Finset.mem_Ico]; omega`",
          "After extracting k=6: bound the non-hex sum with `quad_occ_cancellation maps hM hm` "
          "(accepted axiom — do NOT sorry it); upper bound `total_occ 6 ≤ 3*p₆` "
          "from `Juc_HexMaxOccupation maps hM hm`; combine with `linarith`.",
          "Membership of k in erased set: `Finset.mem_of_mem_erase hk` converts "
          "`hk : k ∈ (Ico 4 (m+1)).erase 6` to `k ∈ Ico 4 (m+1)` for `occupation_bound`.",
          "Final step: `linarith [EdgeCountEquation maps (by omega : maps.m ≥ 6), "
          "RemainingEdgesIdentity maps, hkey]` closes the goal."]),
        # Int.floor / ℚ division patterns
        (["floor", "⌊", "Int.floor", "⌊(k"],
         ["Key: convert Int.floor to ℕ division via `norm_cast` + "
          "`Int.floor_natCast`; use `Finset.sum_congr rfl` to rewrite pointwise",
          "Tactic: `simp only [Int.floor_natCast, Nat.cast_div]` then `omega`",
          "Lemma: Int.floor_div_ofNat — floor of ℕ/ℕ cast to ℚ equals ℕ/ℕ"]),
        # Finset.Ico split patterns
        (["Finset.Ico", "sum_Ico", "Σ", "∑"],
         ["Lemma: Finset.sum_Ico_consecutive — split Ico sum at midpoint",
          "Lemma: Finset.sum_add_distrib — `∑ (f+g) = ∑ f + ∑ g`",
          # sum_sub_distrib: forward is `∑ (f-g) = ∑ f - ∑ g`;
          # use `← Finset.sum_sub_distrib` to COMBINE two separate sums into one.
          "Lemma: Finset.sum_sub_distrib — `∑ (f-g) = ∑ f - ∑ g`; "
          "use `rw [← Finset.sum_sub_distrib]` to turn `∑ f - ∑ g` into `∑ (f-g)`",
          # After Finset.sum_singleton produces ((n : ℕ) : ℤ) / d * var,
          # norm_num alone cannot close the goal because of the variable.
          # Pattern: establish the numeric fact first, then rw or simp it away.
          "After Finset.sum_singleton with integer division: prove the constant "
          "separately — `have h : ((n : ℕ) : ℤ) / d = q := by norm_num; rw [h]` — "
          "then `ring` closes the goal"]),
        # Cast / coercion patterns
        (["cast", "ℤ", "ℚ", "norm_cast", "push_cast"],
         ["Tactic: `push_cast` to move casts inward, then `ring` or `linarith`",
          "Tactic: `norm_cast` to unify ℕ/ℤ/ℚ coercions before arithmetic"]),
    ]

    def _get_partial_dep_code(self, dep_id: str) -> str | None:
        """Return cleaned Lean code for a partial (not-yet-proved) dependency, or None."""
        output_file = self._output_root / "Output" / f"{dep_id}.lean"
        if not output_file.exists():
            return None
        code = output_file.read_text(encoding="utf-8")
        # Strip import lines — caller provides its own preamble
        lines = [l for l in code.splitlines() if not l.startswith("import ")]
        return "\n".join(lines).strip() or None

    def _inject_pattern_hints(self, node: BlueprintNode, hints: list[str]) -> list[str]:
        """Detect known-hard proof patterns and prepend working tactic hints."""
        description_lower = (node.description + " " + node.latex_fragment).lower()
        extra: list[str] = []
        for keywords, pattern_hints in self._PROOF_PATTERNS:
            if any(kw.lower() in description_lower for kw in keywords):
                extra.extend(pattern_hints)
        if extra:
            # Deduplicate and prepend pattern hints (highest priority)
            seen = set(hints)
            new_extra = [h for h in extra if h not in seen]
            return new_extra + hints
        return hints

    def _load_polib_code(self, node_id: str, category: str = "") -> str | None:
        """Extract a node's lean code from Polib.lean (proved entries) or output/Output/ (partial)."""
        polib_lean = Path(self._config.polib_path) / "Polib.lean"
        content = self._get_polib_content(polib_lean)
        if content:
            for status_label in ("proved", "partial"):
                marker = f"-- === {node_id} ({status_label})"
                if marker in content:
                    start = content.index(marker)
                    next_marker = content.find("\n-- === ", start + 1)
                    section = content[start:] if next_marker == -1 else content[start:next_marker]
                    return f"import Mathlib\nimport Inventory\n\n{section.strip()}\n"
        output_file = self._output_root / "Output" / f"{node_id}.lean"
        if output_file.exists():
            code = output_file.read_text(encoding="utf-8")
            # Reject imports-only files: stale placeholders where the proof body
            # was never written (or was written to Polib.lean which was later cleaned).
            # A valid output file must contain at least one lemma/theorem/def declaration.
            import re as _re
            _decl_re = _re.compile(
                r'^(?:private\s+|protected\s+|noncomputable\s+)*'
                r'(?:lemma|theorem|def|abbrev)\s+',
                _re.MULTILINE,
            )
            if not _decl_re.search(code):
                return None
            return code
        return None

    # ------------------------------------------------------------------
    # LLM-driven decomposition
    # ------------------------------------------------------------------

    def _llm_decide_decompose(
        self,
        lean_code: str,
        result: "CompileResult",
        node: BlueprintNode,
        hints: list[str],
    ) -> list[dict] | None:
        """Ask the LLM whether to decompose this node into sub-lemmas.

        Returns a list of sub-lemma dicts (name, statement, description,
        proof_hint) if decomposition is recommended, else None.
        """
        error_block = self._format_errors_for_prompt(result.errors, max_chars=2000)
        hints_str = "\n".join(f"  - {h}" for h in hints) or "  (none)"
        # Collect proved dependencies available in Polib so the LLM can reference them
        proved_deps: list[str] = []
        for dep_id in node.dependencies:
            entry = self._polib_search.find_by_node_id(dep_id)
            if entry and entry.status == "proved":
                proved_deps.append(dep_id)
        proved_deps_str = "\n".join(f"  - {d}" for d in proved_deps) or "  (none)"
        prompt = (
            f"A Lean 4 proof has failed to compile after several attempts.\n\n"
            f"## Node\n{node.node_id}: {node.description}\n\n"
            f"## Compilation Error\n```\n{error_block}\n```\n\n"
            f"## Current Lean 4 Source\n```lean\n{lean_code}\n```\n\n"
            f"## Proved dependencies available to call directly\n{proved_deps_str}\n\n"
            f"## Available Mathlib Lemmas\n{hints_str}\n\n"
            f"Decide: should this lemma be decomposed into smaller independent sub-lemmas "
            f"that are each easier to prove?\n\n"
            f"CRITICAL RULES for sub-lemma statements:\n"
            f"1. Each sub-lemma must be CONSISTENT with the parent lemma's hypotheses — "
            f"do NOT add hypotheses that contradict the parent (e.g. if parent has `hm : m ≥ 6`, "
            f"a sub-lemma must not have `hm : m < 6`).\n"
            f"2. Each sub-lemma must cover a REAL step in the proof that the proved dependencies "
            f"above cannot directly handle.\n"
            f"3. Sub-lemma statements must be valid Lean 4 that can compile independently.\n\n"
            f"If YES — respond with JSON listing the sub-lemmas. Each sub-lemma must be a "
            f"`private lemma` or `private def` that can be proved INDEPENDENTLY.\n\n"
            f"If NO — respond with {{\"should_decompose\": false}}.\n\n"
            f"JSON schema when decomposing:\n"
            f"{{\n"
            f'  "should_decompose": true,\n'
            f'  "reason": "one sentence",\n'
            f'  "sub_lemmas": [\n'
            f'    {{\n'
            f'      "name": "CamelCaseName",\n'
            f'      "statement": "private lemma CamelCaseName ... : ... := by\\n  sorry",\n'
            f'      "description": "what this sub-lemma proves",\n'
            f'      "proof_hint": "key tactic or approach"\n'
            f'    }}\n'
            f'  ]\n'
            f"}}\n\n"
            f"Respond ONLY with valid JSON. No prose outside the JSON."
        )
        raw = self._sdk._call(prompt, timeout=150)
        # Extract JSON from response
        raw = raw.strip()
        m = re.search(r"\{.*\}", raw, re.DOTALL)
        if not m:
            return None
        try:
            data = json.loads(m.group(0))
        except json.JSONDecodeError:
            return None
        if not data.get("should_decompose"):
            return None
        subs = data.get("sub_lemmas", [])
        if not subs or not isinstance(subs, list):
            return None
        return subs

    def _prove_sub_lemma(
        self,
        sub: dict,
        parent_node: BlueprintNode,
        hints: list[str],
        verbose: bool,
    ) -> tuple[str, str, bool]:
        """Prove one sub-lemma. Returns (name, lean_code, success)."""
        name = sub.get("name", "SubLemma")
        stmt = sub.get("statement", "")
        desc = sub.get("description", "")
        hint_extra = sub.get("proof_hint", "")

        sub_node = BlueprintNode(
            node_id=name,
            node_type="lemma",
            description=desc,
            latex_fragment=parent_node.latex_fragment,
            dependencies=[],
            is_main_target=False,
        )
        sub_hints = ([hint_extra] if hint_extra else []) + hints

        # Wrap statement in a compilable file
        code = (
            f"import Mathlib\nimport Inventory\n\n"
            f"{stmt}\n"
        )
        code = self._normalize_lean(code)

        self._log(verbose, f"    [sub-prove] {name}: {desc[:60]}")
        lean_code, ok, _ = self._compile_loop(
            code, sub_node, sub_hints, name, verbose=False,
            _allow_decompose=False,
        )
        # Sub-lemma must be truly sorry-free — Lean compiles sorry as a warning,
        # so ok=True from _compile_loop does not guarantee the proof is complete.
        if ok and (self._has_sorry(lean_code) or self._find_sorry_blocks(lean_code)):
            ok = False
        status = "ok" if ok else "FAILED"
        self._log(verbose, f"    [sub-{status}] {name}")
        return name, lean_code, ok

    def _prove_sub_lemmas_parallel(
        self,
        sub_specs: list[dict],
        parent_node: BlueprintNode,
        hints: list[str],
        verbose: bool,
    ) -> list[tuple[str, str, bool]]:
        """Prove sub-lemmas in parallel. Returns list of (name, code, success)."""
        n = len(sub_specs)
        self._log(verbose, f"  [decompose] {parent_node.node_id} → {n} sub-lemma(s):")
        for i, s in enumerate(sub_specs, 1):
            self._log(verbose, f"      [{i}/{n}] {s.get('name','?')}: {s.get('description','')[:70]}")
        self._log(verbose, f"  [sub-prove] launching {n} parallel workers...")

        results: list[tuple[str, str, bool]] = []
        with ThreadPoolExecutor(max_workers=n) as executor:
            future_to_sub = {
                executor.submit(self._prove_sub_lemma, sub, parent_node, hints, verbose): sub
                for sub in sub_specs
            }
            for future in as_completed(future_to_sub):
                try:
                    results.append(future.result())
                except Exception as exc:
                    sub = future_to_sub[future]
                    name = sub.get("name", "?")
                    self._log(verbose, f"    [sub-err] {name}: {exc}")
                    results.append((name, "", False))
        return results

    def _assemble_with_sub_lemmas(
        self,
        node: BlueprintNode,
        sub_results: list[tuple[str, str, bool]],
        hints: list[str],
        verbose: bool,
    ) -> tuple[str, bool]:
        """Generate the main lemma given proved sub-lemmas. Returns (code, success)."""
        # If every sub-lemma failed there is nothing to assemble — skip to avoid a
        # pointless (and slow) LLM call that would just produce more sorry placeholders.
        if not any(ok for _, _, ok in sub_results):
            self._log(verbose, f"  [assemble-skip] {node.node_id}: all sub-lemmas failed, skipping assembly")
            return "", False
        self._log(verbose, f"  [assemble] {node.node_id}: assembling from sub-lemmas")

        # Collect ONLY proved sub-lemma bodies (failed ones bloat the prompt with useless code)
        sub_bodies: list[str] = []
        for name, code, ok in sub_results:
            if not ok or not code:
                continue
            # Strip import lines
            body_lines = [
                l for l in code.splitlines()
                if not l.startswith("import ") and l.strip() != ""
            ]
            sub_bodies.append("\n".join(body_lines))

        proved_names = [name for name, _, ok in sub_results if ok]
        failed_names = [name for name, _, ok in sub_results if not ok]

        hints_str = "\n".join(f"  - {h}" for h in hints) or "  (none)"
        proved_str = "\n\n".join(sub_bodies) if sub_bodies else "(none proved)"
        prompt = (
            f"Complete the Lean 4 proof of the main lemma using the sub-lemmas below.\n\n"
            f"## Main Node\n{node.node_id}: {node.description}\n\n"
            f"## Proved Sub-lemmas (include these verbatim before the main lemma)\n"
            f"```lean\n{proved_str}\n```\n\n"
            + (f"## Sub-lemmas that FAILED (use sorry for these if needed)\n"
               f"{', '.join(failed_names)}\n\n" if failed_names else "")
            + f"## Available Mathlib Lemmas\n{hints_str}\n\n"
            f"Instructions:\n"
            f"- Start with `import Mathlib\\nimport Inventory`\n"
            f"- Include all proved sub-lemma code verbatim\n"
            f"- Then write the main lemma `{node.node_id}` calling the sub-lemmas\n"
            f"- Use `∑ x ∈ s, f x` notation (∈ not `in`)\n"
            f"- Return ONLY the complete Lean 4 file inside a ```lean fence."
        )
        # Assembly prompts are large (multiple sub-lemmas); use a longer timeout.
        try:
            raw = self._sdk._call(prompt, timeout=180)
        except Exception as exc:
            self._log(verbose, f"  [assemble-timeout] {node.node_id}: assembly call failed ({exc}), returning failure")
            return "", False
        code = self._normalize_lean(self._strip_markdown(raw))
        code = self._ensure_preamble(code)
        if not code.strip():
            return "", False

        result = self._compiler.compile(code, node.node_id)
        self._write_output(code, node.node_id, result.success)
        if result.success:
            self._log(verbose, f"  [assemble-ok] {node.node_id}: assembled proof compiled")
            return code, True

        # Fix loop: up to 3 rounds of targeted_fix_strict + compile
        for fix_round in range(3):
            err = (result.errors[0].raw_message[:80] if result.errors
                   else (result.stderr or "build failed")[:80])
            self._log(verbose, f"  [assemble-err] {node.node_id} fix {fix_round}: {err}")
            # Parallel: run targeted_fix and targeted_fix_strict simultaneously
            with ThreadPoolExecutor(max_workers=2) as _aex:
                _ff = _aex.submit(self._targeted_fix, code, result, node, hints, fix_round)
                _fs = _aex.submit(self._targeted_fix_strict, code, result, node, hints, fix_round)
                _fixed0, _fixed1 = _ff.result(), _fs.result()
            with ThreadPoolExecutor(max_workers=2) as _aex:
                _rr0 = _aex.submit(self._compiler.compile, _fixed0, node.node_id)
                _rr1 = _aex.submit(self._compiler.compile, _fixed1, node.node_id)
                _res0, _res1 = _rr0.result(), _rr1.result()
            self._write_output(_fixed0, node.node_id, _res0.success)
            self._write_output(_fixed1, node.node_id, _res1.success)
            if _res0.success or _res1.success:
                code = _fixed0 if _res0.success else _fixed1
                self._log(verbose, f"  [assemble-ok] {node.node_id}: fixed after {fix_round + 1} pass(es)")
                return code, True
            # Take the one with fewer errors for the next fix round
            code, result = (
                (_fixed0, _res0) if len(_res0.errors) <= len(_res1.errors)
                else (_fixed1, _res1)
            )
        return code, False

    def _compile_loop(
        self,
        lean_code: str,
        node: BlueprintNode,
        hints: list[str],
        node_id: str,
        verbose: bool,
        _allow_decompose: bool = True,
        goal_signature: str = "",
    ) -> tuple[str, bool, list]:
        """Run the compile + targeted-fix retry loop with escalation phases.

        Returns (best_lean_code, compile_ok, last_errors).
        """
        compile_ok = False
        last_errors: list = []
        active_hints = list(hints)
        detector = StagnationDetector()
        _phase1_refreshed = False
        _decompose_checked = False
        _meta_hints_generated = False  # call LLMHintGenerator at most once per node
        current_strategy = "initial_generation"
        failure_history: list[FailureRecord] = []
        # Accumulate identifiers that Lean rejected as unknown/invalid across all rounds.
        # These are injected into every fix prompt so the LLM stops re-inventing them.
        banned_ids: set[str] = set()
        # Count rounds whose primary error class is "unknown identifier / invalid field".
        # Used for cross-identifier stagnation: even if the LLM switches to a different
        # non-existent name each round, the error *class* is the same → escalate sooner.
        _unknown_id_rounds = 0
        _fix_attempt = 0  # counts fix attempts across all rounds

        for round_num in range(self._config.max_rounds_per_node):
            result = self._compiler.compile(lean_code, node_id)
            self._write_output(lean_code, node_id, result.success)
            if self._flog:
                self._flog.log_compile_round(node_id, "compile_loop", current_strategy, lean_code, result)

            if result.success:
                if not self._has_sorry(lean_code):
                    compile_ok = True
                    self._log(verbose, f"  [ok]  {node_id} compiled (round {round_num})")
                    break
                # Compiled with sorry — try mechanical tactics first, then sorry-removal fix.
                n_sorry = len(self._find_sorry_blocks(lean_code))
                self._log(verbose,
                    f"  [sorry] {node_id} round {round_num}: compiled with {n_sorry} sorry(s), attempting removal")
                mechanical = self._try_mechanical_tactics(lean_code, node_id, verbose)
                if mechanical is not None and not self._has_sorry(mechanical):
                    lean_code = mechanical
                    compile_ok = True
                    self._log(verbose, f"  [ok]  {node_id}: sorry removed by mechanical tactic")
                    break
                if round_num < self._config.max_rounds_per_node - 1:
                    _fix_attempt += 1
                    self._log(verbose, f"  [fix]  {node_id} round {round_num}, fix #{_fix_attempt}: attempting sorry removal")
                    fixed = self._targeted_fix_sorry_removal(lean_code, node, active_hints, round_num)
                    if fixed and fixed.strip() != lean_code.strip():
                        lean_code = fixed
                        current_strategy = "sorry_removal"
                        continue
                # No more rounds or fix unchanged — sorry could not be removed, node fails
                self._log(verbose, f"  [sorry-fail] {node_id}: sorry could not be removed, failing node")
                break

            last_errors = result.errors
            error_summary = (result.errors[0].raw_message[:80] if result.errors
                             else (result.stderr or "build failed")[:80])
            self._log(verbose, f"  [err] {node_id} round {round_num}: {error_summary}")

            # Collect banned identifiers from all errors in this round
            _this_round_unknown = False
            _retry_after_strip = False
            for err in result.errors:
                if err.error_class == "F":
                    raise GoalTamperedError(
                        f"Class F error in node '{node_id}': {err.raw_message}"
                    )
                # "already been declared" means a name is already in Polib.lean.
                if "has already been declared" in err.raw_message:
                    # Extract which name was already declared
                    _decl_m = re.search(r"`(\w+)` has already been declared", err.raw_message)
                    _decl_name = _decl_m.group(1) if _decl_m else None

                    if _decl_name and _decl_name != node_id:
                        # The LLM inlined a proved dependency — strip that definition and retry.
                        lean_code = self._strip_named_declaration(lean_code, _decl_name)
                        self._log(verbose,
                            f"  [strip-inline] {node_id}: removed inlined `{_decl_name}` "
                            f"(already in Polib), retrying")
                        _retry_after_strip = True
                        break  # break inner err loop, then continue outer round loop

                    # The current node itself is already declared in Polib → load it.
                    existing_code = self._load_polib_code(node_id)
                    if existing_code and not self._has_sorry(existing_code):
                        self._log(verbose,
                            f"  [already-proved] {node_id}: name exists in Polib.lean, treating as proved")
                        return existing_code, True, []
                    if existing_code:
                        # Partial already in Polib — accept it rather than cascade-failing deps.
                        self._log(verbose,
                            f"  [already-partial] {node_id}: partial in Polib, accepting existing")
                        return existing_code, True, []
                    # Name exists but code not loadable — fail (no sorry insertion)
                    self._log(verbose,
                        f"  [already-declared] {node_id}: name conflict, failing node")
                    return lean_code, False, result.errors
                # Track unknown/invalid identifiers for the banned list
                for pat in (
                    r"Unknown identifier `(\w+)`",
                    r"Invalid field `(\w+)`",
                ):
                    m = re.search(pat, err.raw_message)
                    if m:
                        banned_ids.add(m.group(1))
                        _this_round_unknown = True
            if _retry_after_strip:
                continue  # restart the round with the stripped code (don't count as a new round)
            if _this_round_unknown:
                _unknown_id_rounds += 1

            # Record this failure for the meta-hint generator.
            failure_history.append(FailureRecord(
                round_num=round_num,
                strategy=current_strategy,
                error_classes=[e.error_class for e in result.errors],
                primary_error=(result.errors[0].raw_message if result.errors
                               else (result.stderr or "build failed"))[:200],
                lean_excerpt=(result.errors[0].lean_excerpt if result.errors else ""),
                banned_ids=list(banned_ids),
            ))

            if round_num == self._config.max_rounds_per_node - 1:
                # All rounds exhausted without a sorry-free proof — fail the node
                self._log(verbose, f"  [fail] {node_id}: max rounds exhausted, no sorry-free proof found")
                break

            # Stagnation detection via hash-based counting (Fix 4 + Fix 8).
            # Normalises line/col and identifier names so the same logical error
            # hashes identically across rounds even if the LLM cycles identifiers.
            primary_hash = self._hash_primary_error(result.errors)
            is_stagnant = detector.record(primary_hash)
            detector.mark_strategy(current_strategy)

            # Cross-identifier stagnation: LLM keeps inventing non-existent names.
            if _unknown_id_rounds >= 2 and not is_stagnant:
                is_stagnant = True
                self._log(verbose,
                    f"  [id-stagnant] {node_id}: {_unknown_id_rounds} rounds with unknown "
                    f"identifier errors — banned: {sorted(banned_ids)}")

            # Stagnant after round 1 — no more fix attempts, fail the node
            if round_num >= 1 and is_stagnant:
                self._log(verbose,
                    f"  [stagnant-fail] {node_id}: stagnant at round {round_num}, failing node")
                break

            # Early decompose check: after DECOMPOSE_CHECK_AFTER failures, ask LLM
            if (
                _allow_decompose
                and not _decompose_checked
                and round_num + 1 >= self._DECOMPOSE_CHECK_AFTER
            ):
                _decompose_checked = True
                self._log(verbose,
                    f"  [decompose?] {node_id}: asking LLM after {round_num + 1} failed rounds")
                sub_specs = self._llm_decide_decompose(lean_code, result, node, active_hints)
                if sub_specs:
                    # Signal _process_node to run the decompose path
                    self._thread_local.pending_decompose = sub_specs
                    break

            if is_stagnant:
                effective_round = max(round_num, self._ESCALATION_HINT_REFRESH)
                self._log(verbose,
                    f"  [stagnant] {node_id}: hash threshold reached, "
                    f"escalating to phase {self._escalation_phase(effective_round)}")
                # Ask the meta-hint generator for a strategic pivot (once per node).
                if not _meta_hints_generated and len(failure_history) >= 2:
                    self._log(verbose, f"  [meta-hint] {node_id}: calling LLMHintGenerator")
                    meta_hints = self._llm_hint_generator.generate(
                        node, goal_signature, failure_history
                    )
                    if meta_hints:
                        active_hints = meta_hints + active_hints
                        self._log(verbose,
                            f"  [meta-hint] {node_id}: injected {len(meta_hints)} strategic hint(s)")
                    _meta_hints_generated = True
                detector.reset()
            else:
                effective_round = round_num

            phase = self._escalation_phase(effective_round)

            if phase in (0, 1):
                # Run targeted_fix and targeted_fix_strict in parallel; compile both.
                if phase == 1 and not _phase1_refreshed:
                    fresh = self._hint_generator.generate(node)
                    _lv = getattr(self, '_loogle_validator', None)
                    active_hints = _lv.filter_existing(fresh) if _lv else fresh
                    _phase1_refreshed = True
                _fix_attempt += 1
                self._log(verbose, f"  [fix]  {node_id} round {round_num}, fix #{_fix_attempt}: trying targeted_fix + targeted_fix_strict in parallel")
                with ThreadPoolExecutor(max_workers=2) as _pex:
                    _f0 = _pex.submit(self._targeted_fix, lean_code, result, node, active_hints, round_num, banned_ids)
                    _f1 = _pex.submit(self._targeted_fix_strict, lean_code, result, node, active_hints, round_num, banned_ids)
                    _c0, _c1 = _f0.result(), _f1.result()
                with ThreadPoolExecutor(max_workers=2) as _pex:
                    _r0 = _pex.submit(self._compiler.compile, _c0, node_id)
                    _r1 = _pex.submit(self._compiler.compile, _c1, node_id)
                    _res0, _res1 = _r0.result(), _r1.result()
                self._write_output(_c0, node_id, _res0.success)
                self._write_output(_c1, node_id, _res1.success)
                if _res0.success or _res1.success:
                    _best_code = _c0 if _res0.success else _c1
                    _winner = "targeted_fix_parallel" if _res0.success else "targeted_fix_strict_parallel"
                    if not self._has_sorry(_best_code):
                        lean_code = _best_code
                        compile_ok = True
                        self._log(verbose, f"  [ok]  {node_id} compiled via parallel fix ({_winner}, round {round_num}, fix #{_fix_attempt})")
                        if self._flog:
                            self._flog.log_compile_round(node_id, "compile_loop", _winner, lean_code,
                                                         _res0 if _res0.success else _res1)
                        break
                    # Parallel fix succeeded but still has sorry — treat as needing removal
                    lean_code = _best_code
                    current_strategy = _winner
                # Neither succeeded — use the one with fewer errors for the next round
                fixed, next_strategy = (
                    (_c0, "targeted_fix_parallel") if len(_res0.errors) <= len(_res1.errors)
                    else (_c1, "targeted_fix_strict_parallel")
                )
            elif phase == 2:
                _fix_attempt += 1
                self._log(verbose, f"  [escalate] {node_id}: decomposing into sub-steps (round {round_num}, fix #{_fix_attempt})")
                fixed = self._targeted_fix_decompose(lean_code, result, node, active_hints, round_num, banned_ids)
                next_strategy = "targeted_fix_decompose"
            else:
                # phase 3: try mechanical tactics; if they fail, fail the node (no sorry)
                mechanical = self._try_mechanical_tactics(lean_code, node_id, verbose)
                if mechanical is not None and not self._has_sorry(mechanical):
                    lean_code = mechanical
                    current_strategy = "mechanical_tactic"
                    continue
                self._log(verbose, f"  [fail] {node_id}: phase3 exhausted, no sorry-free proof found")
                break

            if fixed and fixed.strip() != lean_code.strip():
                lean_code = fixed
                current_strategy = next_strategy
            else:
                self._log(verbose, f"  [fix-skip] {node_id} round {round_num}: no change from Claude, failing node")
                break

        # Expose banned_ids so _process_node can use them in the structure-augment fallback
        self._thread_local.last_banned_ids = banned_ids
        return lean_code, compile_ok, last_errors

    def _process_node(
        self,
        node_id: str,
        blueprint: Blueprint,
        goal_lock: GoalLock,
        parsed: ParsedTheorem,
        category: str,
        proven_node_ids: list[str],
        verbose: bool,
        proven_dep_imports: dict[str, str] | None = None,
    ) -> str:
        """Process one blueprint node. Returns 'proved' | 'partial' | 'pending'.

        All nodes (new or partial) go through _partial_solver, which handles
        sorry elimination and fresh generation in a unified way.
        Proved nodes are skipped immediately.
        """
        node = blueprint.get_node(node_id)

        # Skip fully proved nodes — only if code can actually be recovered.
        # If session says "done" but code is missing from Polib.lean (stale
        # session state), fall through and re-prove rather than returning
        # "proved" with no code, which causes "code missing" in assembly.
        if self._session.is_done(node_id):
            self._log(verbose, f"  [skip] {node_id} (proved)")
            code = self._load_polib_code(node_id)
            if not code:
                # Exact name not in Polib.lean; recover via fuzzy polib search
                fallback = self._polib_search.search(node, parsed)
                if fallback and fallback.status == "proved":
                    code = self._load_polib_code(fallback.node_id)
                    if code:
                        self._log(verbose, f"  [skip-recover] {node_id} code recovered via {fallback.node_id}")
            if code:
                _skip_report = self._quality.check(parsed, goal_lock.goal, code, is_main_target=node.is_main_target)
                with self._run_codes_lock:
                    self._run_codes[node_id] = code
                    self._run_quality_reports[node_id] = _skip_report
                    self._run_skipped_nodes.add(node_id)
                return "proved"
            # Code not found despite session saying proved — stale state.
            # Clear it and fall through to re-prove.
            self._log(verbose, f"  [skip-stale] {node_id} session proved but code missing — re-proving")
            self._session.mark_pending(node_id, 0, "stale session: code missing from polib")


        # Exact-name polib lookup: handles stale session state where is_done()
        # returns False but the node was proved in a previous run. This catches
        # the "has already been declared" failure mode where Polib.lean already
        # contains the definition but the session wasn't updated.
        _polib_exact = self._polib_search.find_by_node_id(node_id)
        if _polib_exact:
            code = self._load_polib_code(node_id)
            if _polib_exact.status == "proved" and code and not self._has_sorry(code):
                self._log(verbose, f"  [skip] {node_id} (proved in polib, session stale)")
                self._session.mark_done(node_id, "proved")
                _skip_report = self._quality.check(parsed, goal_lock.goal, code, is_main_target=node.is_main_target)
                with self._run_codes_lock:
                    self._run_codes[node_id] = code
                    self._run_quality_reports[node_id] = _skip_report
                    self._run_skipped_nodes.add(node_id)
                return "proved"
            elif _polib_exact.status == "partial" and code:
                self._log(verbose, f"  [skip] {node_id} (partial in polib, session stale)")
                self._session.mark_partial(node_id, 0, "recovered from polib")
                _skip_report = self._quality.check(parsed, goal_lock.goal, code, is_main_target=node.is_main_target)
                with self._run_codes_lock:
                    self._run_codes[node_id] = code
                    self._run_quality_reports[node_id] = _skip_report
                    self._run_skipped_nodes.add(node_id)
                return "partial"

        # Guard: all declared dependencies must be proved/partial
        failed_deps = [d for d in node.dependencies if d not in proven_node_ids]
        if failed_deps:
            reason = f"unresolved deps: {failed_deps}"
            self._log(verbose, f"  [dep-fail] {node_id} — {reason}")
            self._session.mark_pending(node_id, 0, reason)
            return "pending"

        # Polib search: accept proved (sorry-free) or partial hits
        existing = self._polib_search.find_by_node_id(node_id) or self._polib_search.search(node, parsed)
        if existing:
            code = self._load_polib_code(existing.node_id)
            if existing.status == "proved" and code and not self._has_sorry(code):
                self._log(verbose, f"  [found] {node_id} in polib (proved)")
                self._session.mark_done(node_id, "proved")
                _skip_report = self._quality.check(parsed, goal_lock.goal, code, is_main_target=node.is_main_target)
                with self._run_codes_lock:
                    self._run_codes[node_id] = code
                    self._run_quality_reports[node_id] = _skip_report
                    self._run_skipped_nodes.add(node_id)
                return "proved"
            elif existing.status == "partial" and code:
                self._log(verbose, f"  [found] {node_id} in polib (partial)")
                self._session.mark_partial(node_id, 0, "recovered from polib")
                _skip_report = self._quality.check(parsed, goal_lock.goal, code, is_main_target=node.is_main_target)
                with self._run_codes_lock:
                    self._run_codes[node_id] = code
                    self._run_quality_reports[node_id] = _skip_report
                    self._run_skipped_nodes.add(node_id)
                return "partial"
            elif existing.status == "proved":
                self._log(verbose, f"  [found] {node_id} matched polib but code has sorry — will re-prove")

        if self._flog:
            self._flog.start_node(node_id, node.node_type, node.description)

        # Fire reasoning_hint speculatively in a background thread so it overlaps
        # with the CombinedHintGenerator.  If >= 3 hints come back we discard
        # the result; otherwise it is already done (or nearly) when needed.
        goal_sig = goal_lock.goal.lean_signature if goal_lock and goal_lock.goal else ""
        _reason_ex = ThreadPoolExecutor(max_workers=1)
        fut_reasoning = _reason_ex.submit(self._reasoning_hint_generator.generate, node, goal_sig)

        # CombinedHintGenerator: one Haiku call + all Loogle queries in parallel.
        # All returned names come directly from Loogle so no post-validation needed.
        hints = self._hint_generator.generate(node)

        self._log(verbose, f"  [hints] {node_id}: {len(hints)} (combined, verified)")

        # Use the speculatively computed proof sketch when hints are still sparse.
        if len(hints) < 3:
            self._log(verbose,
                f"  [reasoning-hint] {node_id}: only {len(hints)} hint(s), "
                f"using pre-computed LLM proof sketch")
            sketch_hints = fut_reasoning.result()
            _reason_ex.shutdown(wait=False)
            if sketch_hints:
                hints = hints + sketch_hints
                self._log(verbose, f"  [reasoning-hint] {node_id}: proof sketch added")
        else:
            fut_reasoning.cancel()
            _reason_ex.shutdown(wait=False)

        # For partial nodes: ask the LLM whether current hints are sufficient to
        # complete the proof.  Skip and reuse the existing sorry-code if not.
        existing_code: str | None = None
        if self._session.is_partial(node_id):
            existing_code = self._load_polib_code(node_id, category)
            if existing_code:
                feasible, assess_sketch = self._reasoning_hint_generator.assess_and_sketch_partial(
                    node, existing_code, hints, goal_sig
                )
                if not feasible:
                    self._log(verbose, f"  [skip] {node_id} (partial — LLM assessed infeasible)")
                    with self._run_codes_lock:
                        self._run_codes[node_id] = existing_code
                    return "partial"
                # Feasible: prepend the completion sketch so the retry model sees it
                if assess_sketch:
                    hints = assess_sketch + hints
                self._log(verbose, f"  [partial-assess] {node_id}: LLM assessed feasible, retrying")

        mode = "retry-partial" if self._session.is_partial(node_id) else "gen"
        self._log(verbose,
            f"  [{mode}] {node_id} — {len(hints)} hints (validated)")

        hints = self._inject_pattern_hints(node, hints)

        # For retry-partial: if the node already has a section in Polib.lean,
        # remove it before the compile attempt.  Without this, the temp file
        # does `import Inventory` + redefines the lemma → "has already been
        # declared" on round 0, so no LLM-generated code ever gets tested.
        # Save a backup so we can restore if the retry completely fails (keeps
        # the node as partial for downstream dependency resolution).
        _partial_backup: str | None = None
        if existing_code is not None and self._polib_mgr._polib_lean.exists():
            _pc = self._get_polib_content(self._polib_mgr._polib_lean)
            if f"\n-- === {node_id} " in _pc:
                _partial_backup = existing_code
                with self._polib_lock:
                    self._polib_mgr.remove(node_id)
                    self._invalidate_polib_content(self._polib_mgr._polib_lean)
                self._log(verbose,
                    f"  [pre-remove] {node_id}: removed old partial from Polib before retry")

        # Load cross-run failure history so the LLM can avoid repeating past mistakes
        cross_run_errors = self._session.get_cross_run_errors(node_id) or None

        self._thread_local.pending_decompose = None
        try:
            lean_code, compile_ok, last_errors = self._partial_solver(
                node, goal_lock, hints, proven_node_ids, proven_dep_imports,
                category, node_id, verbose, existing_code,
                cross_run_errors=cross_run_errors,
            )
        except GoalTamperedError:
            raise  # always propagate goal-tamper errors
        except Exception as _solver_exc:
            # Any unexpected exception (API timeout, network error, etc.) — fail the node.
            self._log(verbose, f"  [solver-exc] {node_id}: {_solver_exc}")
            self._session.mark_pending(node_id, 0, str(_solver_exc))
            if self._flog:
                self._flog.finish_node(node_id, "failed", sorry_count=0)
            return "pending"

        # ── Decompose path: LLM decided to split into sub-lemmas ──────
        if not compile_ok and getattr(self._thread_local, 'pending_decompose', None):
            sub_specs = self._thread_local.pending_decompose
            self._thread_local.pending_decompose = None
            sub_results = self._prove_sub_lemmas_parallel(sub_specs, node, hints, verbose)
            assembled_code, assemble_ok = self._assemble_with_sub_lemmas(node, sub_results, hints, verbose)
            if assemble_ok:
                lean_code = assembled_code
                compile_ok = True
                last_errors = []
            elif assembled_code and assembled_code.strip():
                # Assembly failed to compile — node fails (no sorry insertion)
                self._log(verbose, f"  [assemble-fail] {node_id}: assembled code failed to compile, failing node")

        # ── Phase 4: quality check + save ─────────────────────────────
        report = self._quality.check(
            parsed, goal_lock.goal, lean_code, is_main_target=node.is_main_target
        )
        with self._run_codes_lock:
            self._run_quality_reports[node_id] = report
        # Reject imports-only files: an empty body compiles with 0 sorrys but
        # contains no actual proof — accepting it would mark the node as proved
        # with no code (the false-positive that burned P6GenusG).
        _has_target_decl = bool(re.search(
            r'^(?:private\s+|protected\s+|noncomputable\s+)*'
            r'(?:lemma|theorem|def|abbrev)\s+' + re.escape(node_id),
            lean_code, re.MULTILINE,
        ))
        sorry_free = compile_ok and report.sorry_count == 0 and _has_target_decl and report.passed

        # Reject trivially-degenerate proofs: a declaration whose return type is
        # bare `True`, `False`, or `Prop` proves nothing about the conjecture.
        # This catches the failure mode where the LLM falls back to `lemma X : True`.
        _trivial_type = bool(re.search(
            r'(?:lemma|theorem)\s+\S[^:]*:\s*(?:True|False|Prop)\s*(?::=|where)',
            lean_code,
        ))
        if _trivial_type and node.is_main_target:
            # If this trivial sorry is already saved in Polib from a previous run
            # (e.g. from an earlier nuclear-sorry), accept it as partial rather than
            # failing: any new compile would hit "already been declared" anyway.
            # Use _load_polib_code rather than polib_search since the entry may not
            # be in the index (polib_index only covers indexed saves, not all sections).
            _existing_in_polib = self._load_polib_code(node_id)
            if _existing_in_polib:
                self._log(verbose,
                    f"  [trivial-type-partial] {node_id}: trivial type already in Polib — "
                    f"accepting existing as partial")
                self._session.mark_partial(
                    node_id, self._config.max_rounds_per_node, "trivial type, already in Polib")
                with self._run_codes_lock:
                    self._run_codes[node_id] = lean_code
                if self._flog:
                    self._flog.finish_node(node_id, "partial", sorry_count=report.sorry_count)
                return "partial"
            self._log(verbose,
                f"  [trivial-type] {node_id}: main target has degenerate return type "
                f"(True/False/Prop) — treating as failed")
            compile_ok = False
            sorry_free = False

        # If the node is already present in Polib (e.g. an [already-proved] path loaded
        # existing code), skip the duplicate save — re-saving would cause a
        # "has already been declared" build failure and roll back to [fail].
        if sorry_free and compile_ok:
            _pc_now = self._get_polib_content(self._polib_mgr._polib_lean)
            if f"\n-- === {node_id} " in _pc_now:
                self._log(verbose, f"  [already-in-polib] {node_id}: skipping duplicate save")
                self._session.mark_done(node_id, "proved")
                with self._run_codes_lock:
                    self._run_codes[node_id] = lean_code
                if self._flog:
                    self._flog.finish_node(node_id, "proved", sorry_count=0)
                return "proved"

        if sorry_free:
            try:
                with self._polib_lock:
                    entry = self._polib_mgr.save(node, lean_code, report, category, parsed)
                    # Verify inside the lock: no other thread can modify Polib between
                    # save and verify, so a build failure is unambiguously caused by
                    # this entry and not by a concurrent write.
                    if not self._verify_polib_builds(node_id, verbose):
                        self._polib_mgr.remove(node_id)
                        self._invalidate_polib_content(self._polib_mgr._polib_lean)
                        raise PolibSaveError(f"Node '{node_id}': entry broke Polib.lean build, rolled back")
                    self._invalidate_polib_content(self._polib_mgr._polib_lean)
                with self._save_lock:
                    self._dep_graph.record_edges(entry.node_id, lean_code, parsed)
                    self._dep_graph.save()
                self._session.mark_done(node_id, entry.status)
                try:
                    from visualizer.generate import generate_explorer
                    generate_explorer(
                        Path(self._config.store_path),
                        Path(self._config.polib_path) / "proof_explorer.html",
                    )
                except Exception:
                    pass
                self._log(verbose, f"  [saved] {node_id} → polib ({entry.status})")
                with self._run_codes_lock:
                    self._run_codes[node_id] = lean_code
                if self._flog:
                    self._flog.finish_node(node_id, entry.status, sorry_count=0)
                return entry.status
            except PolibSaveError as exc:
                self._log(verbose, f"  [save-err] {node_id}: {exc} — failing node")
                self._session.mark_pending(node_id, self._config.max_rounds_per_node, str(exc))
                if self._flog:
                    self._flog.finish_node(node_id, "failed", sorry_count=report.sorry_count)
                return "pending"

        elif compile_ok and report.sorry_count > 0:
            # Code compiled but still has sorry — reject as failure (no new sorry accepted)
            last_err_msg = f"compiled with {report.sorry_count} sorry(s) — sorry not accepted"
            self._log(verbose, f"  [sorry-reject] {node_id} — {report.sorry_count} sorry(s), failing node")
            self._session.mark_pending(node_id, self._config.max_rounds_per_node, last_err_msg, failed_code=lean_code)
            if self._flog:
                self._flog.finish_node(node_id, "failed", sorry_count=report.sorry_count)
            return "pending"

        else:
            last_err_msg = last_errors[0].raw_message[:120] if last_errors else "compile failed"
            self._session.mark_pending(node_id, self._config.max_rounds_per_node, last_err_msg, failed_code=lean_code)
            self._log(verbose, f"  [fail] {node_id} — saved to output/ for inspection")
            if self._flog:
                self._flog.finish_node(node_id, "failed", sorry_count=report.sorry_count)
            return "pending"

    # ------------------------------------------------------------------
    # Complete proof file assembly
    # ------------------------------------------------------------------

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
            for line in self._get_polib_content(polib_lean).splitlines():
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
                if not node_code or not self._has_sorry(node_code):
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

    # ------------------------------------------------------------------
    # Main pipeline
    # ------------------------------------------------------------------

    def formalize(
        self,
        latex_source: str,
        category: str = "Polytope",
        verbose: bool = True,
        tex_path: str | None = None,
        parsed: "ParsedTheorem | None" = None,
    ) -> FormalizationResult:

        polib_path = Path(self._config.polib_path)
        store_path_str = str(self._config.store_path)
        dep_graph_path = store_path_str
        session_state_path = store_path_str

        nodes_proved: list[str] = []
        nodes_partial: list[str] = []
        nodes_failed: list[str] = []
        parsed: ParsedTheorem | None = None  # initialised before try so except can reference it

        # Reset per-run code collection
        with self._run_codes_lock:
            self._run_codes.clear()
            self._run_quality_reports.clear()
            self._run_skipped_nodes.clear()

        # Initialise per-run formalization logger
        import uuid as _uuid
        run_id = datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%S") + f"_{_uuid.uuid4().hex[:6]}"
        log_dir = polib_path.parent / "logs"
        self._flog = FormalizationLogger(log_dir, run_id, theorem_name="(pending)")

        try:
            # ── Step 1: Parse ──────────────────────────────────────────
            self._log(verbose, "[1/8] Parsing conjecture...")
            if parsed is None:
                parsed = self._parser.parse_with_llm(latex_source, self._sdk_fast, self._config.model_fast)
            self._log(verbose, f"      theorem: {parsed.name} ({len(parsed.proof_steps)} steps)")
            self._flog._data["theorem_name"] = parsed.name  # update now that we know the name
            self._flog._flush()

            # ── Step 2: Lock goal (cached) ─────────────────────────────
            self._log(verbose, "[2/8] Extracting & locking goal...")
            goal_lock = self._load_cached_goal(parsed, verbose=verbose) or GoalLock.create(
                parsed, self._extractor, self._validator, max_attempts=3
            )
            # Reject any goal whose signature uses undefined simplicity predicates or
            # wrong f_2 translation — they would fail every Lean compile.
            _bad_sig_patterns = [
                "IsSimple", "maps.simple", "maps.is_simple", "simple maps",
                "maps.f2 ", "maps.f_2 ", "maps.f2\n", "maps.f_2\n",
            ]
            import re as _re
            import re as _re2
            _sig = goal_lock.goal.lean_signature
            _has_bad = any(p in _sig for p in _bad_sig_patterns)
            # Reject goals whose conclusion is trivially True or False — the LLM
            # sometimes emits these when it cannot formalize the actual statement.
            if not _has_bad and _re2.search(r':\s*(?:True|False|Prop)\s*:=\s*by\s*$', _sig.strip()):
                _has_bad = True
            # Also catch maps.p_i 2 used as the f_2 hypothesis (comparison against int)
            if not _has_bad and _re.search(r'maps\.p_i 2\s*[≥≤><=]', _sig):
                _has_bad = True
            if _has_bad:
                self._log(verbose,
                    f"  [goal-reject] Signature uses undefined predicate or wrong f_2 — "
                    f"discarding cache and re-extracting."
                )
                goal_lock = GoalLock.create(parsed, self._extractor, self._validator, max_attempts=3)
            self._save_cached_goal(parsed, goal_lock)

            # Warn prominently if the goal signature was not confirmed by the validator
            if not goal_lock.goal.validator_confirmed:
                self._log(True,
                    f"\n  *** WARNING: Goal signature was NOT confirmed by the validator. ***\n"
                    f"  *** Proceeding with best-effort signature: ***\n"
                    f"  *** {goal_lock.goal.lean_signature[:100]} ***\n"
                    f"  *** Notes: {goal_lock.goal.validator_notes} ***\n"
                )

            self._log(verbose, f"      signature: {goal_lock.goal.lean_signature[:80]}...")

            # ── Step 3: Blueprint (cached) ─────────────────────────────
            self._log(verbose, "[3/8] Decomposing blueprint...")
            _proved_lemmas = [
                {
                    "node_id": e["node_id"],
                    "description": (
                        e.get("description", "")
                        + (" [partial — has sorry, use for structural reference only]"
                           if e.get("status") == "partial" else "")
                    ),
                }
                for e in (self._store.get("polib_index") or [])
                if isinstance(e, dict) and e.get("status") in ("proved", "partial")
            ]
            blueprint = self._load_cached_blueprint(parsed, goal_lock, verbose=verbose) or \
                self._decomposer.decompose(parsed, goal_lock.goal, proved_lemmas=_proved_lemmas)
            self._save_cached_blueprint(parsed, goal_lock, blueprint)
            self._log(verbose, f"      nodes: {[n.node_id for n in blueprint.nodes]}")
            self._log(verbose, f"      topo order: {blueprint.topo_order}")

            # ── Step 4: Per-node loop (parallel by dependency level) ───
            self._log(verbose, "[4/8] Formalizing nodes...")
            levels = self._compute_parallel_levels(blueprint)
            proven_node_ids: list[str] = []
            # Maps node_id → Lean import path for nodes saved to polib this session
            proven_dep_imports: dict[str, str] = {}

            for level_idx, level_nodes in enumerate(levels):
                if len(level_nodes) == 1:
                    # Single node — run directly, no thread overhead
                    node_id = level_nodes[0]
                    status = self._process_node(
                        node_id, blueprint, goal_lock, parsed,
                        category, list(proven_node_ids), verbose,
                        proven_dep_imports=dict(proven_dep_imports),
                    )
                    if status in ("proved", "partial"):
                        proven_node_ids.append(node_id)
                        proven_dep_imports[node_id] = "Polib"
                else:
                    # Multiple independent nodes — run in parallel
                    workers = min(len(level_nodes), self._config.max_parallel_nodes)
                    self._log(verbose, f"  [level {level_idx}] parallelizing {level_nodes} ({workers} workers)")
                    snapshot_ids = list(proven_node_ids)
                    snapshot_imports = dict(proven_dep_imports)
                    level_results: dict[str, str] = {}

                    with ThreadPoolExecutor(max_workers=workers) as executor:
                        future_to_node = {
                            executor.submit(
                                self._process_node,
                                nid, blueprint, goal_lock, parsed,
                                category, snapshot_ids, verbose,
                                snapshot_imports,
                            ): nid
                            for nid in level_nodes
                        }
                        for future in as_completed(future_to_node):
                            nid = future_to_node[future]
                            try:
                                level_results[nid] = future.result()
                            except GoalTamperedError:
                                raise
                            except Exception as exc:
                                self._log(verbose, f"  [thread-err] {nid}: {exc}")
                                level_results[nid] = "pending"

                    # Add proved/partial nodes to proven list in topo order
                    for nid in level_nodes:
                        res = level_results.get(nid)
                        if res in ("proved", "partial"):
                            proven_node_ids.append(nid)
                            proven_dep_imports[nid] = "Polib"

            # ── Step 5: Inline retry loop for failed nodes ─────────────
            # Instead of restarting the whole pipeline N times (which redoes
            # parse/goal/blueprint each time), we keep retrying just the failed
            # nodes here. Each retry feeds the cross-run failure memory + the
            # newly-available dep signatures back into the generation prompt.
            def _collect_failed() -> list[str]:
                _nodes = self._session.data.get("nodes", {})
                return [
                    nid for nid in blueprint.topo_order
                    if _nodes.get(nid, {}).get("status") not in ("proved", "partial")
                ]

            failed_now = _collect_failed()
            if failed_now:
                self._log(verbose, "\n[5/8] Retrying failed nodes...")
                MAX_RETRY_ITERS = 20
                max_node_retries = self._config.max_node_retries
                retry_counts: dict[str, int] = {}
                consecutive_no_progress = 0
                iter_count = 0
                while failed_now and iter_count < MAX_RETRY_ITERS:
                    iter_count += 1
                    any_progress = False
                    attempted_any = False
                    still_failing = set(failed_now)
                    for nid in failed_now:
                        # Don't burn a Claude call + lake build on a node whose
                        # direct deps are still failing — it is near-certain to fail.
                        blocked = [d for d in blueprint.get_node(nid).dependencies
                                   if d in still_failing]
                        if blocked:
                            self._log(verbose,
                                f"  [{nid}] skipped — waiting on failed dep(s): {blocked}")
                            continue
                        if retry_counts.get(nid, 0) >= max_node_retries:
                            self._log(verbose,
                                f"  [{nid}] retry budget exhausted ({max_node_retries})")
                            continue
                        retry_counts[nid] = retry_counts.get(nid, 0) + 1
                        attempted_any = True
                        node_data = self._session.data.get("nodes", {}).get(nid, {})
                        last_err = (node_data.get("last_error") or "(unknown)").strip()
                        last_err_line = last_err.splitlines()[0][:140] if last_err else "(unknown)"
                        self._log(verbose,
                            f"  [{nid}] previous failure: {last_err_line}")
                        self._log(verbose,
                            f"  [{nid}] retry {retry_counts[nid]}/{max_node_retries}: regenerate with updated dep signatures + cross-run failure memory")
                        try:
                            status = self._process_node(
                                nid, blueprint, goal_lock, parsed,
                                category, list(proven_node_ids), verbose=False,
                                proven_dep_imports=dict(proven_dep_imports),
                            )
                        except GoalTamperedError:
                            raise
                        except Exception as exc:
                            self._log(verbose, f"  [{nid}] retry crashed: {exc}")
                            status = "pending"

                        if status in ("proved", "partial"):
                            self._log(verbose, f"  [{nid}] retry successfully → {status}")
                            still_failing.discard(nid)
                            if nid not in proven_node_ids:
                                proven_node_ids.append(nid)
                                proven_dep_imports[nid] = "Polib"
                            any_progress = True
                        else:
                            self._log(verbose, f"  [{nid}] still failing")

                    failed_now = _collect_failed()
                    if not attempted_any:
                        self._log(verbose,
                            f"  [retry-exhausted] remaining nodes are blocked or out of retry budget; stopping")
                        break
                    if not any_progress:
                        consecutive_no_progress += 1
                        if consecutive_no_progress >= 2:
                            self._log(verbose,
                                f"  [retry-stall] no progress for 2 consecutive iterations; stopping")
                            break
                    else:
                        consecutive_no_progress = 0
                if not failed_now:
                    self._log(verbose, f"  [retrying] all nodes resolved after {iter_count} iteration(s)")

        except GoalTamperedError as exc:
            if self._flog:
                self._flog.finish_run()
            return FormalizationResult(
                theorem_name=parsed.name if parsed is not None else "Unknown",
                status="failed",
                nodes_proved=nodes_proved,
                nodes_partial=nodes_partial,
                nodes_failed=nodes_failed,
                total_sorry_count=self._sorry_get(),
                error=f"GoalTamperedError: {exc}",
                dep_graph_path=dep_graph_path,
                session_state_path=session_state_path,
            )
        except Exception as exc:
            import traceback
            if self._flog:
                self._flog.finish_run()
            # Collect partial session results even on crash so nodes_proved/partial/failed are populated
            try:
                if blueprint is not None:
                    _session_nodes = self._session.data.get("nodes", {})
                    for _nid in blueprint.topo_order:
                        _nd = _session_nodes.get(_nid, {})
                        _st = _nd.get("status")
                        if _st == "proved" and _nid not in nodes_proved:
                            nodes_proved.append(_nid)
                        elif _st == "partial" and _nid not in nodes_partial:
                            nodes_partial.append(_nid)
                        elif _st not in ("proved", "partial") and _nid not in nodes_failed:
                            nodes_failed.append(_nid)
            except Exception:
                pass
            return FormalizationResult(
                theorem_name=parsed.name if parsed is not None else "Unknown",
                status="failed",
                nodes_proved=nodes_proved,
                nodes_partial=nodes_partial,
                nodes_failed=nodes_failed,
                total_sorry_count=self._sorry_get(),
                error=f"{type(exc).__name__}: {exc}\n{traceback.format_exc()}",
                dep_graph_path=dep_graph_path,
                session_state_path=session_state_path,
            )

        # ── Step 6: Quality check summary ─────────────────────────────
        self._log(verbose, "[6/8] Checking formalization quality...")
        with self._run_codes_lock:
            _qr_snapshot = dict(self._run_quality_reports)
            _skipped_snapshot = set(self._run_skipped_nodes)
        for _qr_node_id in blueprint.topo_order:
            _qr = _qr_snapshot.get(_qr_node_id)
            if _qr is None:
                self._log(verbose, f"  [{_qr_node_id}] — not reached (dependency failed)")
                continue
            _tag = "PASS" if _qr.passed else "FAIL"
            if _qr_node_id in _skipped_snapshot:
                self._log(verbose, f"  [{_qr_node_id}] Retrying... (loaded from Polib)")
            self._log(verbose, f"    Quality: {_tag} (score={_qr.score:.2f})")
            for _finding in _qr.findings:
                self._log(verbose, f"    • {_finding}")

        # ── Step 7: Validate and repair Polib integrity ────────────────
        from agent.prover.tools.polib_validator import PolibValidator
        self._log(verbose, "[7/8] Validating Polib...")
        _val = PolibValidator(
            polib_lean=self._polib_mgr._polib_lean,
            workspace=Path(self._config.polib_path),
            log_fn=lambda msg: self._log(verbose, msg),
        )
        _val_result = _val.validate_and_repair()
        # All node IDs removed from Polib (for any reason) must be downgraded
        # in session state so Step 8 classifies them as failed, not proved/partial.
        for _nid in _val_result.all_removed:
            self._session.mark_pending(
                _nid, 0,
                "Polib validator removed broken section — re-run to re-prove",
            )

        # ── Step 8: Collect results + save ─────────────────────────────
        all_session_nodes = self._session.data.get("nodes", {})
        for node_id in blueprint.topo_order:
            node_data = all_session_nodes.get(node_id, {})
            status = node_data.get("status")
            if status == "proved":
                nodes_proved.append(node_id)
            elif status == "partial":
                nodes_partial.append(node_id)
            else:
                nodes_failed.append(node_id)

        if self._flog:
            self._flog.finish_run()

        sorry_total = self._sorry_get()

        if tex_path:
            lean_out_path, _, _ = self._write_complete_proof_file(
                tex_path,
                parsed.name if parsed is not None else "(unknown)",
                nodes_proved, nodes_partial, nodes_failed, sorry_total,
            )
            self._log(verbose, f"[8/8] Formalization saved → {lean_out_path}")

        if nodes_failed and not (nodes_proved or nodes_partial):
            _status = "failed"
        elif nodes_failed:
            # Some nodes proved/partial — call it partial, not a total failure.
            _status = "partial"
        elif nodes_partial:
            _status = "partial"
        else:
            _status = "success"

        return FormalizationResult(
            theorem_name=parsed.name,
            status=_status,
            nodes_proved=nodes_proved,
            nodes_partial=nodes_partial,
            nodes_failed=nodes_failed,
            total_sorry_count=sorry_total,
            error=None,
            dep_graph_path=dep_graph_path,
            session_state_path=session_state_path,
        )
from typing import TYPE_CHECKING
from agent.prover.tools.blueprint import (
    _parse_blueprint_json,
    _topological_sort,
    _validate_blueprint_nodes,
)
from agent.orchestrator.tools.conjecture_parser import ConjectureParser, ParsedConjecture

if TYPE_CHECKING:
    pass

# ---------------------------------------------------------------------------
# Signature extraction + relevance ranking helpers
# ---------------------------------------------------------------------------

_SIG_DECL_START = re.compile(
    r"^(?:private\s+)?(?:lemma|theorem|def|abbrev)\s+(\w+)",
    re.MULTILINE,
)


def _extract_lean_signatures(polib_lean: Path) -> dict[str, str]:
    """Return {node_id: signature_text} by scanning Polib.lean.

    Extracts only the type signature (the part before ':= by' or ':='),
    capped at 200 chars so the prompt stays readable.
    """
    try:
        text = polib_lean.read_text(encoding="utf-8")
    except OSError:
        return {}
    sigs: dict[str, str] = {}
    lines = text.splitlines()
    i = 0
    while i < len(lines):
        m = _SIG_DECL_START.match(lines[i])
        if m:
            name = m.group(1)
            collected: list[str] = []
            done = False
            for j in range(i, min(i + 6, len(lines))):
                line = lines[j]
                # Check for ':= by' first (proof tactic block)
                if ":= by" in line:
                    collected.append(line.split(":= by")[0])
                    done = True
                    break
                # Check for ':=' with something after it on the same line (inline body)
                if re.search(r":=\s*\S", line):
                    collected.append(re.split(r":=\s*\S", line)[0] + ":=")
                    done = True
                    break
                collected.append(line)
                # ':=' at end of line means body is on the next line — stop here
                if re.search(r":=\s*$", line):
                    done = True
                    break
            sigs[name] = " ".join(collected).strip()[:200]
            _ = done  # just consumed
        i += 1
    return sigs


def _camel_tokens(s: str) -> set[str]:
    """Split a CamelCase/underscore identifier into lowercase word tokens."""
    return {w.lower() for w in re.findall(r"[A-Z][a-z]+|[a-z]+|[0-9]+", s)}


_RANK_STOP = frozenset(
    {"maps", "the", "a", "an", "and", "or", "in", "of", "for", "is", "to",
     "with", "all", "let", "if", "then", "be", "by", "on", "at", "from"}
)


def _rank_lemmas_for_discovery(
    proved_lemmas: list[dict],
    theorem_name: str,
    hypotheses: list[str],
    conclusion: str,
    top_k: int = 12,
) -> tuple[list[dict], list[dict]]:
    """Return (top_k_relevant, rest) sorted by token overlap with the conjecture."""
    if not proved_lemmas:
        return [], []
    context_tokens = (
        _camel_tokens(theorem_name)
        | {w for w in re.findall(r"\w+", " ".join(hypotheses).lower())}
        | {w for w in re.findall(r"\w+", conclusion.lower())}
    ) - _RANK_STOP

    def _score(e: dict) -> int:
        text = f"{e.get('node_id', '')} {e.get('description', '')}"
        tokens = _camel_tokens(text) | {w for w in re.findall(r"\w+", text.lower())}
        return len(tokens & context_tokens)

    ranked = sorted(proved_lemmas, key=_score, reverse=True)
    return ranked[:top_k], ranked[top_k:]


# ---------------------------------------------------------------------------
# Discovery-mode blueprint prompt
# ---------------------------------------------------------------------------

DISCOVERY_BLUEPRINT_PROMPT = """\
You are a Lean 4 proof discovery expert working in the domain of combinatorial
polytope theory. Your task is to devise a proof strategy for the following
UNPROVEN conjecture and express it as a directed acyclic graph (DAG) of
blueprint nodes. There is no known proof — you must figure out how to prove
it from first principles using Lean 4 / Mathlib tactics and the Inventory lemmas
listed below.

Conjecture name: {theorem_name}
Lean signature:  {lean_signature}
Hypotheses:
{hypotheses}
Conclusion: {conclusion}

## Domain context (simple 3-polytopes / maps on surfaces)
- Euler's formula for the sphere: v - e + f = 2
- Handshaking: 2e = sum_k k*p_k   (each face has k edges)
- Vertex-degree for simple polytopes: 2e = 3v
- p-vector constraint: sum_k p_k = f_2  (total face count)
- Dehn–Sommerville: sum_k (6-k)*p_k = 12  (for genus-0 simple maps)
- All p_k >= 0; only finitely many p_k are nonzero (captured by maps.m)
- The Lean structure is SimplyCon3ConnectedMap 0 (genus 0 = sphere for ALL IRIS
  conjectures). Fields: maps.p_i k (face counts), maps.v, maps.e, maps.m.
  NEVER use maps.f2 or maps.f_2 — those fields do not exist.
  f_2 (total face count) = ∑ k in Finset.Ico 3 (maps.m + 1), maps.p_i k.
  Do NOT add IsSimple, maps.simple, or any simplicity hypothesis — it is not defined.

## Polib lemmas (available via `import Inventory`)
Two kinds are listed below:
- **proved** (no tag): fully verified, zero sorry — safe to depend on directly.
- **partial** (tagged `[partial — has sorry…]`): proof structure exists but incomplete.
  Use these for **structural reference** (understand the proof approach, reuse sub-steps),
  but do NOT add them as `dependencies` — treat them as inspiration, not axioms.

The most relevant lemmas are shown with their Lean signatures; others are listed
by name only. Use signatures to decide which lemma to call and how to apply it.
{available_lemmas}
For any node whose proof can directly call a **proved** lemma, say so explicitly
in the `description` field.

## Node structure
- Each auxiliary definition or lemma needed before the main result gets its own node.
- **Parallelism**: only add a dependency edge A→B when B's proof body will
  DIRECTLY call or apply A by name. Avoid speculative edges — unnecessary
  dependencies force sequential execution and slow things down.
- **Independence**: if two sub-lemmas don't use each other's results, leave
  them unconnected so they can run in parallel. For example, extracting the
  Euler relation and extracting the handshaking identity are independent; only
  the final combination node should depend on both.
- Node types: "def" | "lemma" | "theorem"
- Exactly ONE node must have "is_main_target": true.
- "latex_fragment": write a brief mathematical description of what this node
  states (no verbatim proof exists — summarise the sub-goal instead).

## CRITICAL — Node naming
All nodes live in a shared Inventory namespace. You MUST prefix every new node
you define with the exact conjecture identifier: `{theorem_name}`.

  REQUIRED prefix: `{theorem_name}`
  BAD:   "InequalityBound"        ← no prefix, will collide
  BAD:   "P6InequalityBound"      ← wrong conjecture prefix
  GOOD:  "{theorem_name}InequalityBound"  ← correct

Exception: nodes that intentionally REUSE an existing Inventory lemma listed above
must use that lemma's exact name unchanged.

## CRITICAL — Dependency rules
Add A as a dependency of B ONLY IF B's proof directly calls/applies A's result
or B's type mentions a type defined in A. When in doubt, omit the dependency.

## CRITICAL — Cross-theorem dependencies are FORBIDDEN
Dependencies must only reference node_ids defined WITHIN THIS blueprint.
Do NOT list a node_id from another theorem's blueprint (e.g. "C2_DehnSommerville"
for a C4 blueprint) — those lemmas are already available via `import Inventory` and
must NOT appear as dependency entries. If you need a proved Inventory lemma, just
reference it by name in the `description` field; leave `dependencies` empty for that edge.

Respond with ONLY valid JSON — no prose, no markdown fences.

{{
  "nodes": [
    {{
      "node_id": "CamelCaseUniqueId",
      "node_type": "def" | "lemma" | "theorem",
      "description": "One sentence: what this node proves or defines.",
      "latex_fragment": "Brief mathematical description of the sub-goal.",
      "dependencies": ["only_direct_deps_here"],
      "is_main_target": false
    }}
  ]
}}
"""


class ConjectureDecomposer(BlueprintDecomposer):
    """BlueprintDecomposer variant that uses the discovery-mode prompt."""

    def __init__(self, client, model: str, polib_lean: Path | None = None) -> None:
        super().__init__(client, model)
        self._polib_lean = polib_lean

    def decompose(
        self,
        parsed: ParsedTheorem,
        goal,
        proved_lemmas: list[dict] | None = None,
    ) -> Blueprint:
        locked_goal = goal.goal if hasattr(goal, "goal") else goal

        # Load Lean signatures once from Polib.lean (best-effort)
        sigs: dict[str, str] = {}
        if self._polib_lean is not None:
            sigs = _extract_lean_signatures(self._polib_lean)

        # Rank lemmas by relevance; show top-k with signatures, rest names-only
        all_lemmas: list[dict] = proved_lemmas or []
        top, rest = _rank_lemmas_for_discovery(
            all_lemmas,
            theorem_name=parsed.name,
            hypotheses=list(parsed.hypotheses),
            conclusion=parsed.conclusion,
        )

        def _fmt_entry(e: dict) -> str:
            line = f"  - `{e['node_id']}`"
            if e.get("description"):
                line += f": {e['description']}"
            sig = sigs.get(e["node_id"], "")
            if sig:
                line += f"\n    Lean: `{sig}`"
            return line

        if all_lemmas:
            avail_lines = [_fmt_entry(e) for e in top]
            if rest:
                rest_ids = ", ".join(f"`{e['node_id']}`" for e in rest)
                avail_lines.append(
                    f"  Also available (name only): {rest_ids}"
                )
            avail = "\n".join(avail_lines)
        else:
            avail = "  (none yet)"

        user_content = DISCOVERY_BLUEPRINT_PROMPT.format(
            theorem_name=parsed.name,
            lean_signature=locked_goal.lean_signature,
            hypotheses="\n".join(f"  - {h}" for h in parsed.hypotheses),
            conclusion=parsed.conclusion,
            available_lemmas=avail,
        )
        response = self._client.messages.create(
            model=self._model,
            max_tokens=2048,
            messages=[{"role": "user", "content": user_content}],
        )
        text = response.content[0].text.strip()
        nodes = _parse_blueprint_json(text)
        polib_ids = {e["node_id"] for e in (proved_lemmas or [])}
        _validate_blueprint_nodes(nodes, known_polib_ids=polib_ids)
        topo_order = _topological_sort(nodes)
        blueprint_data = json.dumps([n.to_dict() for n in nodes], sort_keys=True)
        blueprint_hash = hashlib.sha256(blueprint_data.encode()).hexdigest()
        return Blueprint(
            theorem_name=parsed.name,
            nodes=nodes,
            topo_order=topo_order,
            blueprint_hash=blueprint_hash,
        )


# ---------------------------------------------------------------------------
# ProverAgent
# ---------------------------------------------------------------------------

class ProverAgent(FormalizerAgent):
    """Attempts to prove unproven conjectures using the standard formalization
    pipeline but with a discovery-mode blueprint decomposer.

    Usage
    -----
    agent = ProverAgent(Config.from_env())

    # From a ParsedConjecture (parsed from the IRIS table):
    result = agent.prove_conjecture(conjecture)

    # From a raw statement string:
    result = agent.prove_statement(
        statement_latex="$p_6 \\geq -5\\sum_{k\\geq 7} p_k + 10$",
        conjecture_id="MyConj",
    )

    # From a ParsedTheorem already constructed elsewhere:
    result = agent.prove(parsed_theorem)
    """

    _proof_subdir: str = "conjecture_proof"  # output/conjecture_proof/ instead of complete_proof/

    def __init__(self, config: Config) -> None:
        super().__init__(config)
        # Replace the standard decomposer with the discovery-mode one.
        self._decomposer = ConjectureDecomposer(
            self._sdk_fast,
            config.model_fast,
            polib_lean=Path(config.polib_path) / "Polib.lean",
        )

    # ------------------------------------------------------------------
    # Public API
    # ------------------------------------------------------------------

    def prove_conjecture(
        self,
        conjecture: ParsedConjecture,
        category: str = "Polytope",
        verbose: bool = True,
    ) -> FormalizationResult:
        """Prove a ParsedConjecture (extracted from the IRIS table).

        Output is written to output/conjecture_proof/{conjecture_id}.lean.
        """
        # tex_path stem is used as the output filename; the file need not exist.
        tex_path = str(
            Path(__file__).resolve().parent.parent
            / "conjectures" / "individual"
            / f"{conjecture.short_id.lower()}.tex"
        )
        parsed_theorem = conjecture.to_parsed_theorem()
        return self.formalize(
            conjecture._synth_latex(),
            category=category,
            verbose=verbose,
            tex_path=tex_path,
            parsed=parsed_theorem,
        )

    def prove_statement(
        self,
        statement_latex: str,
        conjecture_id: str = "Conjecture",
        category: str = "Polytope",
        verbose: bool = True,
    ) -> FormalizationResult:
        """Prove an arbitrary LaTeX statement string (no theorem environment needed)."""
        parser = ConjectureParser()
        conjecture = parser.parse_statement(statement_latex, conjecture_id)
        return self.prove_conjecture(conjecture, category=category, verbose=verbose)

    def prove(
        self,
        parsed: ParsedTheorem,
        category: str = "Polytope",
        verbose: bool = True,
    ) -> FormalizationResult:
        """Prove using an already-constructed ParsedTheorem (skips LLM parsing)."""
        return self.formalize(
            parsed.latex_source,
            category=category,
            verbose=verbose,
            parsed=parsed,
        )
