from __future__ import annotations

import hashlib
import json
import os
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
from agent.prover import lean_codegen
from agent.prover._node_solver_mixin import NodeSolverMixin
from agent.prover._proof_assembly_mixin import ProofAssemblyMixin
from agent.prover._strategies_mixin import StrategiesMixin
from agent.prover.conjecture_decomposer import ConjectureDecomposer, DISCOVERY_BLUEPRINT_PROMPT
from agent.prover.polib_store import PolibStore
from agent.prover.tools.blueprint import Blueprint, BlueprintDecomposer, BlueprintNode
from agent.prover.tools.formalization_logger import FormalizationLogger
from agent.prover.tools.goal_lock import GoalExtractor, GoalLock, GoalValidator, LockedGoal
from agent.prover.tools.latex_parser import LatexParser, ParsedTheorem
from agent.prover.tools.lean_compiler import LeanCompiler
from agent.prover.tools.polib_manager import DepGraphManager, PolibManager, SessionState, StoreManager
from agent.prover.tools.quality_checker import QualityChecker, QualityReport
from agent.prover.tools.search import CombinedHintGenerator, GitHubLean4Search, MathlibSearch, PolibSearch
from agent.orchestrator.tools.conjecture_parser import ConjectureParser, ParsedConjecture
from agent.prover.tools.prompt_optimizer import extract_signature, filter_dep_imports_to_direct
from agent.prover.tools.output_search import OutputSearch
from agent.prover.tools.llm_hint_generator import LLMHintGenerator, FailureRecord


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


class FormalizerAgent(NodeSolverMixin, ProofAssemblyMixin, StrategiesMixin):
    _proof_subdir: str = "complete_proof"  # overrideable by subclasses

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
            content = self._polib_store.read()
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
        # Planner uses model_main (Sonnet): blueprint decomposition is the
        # highest-leverage decision in the pipeline — a bad blueprint kills
        # all downstream LLM calls. Haiku has been observed (2026-06-28/29)
        # to repeatedly invent the same arithmetically-false intermediate
        # lemma `p_6 + 5·∑_{k≥7} p_k ≥ 10` for C104. Per-call cost is ~5x
        # higher than Haiku but planner is called once per conjecture so the
        # absolute impact is small. See D-2 in the C104 post-mortem.
        self._decomposer = BlueprintDecomposer(self._sdk, config.model_main)
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
        self._polib_store = PolibStore(self._polib_mgr)
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
            PolibStore.invalidate_path(polib_lean)

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
        elif node.lean_signature:
            # Sub-lemma with a locked Lean signature supplied by the planner.
            # Treat it like main target: show the signature as authoritative and
            # require the LLM to prove it exactly. Eliminates signature drift
            # across retry rounds and across nested sub-lemma decompositions.
            goal_context = (
                f"Locked sub-lemma signature (IMMUTABLE — you MUST prove this "
                f"exactly as written):\n{node.lean_signature}\n\n"
                f"This sub-lemma supports the parent theorem `{theorem_name}` "
                f"whose signature is:\n  {goal.lean_signature}\n"
                f"⚠ GENUS RULE: keep `SimplyCon3ConnectedMap 0` consistent with "
                f"the parent; do NOT default to generic `{{g : ℤ}}`."
            )
            goal_instruction = _GOAL_INSTR_INTERMEDIATE.format(
                node_id=node.node_id,
                node_type=node.node_type,
                theorem_name=theorem_name,
            )
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

        # Change 3: Polib compendium — append signatures of OTHER proved
        # lemmas (not in direct deps) so Sonnet can laterally reuse them
        # without re-deriving. Critical when planner under-specifies deps
        # (e.g. C104_CaseLargeSum could call C104_HandshakingConstraint even
        # if planner didn't link them in the blueprint).
        compendium = self._build_polib_compendium(proven_deps, max_extra=30)
        if compendium:
            dep_details_str = dep_details_str + "\n\n" + compendium

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

        # Change 2b: sandwich prompt — prepend a tight summary so Sonnet
        # sees the SPECIFIC task + most-relevant hints + most-recent
        # error FIRST (primacy bias). The existing prior_context section
        # near the end provides recency. Together: critical info is
        # double-exposed, dramatically reducing the time Sonnet spends
        # searching the full prompt during extended thinking.
        prompt = self._build_sandwich_summary(
            node=node,
            goal=goal,
            hints=hints,
            existing_code=existing_code,
            cross_run_errors=cross_run_errors,
        ) + prompt
        raw = self._sdk._call(prompt, fast_model=self._config.model_fast,
                              system=LEAN_GENERATION_SYSTEM_PROMPT)
        code = lean_codegen.normalize_lean(lean_codegen.strip_markdown(raw))
        code = lean_codegen.ensure_preamble(code)
        if not node.is_main_target:
            code = lean_codegen.rename_last_decl(code, node.node_id)
        return code


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
        # Include planner prompt hash so any prompt tuning auto-invalidates old
        # blueprints. Prevents the "stale-cache poisoning" failure mode where a
        # newly fixed planner prompt keeps serving the broken old decomposition
        # (root cause of the C104 latex_fragment coefficient-swap incident).
        prompt_hash = hashlib.sha256(
            DISCOVERY_BLUEPRINT_PROMPT.encode()
        ).hexdigest()[:8]
        return f"{latex_key}:{struct_hash}:{prompt_hash}"

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

    def _rank_and_trim_hints(
        self,
        hints: list[str],
        node: BlueprintNode,
        goal_signature: str = "",
        max_keep: int = 8,
    ) -> list[str]:
        """Rank `hints` by token overlap with the node's goal/description, keep top-K.

        Why: hint generator returns up to 16 candidates from Loogle; many are
        only weakly relevant. Sonnet has to filter signal from noise during
        thinking, which fragments the response across many assistant turns
        (root cause of the C104 `max_turns` hits). Cutting to top-8 by
        token-overlap similarity cuts prompt noise ~50% and reduces thinking
        fragmentation. Hints with no overlap STILL get a base score so we
        don't completely drop e.g. structural `linarith`/`omega` mentions.

        Token similarity is computed against (node.description + latex_fragment
        + goal_signature), tokenised by CamelCase + snake_case + dot splits.
        Pattern hints injected by _inject_pattern_hints already sit at the top
        of the list and get a stability bonus so they don't get evicted.
        """
        if len(hints) <= max_keep:
            return hints

        # Build the reference token bag from goal + node info
        ref_text = " ".join(filter(None, [
            node.description or "",
            getattr(node, "latex_fragment", "") or "",
            goal_signature or "",
        ]))
        ref_tokens = lean_codegen.tokenize_for_hint_ranking(ref_text)
        if not ref_tokens:
            return hints[:max_keep]  # graceful degradation: just truncate

        scored: list[tuple[float, int, str]] = []  # (score, original_idx, hint)
        for idx, h in enumerate(hints):
            tokens = lean_codegen.tokenize_for_hint_ranking(h)
            if not tokens:
                overlap = 0.0
            else:
                overlap = len(tokens & ref_tokens) / max(1, len(tokens | ref_tokens))
            # Stability bonus for earlier hints (preserves pattern-hint ordering)
            stability = max(0.0, 0.05 * (1.0 - idx / max(1, len(hints))))
            scored.append((overlap + stability, idx, h))

        # Pick top max_keep by score; keep original order for ties → stable
        scored.sort(key=lambda x: (-x[0], x[1]))
        kept = [h for _, _, h in scored[:max_keep]]
        # Log how many we dropped for visibility
        dropped = len(hints) - len(kept)
        if dropped > 0:
            try:
                self._log(True,
                    f"  [hint-rank] {node.node_id}: kept {len(kept)}/"
                    f"{len(hints)} hints (dropped {dropped} low-overlap)")
            except Exception:
                pass
        return kept

    def _regen_hints_from_bad_name(
        self,
        bad_name: str,
        current_hints: list[str],
        verbose: bool = True,
    ) -> list[str]:
        """When LLM hallucinates a Mathlib name (e.g. `Finset.sum_Ico_succ`),
        query Loogle with the bad name's tokens to find REAL candidates.

        Returns at most 5 new (not already in current_hints) hints.

        Why: without this, the LLM might re-hallucinate the same name (or
        another close-but-wrong name) on the next round. By injecting real
        Mathlib results, we channel the fix into actually existing lemmas.

        This is information injection (provides knowledge), NOT strategy
        injection (doesn't say HOW to use the lemmas).
        """
        # Tokenize the bad name into searchable parts:
        # "Finset.sum_Ico_succ" → ["Finset", "sum", "Ico", "succ"]
        tokens = lean_codegen.tokenize_for_hint_ranking(bad_name)
        if not tokens:
            return []
        # Drop common-noise tokens
        tokens = {t for t in tokens if t not in {"the", "a", "an", "of", "in"}}
        if not tokens:
            return []
        # Build a Loogle keyword query (space-joined tokens)
        query = " ".join(sorted(tokens))
        try:
            # Reuse the hint generator's Loogle helper if available
            hg = getattr(self, "_hint_generator", None)
            if hg is None:
                return []
            # _query_keyword exists on CombinedHintGenerator — use it directly
            qf = getattr(hg, "_query_keyword", None)
            if not callable(qf):
                return []
            results = qf(query) or []
        except Exception:
            return []
        # Filter: not already in hints, and not the bad name itself
        existing = set(current_hints or [])
        new = [
            r for r in results
            if r and r not in existing and r != bad_name
        ][:5]
        if new and verbose:
            try:
                self._log(True,
                    f"  [error-regen] queried Loogle for `{bad_name}` tokens "
                    f"({query}), got {len(new)} real candidate(s)")
            except Exception:
                pass
        return new

    def _build_polib_compendium(
        self,
        proven_deps: list[str],
        max_extra: int = 30,
    ) -> str:
        """Return a block listing ALL session-proved Polib lemmas' signatures
        (no bodies), MINUS the ones already shown as direct deps.

        Why: planner declares only DIRECT dependencies. Sonnet might find a
        non-direct already-proved lemma useful (e.g. C104_CaseLargeSum could
        leverage C104_HandshakingConstraint even though planner didn't link
        them). Showing all proved signatures lets the LLM laterally reuse
        without re-deriving — especially important when the same conjecture
        has been partially proved in a previous run.

        Returns "" if no Polib entries beyond direct deps.
        """
        all_entries = getattr(self._polib_search, "_entries", []) or []
        direct_dep_set = set(proven_deps or [])
        # Filter: proved status, not already in direct deps, has a real signature
        extras: list[tuple[str, str]] = []
        for entry in all_entries:
            nid = getattr(entry, "node_id", None)
            if not nid or nid in direct_dep_set:
                continue
            if getattr(entry, "status", None) != "proved":
                continue
            lean_name = getattr(entry, "theorem_name", None) or nid
            sig = self._extract_polib_signature(lean_name)
            if sig and len(sig) < 600:  # exclude monster signatures
                extras.append((lean_name, sig.strip()))
        if not extras:
            return ""
        # Cap to max_extra most recent (rough proxy for "most relevant in current
        # session"). If Polib has 100+ entries this prevents prompt bloat.
        extras = extras[-max_extra:]
        lines: list[str] = [
            "## Other proved Polib lemmas available (lateral reuse — call by name; do NOT redeclare):",
            "(Compendium: all session-proved lemmas. Use any that matches a step you need.)",
        ]
        for name, sig in extras:
            sig_one = " ".join(sig.split())[:280]
            lines.append(f"- `{name}` : `{sig_one}`")
        return "\n".join(lines) + "\n"

    @staticmethod
    def _build_sandwich_summary(
        node: BlueprintNode,
        goal: "LockedGoal",
        hints: list[str],
        existing_code: str | None = None,
        cross_run_errors: list[dict] | None = None,
    ) -> str:
        """Tight `[TL;DR]` block prepended to the lean-generation prompt.

        Why: Sonnet 4.6 with extended thinking will scan the full prompt
        before responding. For a 30KB prompt this fragments the response
        into many assistant turns (each "now I'll think about X" can become
        a separate AssistantMessage → counted as a turn). Putting the
        critical info upfront primes thinking onto the right pieces FAST,
        reducing turn fragmentation. Keep this block compact (≤ 25 lines).
        """
        lines: list[str] = ["[TL;DR — critical task summary, read this first]\n"]
        # 1. Goal — most important
        lines.append(f"GOAL: prove `{node.node_id}` (type: {node.node_type})")
        if node.latex_fragment:
            lines.append(f"CLAIM: {node.latex_fragment[:200]}")
        # 2. The exact Lean signature it needs to satisfy
        sig = (goal.lean_signature or "").strip().splitlines()
        if sig:
            sig_text = " ".join(sig)[:240]
            lines.append(f"SIGNATURE: {sig_text}")
        # 3. Top 5 most relevant hints (already pre-ranked)
        if hints:
            lines.append("TOP HINTS (most relevant first):")
            for h in hints[:5]:
                lines.append(f"  • {h}")
        # 4. If retry: most-recent failure to avoid repeating
        if cross_run_errors:
            last_err = cross_run_errors[-1].get("error", "")[:160]
            if last_err:
                lines.append(f"LAST FAILURE (do NOT repeat): {last_err}")
        # 5. If retry-partial: existing code's first/last lines for orientation
        if existing_code:
            code_lines = existing_code.strip().splitlines()
            if len(code_lines) >= 2:
                lines.append(
                    f"PRIOR CODE: {code_lines[0][:80]} ... {code_lines[-1][:80]}"
                )
        lines.append("\n[End TL;DR — full context follows]\n\n")
        return "\n".join(lines)

    def _load_polib_code(self, node_id: str, category: str = "") -> str | None:
        """Extract a node's lean code from Polib.lean (proved entries) or output/Output/ (partial)."""
        content = self._polib_store.read()
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

    # ------------------------------------------------------------------
    # Complete proof file assembly
    # ------------------------------------------------------------------

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

# ---------------------------------------------------------------------------
# Signature extraction + relevance ranking helpers
# ---------------------------------------------------------------------------

_SIG_DECL_START = re.compile(
    r"^(?:private\s+)?(?:lemma|theorem|def|abbrev)\s+(\w+)",
    re.MULTILINE,
)




_RANK_STOP = frozenset(
    {"maps", "the", "a", "an", "and", "or", "in", "of", "for", "is", "to",
     "with", "all", "let", "if", "then", "be", "by", "on", "at", "from"}
)




# ---------------------------------------------------------------------------
# Discovery-mode blueprint prompt
# ---------------------------------------------------------------------------



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
