"""Top-level prover agent.

``ProverAgent.prove_conjecture`` is the single public entry: it builds a
``ParsedTheorem`` from a JSON conjecture, then delegates to the 8-stage
pipeline in ``agent/prover/pipeline.py``.

This module owns:
  * ``FormalizationResult`` — the per-conjecture status returned to callers
  * ``FormalizerAgent``     — shared infrastructure (SDK clients, caches,
                              session state) used by every pipeline stage
  * ``ProverAgent``         — adds the discovery-mode blueprint decomposer

The actual proof-generation core lives in ``agent/prover/proof_agent.py``
(one LLM session + one MCP ``lean_compile`` tool); this file no longer
contains compile-fix loops, hint generators, sandwich prompts, or any of
the pre-proof_agent scaffolding.
"""
from __future__ import annotations

import hashlib
import threading
from dataclasses import dataclass, field
from pathlib import Path

from agent.claude_sdk import ClaudeSDKClient
from agent.config import Config
from agent.prover._node_solver_mixin import NodeSolverMixin
from agent.prover._proof_assembly_mixin import ProofAssemblyMixin
from agent.prover.conjecture_decomposer import ConjectureDecomposer, DISCOVERY_BLUEPRINT_PROMPT
from agent.prover.polib_store import PolibStore
from agent.prover.tools.blueprint import Blueprint
from agent.prover.tools.formalization_logger import FormalizationLogger
from agent.prover.tools.goal_lock import LockedGoal, _GOAL_PROMPT_HASH
from agent.prover.tools.lean_compiler import LeanCompiler
from agent.prover.tools.parsed_theorem import ParsedTheorem
from agent.prover.tools.polib_manager import DepGraphManager, PolibManager, SessionState, StoreManager
from agent.prover.tools.quality_checker import QualityChecker, QualityReport
from agent.prover.tools.search import PolibSearch
from agent.orchestrator.tools.conjecture_parser import ParsedConjecture


@dataclass
class FormalizationResult:
    """Per-conjecture pipeline outcome.

    Under no-new-sorry policy a node is either fully ``"proved"`` or fully
    failed — there is no ``"partial"`` state, hence no ``nodes_partial`` field
    and no ``total_sorry_count``.
    """
    theorem_name: str
    status: str  # "success" | "failed"
    nodes_proved: list[str]
    nodes_failed: list[str]  # blocking failures only — see nodes_unused
    error: str | None
    dep_graph_path: str
    session_state_path: str
    # Failed blueprint nodes the root proof never referenced (planner
    # over-decomposition); they don't block a "success" verdict.
    nodes_unused: list[str] = field(default_factory=list)

    @property
    def success(self) -> bool:
        return self.status == "success"

    def to_dict(self) -> dict:
        return {
            "theorem_name": self.theorem_name,
            "status": self.status,
            "nodes_proved": self.nodes_proved,
            "nodes_failed": self.nodes_failed,
            "error": self.error,
            "dep_graph_path": self.dep_graph_path,
            "session_state_path": self.session_state_path,
            "nodes_unused": self.nodes_unused,
        }


class FormalizerAgent(NodeSolverMixin, ProofAssemblyMixin):
    _proof_subdir: str = "complete_proof"  # overrideable by subclasses

    def __init__(self, config: Config):
        self._config = config

        # Claude Code SDK client — no API key needed
        self._sdk = ClaudeSDKClient(model=config.model_main)
        self._sdk_fast = ClaudeSDKClient(model=config.model_fast)

        polib_path = Path(config.polib_path)
        store_path = Path(config.store_path)

        self._store = StoreManager(store_path)
        # NOTE: self._decomposer is set by ProverAgent.__init__.  Blueprint
        # decomposition is the highest-leverage decision in the pipeline — a
        # bad blueprint kills every downstream LLM call.  Haiku has been
        # observed (2026-06-28/29) to invent the arithmetically-false
        # intermediate lemma `p_6 + 5·∑_{k≥7} p_k ≥ 10` for C104, so
        # ProverAgent uses model_main (Sonnet).  See D-2 in the C104 post-mortem.

        self._polib_search = PolibSearch(self._store)
        self._compiler = LeanCompiler(
            polib_path,
            config.compile_timeout_seconds,
            keep_on_failure=config.keep_temp_on_failure,
            lake_binary=config.lake_binary,
        )
        self._quality = QualityChecker(self._sdk_fast, config.model_fast)
        self._dep_graph = DepGraphManager(self._store)
        self._polib_mgr = PolibManager(polib_path, self._polib_search, self._dep_graph)
        self._polib_store = PolibStore(self._polib_mgr)
        self._session = SessionState(self._store)

        # Output directory — Lake project for user inspection
        self._output_root = polib_path.parent / "output"
        self._output_root.mkdir(parents=True, exist_ok=True)

        # Ensure Polib.lean exists before any compilation
        self._ensure_polib_lean(polib_path)

        # Per-run state
        self._flog: FormalizationLogger | None = None   # set by formalize()
        self._save_lock = threading.Lock()              # dep_graph + session saves
        self._run_codes: dict[str, str] = {}            # node_id → final Lean code
        self._run_codes_lock = threading.Lock()
        self._run_quality_reports: dict[str, QualityReport] = {}
        self._run_skipped_nodes: set[str] = set()       # loaded from Polib, shown in step 6

    # ------------------------------------------------------------------
    # Polib.lean preflight
    # ------------------------------------------------------------------

    @staticmethod
    def _ensure_polib_lean(polib_path: Path) -> None:
        """Create polib/Polib.lean if missing, and ensure Polib/_Temp exists.
        Inventory.lean is hand-crafted and never touched here.
        Polib.lean only needs imports — foundational content lives in Inventory.lean.
        """
        from agent.prover.tools.polib_manager import _SECTION_MARKER
        polib_lean = polib_path / "Polib.lean"
        temp_dir = polib_path / "Polib" / "_Temp"
        temp_dir.mkdir(parents=True, exist_ok=True)
        # Scratch modules linger when a compile fails (keep_on_failure) or a
        # run dies mid-compile; prune to the newest 50 at startup so the dir
        # can't grow without bound (it once reached 242 files / 1.1 MB).
        stale = sorted(temp_dir.glob("*.lean"),
                       key=lambda p: p.stat().st_mtime)[:-50]
        for f in stale:
            try:
                f.unlink()
            except OSError:
                pass

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
        proved_part = (
            existing[existing.index(_SECTION_MARKER):]
            if _SECTION_MARKER in existing else _SECTION_MARKER
        )
        if not existing.startswith(header):
            polib_lean.write_text(header + proved_part, encoding="utf-8")
            PolibStore.invalidate_path(polib_lean)

    # ------------------------------------------------------------------
    # Logging
    # ------------------------------------------------------------------

    def _log(self, verbose: bool, msg: str) -> None:
        if verbose:
            print(msg)

    # ------------------------------------------------------------------
    # Cache helpers (goal lock + blueprint, both keyed off parsed.content_hash)
    # ------------------------------------------------------------------

    def _goal_cache_key(self, parsed: ParsedTheorem) -> str:
        # Include the extraction-prompt hash so cached signatures auto-evict
        # when the prompt is tuned (otherwise a fixed prompt would keep
        # serving the old buggy signatures).
        return f"{parsed.content_hash}:{_GOAL_PROMPT_HASH}"

    def _blueprint_cache_key(self, parsed: ParsedTheorem, locked: LockedGoal) -> str:
        # struct_hash invalidates when SimplyCon3ConnectedMap fields change.
        # prompt_hash invalidates when the planner prompt is tuned — prevents
        # stale-cache poisoning (a fixed prompt serving the old broken
        # decomposition; root cause of the C104 latex_fragment swap incident).
        # NOTE: polib_hash intentionally excluded — new proved lemmas are
        # available via `import Inventory` without needing a blueprint regen.
        # Including it caused blueprint churn (different strategy each run → worse).
        from agent.prover.prompts.lean_generation import SHARED_MODULE_CONTENT
        struct_hash = hashlib.sha256(SHARED_MODULE_CONTENT.encode()).hexdigest()[:8]
        prompt_hash = hashlib.sha256(DISCOVERY_BLUEPRINT_PROMPT.encode()).hexdigest()[:8]
        return f"{parsed.content_hash}:{struct_hash}:{prompt_hash}"

    def _load_cached_goal(self, parsed: ParsedTheorem, verbose: bool = True) -> LockedGoal | None:
        """Return a confirmed cached goal, or None.

        Returns None on cache miss, on schema mismatch (logged + entry
        evicted), or on an unconfirmed cache entry (also evicted — step 2
        guarantees we never write those, so any such entry on disk is from
        an older code version).
        """
        key = self._goal_cache_key(parsed)
        goals = self._store.get("goals") or {}
        data = goals.get(key)
        if data is None:
            return None
        try:
            locked = LockedGoal.from_dict(data)
        except Exception as exc:
            self._log(verbose,
                f"      [cache evict] goal entry {key} unreadable ({type(exc).__name__}): "
                f"{str(exc)[:80]} — discarding")
            self._evict_cached_goal(key)
            return None
        if not locked.validator_confirmed:
            self._log(verbose,
                f"      [cache evict] goal entry {key} was unconfirmed — discarding")
            self._evict_cached_goal(key)
            return None
        self._log(verbose, f"      [cache hit] goal loaded from store (key={key})")
        return locked

    def _save_cached_goal(self, parsed: ParsedTheorem, locked: LockedGoal) -> None:
        self._store.update_in("goals", self._goal_cache_key(parsed), locked.to_dict())

    def _evict_cached_goal(self, key: str) -> None:
        goals = dict(self._store.get("goals") or {})
        if key in goals:
            del goals[key]
            self._store.update("goals", goals)

    def _load_cached_blueprint(
        self, parsed: ParsedTheorem, locked: LockedGoal, verbose: bool = True,
    ) -> Blueprint | None:
        """Return a cached blueprint, or None.

        On schema mismatch (old code version, hand-edited cache, etc.) the
        bad entry is logged + evicted so subsequent runs don't keep paying
        the same re-decompose tax.
        """
        key = self._blueprint_cache_key(parsed, locked)
        blueprints = self._store.get("blueprints") or {}
        data = blueprints.get(key)
        if data is None:
            return None
        try:
            bp = Blueprint.from_dict(data)
        except Exception as exc:
            self._log(verbose,
                f"      [cache evict] blueprint entry {key} unreadable "
                f"({type(exc).__name__}): {str(exc)[:80]} — discarding")
            self._evict_cached_blueprint(key)
            return None
        self._log(verbose, f"      [cache hit] blueprint loaded from store (key={key})")
        return bp

    def _save_cached_blueprint(
        self, parsed: ParsedTheorem, locked: LockedGoal, blueprint: Blueprint,
    ) -> None:
        self._store.update_in(
            "blueprints", self._blueprint_cache_key(parsed, locked), blueprint.to_dict(),
        )

    def _evict_cached_blueprint(self, key: str) -> None:
        blueprints = dict(self._store.get("blueprints") or {})
        if key in blueprints:
            del blueprints[key]
            self._store.update("blueprints", blueprints)

    # ------------------------------------------------------------------
    # Polib code recovery (used by NodeSolverMixin._process_node)
    # ------------------------------------------------------------------

    def _load_polib_code(self, node_id: str, category: str = "") -> str | None:
        """Extract a node's Lean code from Polib.lean, or from output/Output/ fallback.

        Only ``-- === {node_id} (proved) ===`` sections are returned — stale
        ``(partial)`` sections from before the no-new-sorry policy are
        IGNORED (their bodies contain sorry, and downstream callers expect
        clean code).  Imports-only output files (stale placeholders where the
        proof body was never written) are rejected — a valid output file
        must contain at least one lemma/theorem/def declaration.
        """
        import re as _re
        content = self._polib_store.read()
        marker = f"-- === {node_id} (proved)"
        if content and marker in content:
            start = content.index(marker)
            next_marker = content.find("\n-- === ", start + 1)
            section = content[start:] if next_marker == -1 else content[start:next_marker]
            return f"import Mathlib\nimport Inventory\n\n{section.strip()}\n"
        output_file = self._output_root / "Output" / f"{node_id}.lean"
        if not output_file.exists():
            return None
        code = output_file.read_text(encoding="utf-8")
        _decl_re = _re.compile(
            r'^(?:private\s+|protected\s+|noncomputable\s+)*'
            r'(?:lemma|theorem|def|abbrev)\s+',
            _re.MULTILINE,
        )
        return code if _decl_re.search(code) else None

    # ------------------------------------------------------------------
    # Main pipeline
    # ------------------------------------------------------------------

    def formalize(
        self,
        parsed: ParsedTheorem,
        output_stem: str,
        category: str = "Polytope",
        verbose: bool = True,
    ) -> FormalizationResult:
        """Thin delegate — orchestration lives in agent/prover/pipeline.py."""
        from agent.prover.pipeline import formalize as _pipeline_formalize
        return _pipeline_formalize(
            self, parsed, output_stem,
            category=category, verbose=verbose,
        )


# ---------------------------------------------------------------------------
# ProverAgent
# ---------------------------------------------------------------------------

class ProverAgent(FormalizerAgent):
    """Prove unproven JSON conjectures via the discovery-mode planner.

        agent = ProverAgent(Config.from_env())
        result = agent.prove_conjecture(conjecture)
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

    def prove_conjecture(
        self,
        conjecture: ParsedConjecture,
        category: str = "Polytope",
        verbose: bool = True,
    ) -> FormalizationResult:
        """Prove a ParsedConjecture (extracted from conjectures.json).

        Output is written to ``output/conjecture_proof/{short_id}.lean``.
        """
        return self.formalize(
            parsed=conjecture.to_parsed_theorem(),
            output_stem=conjecture.short_id.lower(),
            category=category,
            verbose=verbose,
        )
