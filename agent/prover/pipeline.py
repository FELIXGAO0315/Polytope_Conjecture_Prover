"""Top-level prover pipeline orchestrator.

Single source of truth for the 8-stage formalization flow.  Each stage is a
free function taking ``agent`` (a FormalizerAgent or ProverAgent) plus the
outputs of earlier stages, and returns its own result.  ``formalize()`` is
the small orchestrator that strings them together with the shared
exception handler around stages 1-5.

The 8 stages mirror the ``[N/8]`` log messages the prover prints:

    1.  Parse LaTeX                     -> ParsedTheorem
    2.  Lock + validate goal signature  -> GoalLock
    3.  Decompose into blueprint DAG    -> Blueprint
    4.  Per-node compile loop (parallel by dep level)
    5.  Retry failed nodes
    6.  Quality-check summary
    7.  Polib validate + repair
    8.  Collect results + assemble proof file

To debug or replay a single stage, import the function directly:

    from agent.prover.pipeline import _step4_node_loop
    proven, imports = _step4_node_loop(agent, blueprint, goal_lock, parsed,
                                       "Polytope", verbose=True)

``FormalizerAgent.formalize()`` is a one-line delegate to ``formalize()``
here, so external callers (Orchestrator, run.py, tests) keep working
unchanged.
"""
from __future__ import annotations

import re
import traceback
import uuid as _uuid
from concurrent.futures import ThreadPoolExecutor, as_completed
from datetime import datetime, timezone
from pathlib import Path
from typing import TYPE_CHECKING

from agent.exceptions import GoalTamperedError
from agent.prover.tools.formalization_logger import FormalizationLogger
from agent.prover.tools.goal_lock import GoalLock

if TYPE_CHECKING:
    from agent.prover.agent import FormalizationResult, FormalizerAgent
    from agent.prover.tools.blueprint import Blueprint
    from agent.prover.tools.latex_parser import ParsedTheorem


# ---------------------------------------------------------------------------
# Stage 1 - Resolve theorem (from pre-parsed conjecture, or LaTeX fallback)
# ---------------------------------------------------------------------------

def _step1_resolve_theorem(
    agent: "FormalizerAgent",
    latex_source: str,
    parsed: "ParsedTheorem | None",
    verbose: bool,
) -> "ParsedTheorem":
    """Resolve the theorem to formalize.

    The primary path is **JSON-driven**: ``ProverAgent.prove_conjecture``
    builds a ``ParsedTheorem`` directly from a ``ParsedConjecture`` (which
    came from ``conjectures.json``) and passes it in via ``parsed=``.  No
    LLM call is needed.

    The LaTeX-parsing path (``parsed is None``) is a fallback for the rare
    case where only a raw LaTeX string is available — it invokes the
    LLM-backed LaTeX parser.  This path is **not** used by the current
    ``python -m formalize`` / ``python -m run`` CLIs.
    """
    if parsed is not None:
        agent._log(verbose,
            f"[1/8] Using pre-parsed theorem from JSON: "
            f"{parsed.name} ({len(parsed.proof_steps)} step(s))")
    else:
        if not latex_source:
            raise ValueError(
                "_step1_resolve_theorem: need either parsed= or non-empty latex_source"
            )
        agent._log(verbose, "[1/8] Parsing LaTeX source (fallback path, no pre-parsed theorem)...")
        parsed = agent._parser.parse_with_llm(
            latex_source, agent._sdk_fast, agent._config.model_fast,
        )
        agent._log(verbose,
            f"      parsed: {parsed.name} ({len(parsed.proof_steps)} step(s))")
    agent._flog._data["theorem_name"] = parsed.name
    agent._flog._flush()
    return parsed


# ---------------------------------------------------------------------------
# Stage 2 - Lock goal signature
# ---------------------------------------------------------------------------

# Goal signatures using these substrings indicate the LLM hallucinated a
# predicate that does not exist in Inventory.  Discard the cache and
# re-extract rather than letting downstream compiles all fail with
# "unknown identifier IsSimple" etc.
_BAD_SIG_PATTERNS = (
    "IsSimple", "maps.simple", "maps.is_simple", "simple maps",
    "maps.f2 ", "maps.f_2 ", "maps.f2\n", "maps.f_2\n",
)
_TRIVIAL_CONCLUSION_RE = re.compile(r":\s*(?:True|False|Prop)\s*:=\s*by\s*$")
_F2_INT_COMPARE_RE = re.compile(r"maps\.p_i 2\s*[≥≤><=]")


def _signature_is_rejectable(sig: str) -> bool:
    if any(p in sig for p in _BAD_SIG_PATTERNS):
        return True
    if _TRIVIAL_CONCLUSION_RE.search(sig.strip()):
        return True
    if _F2_INT_COMPARE_RE.search(sig):
        return True
    return False


def _step2_lock_goal(
    agent: "FormalizerAgent",
    parsed: "ParsedTheorem",
    verbose: bool,
) -> GoalLock:
    """Lock the theorem's Lean signature (cache first, re-extract on bad sig)."""
    agent._log(verbose, "[2/8] Extracting & locking goal...")
    goal_lock = agent._load_cached_goal(parsed, verbose=verbose) or GoalLock.create(
        parsed, agent._extractor, agent._validator, max_attempts=3,
    )
    # Reject signatures using undefined predicates / wrong f_2 translation —
    # they would fail every downstream compile.
    if _signature_is_rejectable(goal_lock.goal.lean_signature):
        agent._log(verbose,
            "  [goal-reject] Signature uses undefined predicate or wrong f_2 — "
            "discarding cache and re-extracting.")
        goal_lock = GoalLock.create(
            parsed, agent._extractor, agent._validator, max_attempts=3,
        )
    agent._save_cached_goal(parsed, goal_lock)

    if not goal_lock.goal.validator_confirmed:
        agent._log(True,
            f"\n  *** WARNING: Goal signature was NOT confirmed by the validator. ***\n"
            f"  *** Proceeding with best-effort signature: ***\n"
            f"  *** {goal_lock.goal.lean_signature[:100]} ***\n"
            f"  *** Notes: {goal_lock.goal.validator_notes} ***\n"
        )

    agent._log(verbose, f"      signature: {goal_lock.goal.lean_signature[:80]}...")
    return goal_lock


# ---------------------------------------------------------------------------
# Stage 3 - Blueprint decomposition
# ---------------------------------------------------------------------------

def _step3_blueprint(
    agent: "FormalizerAgent",
    parsed: "ParsedTheorem",
    goal_lock: GoalLock,
    verbose: bool,
) -> "Blueprint":
    """Decompose the proof into a DAG of nodes (cached by latex hash)."""
    agent._log(verbose, "[3/8] Decomposing blueprint...")
    proved_lemmas = [
        {
            "node_id": e["node_id"],
            "description": (
                e.get("description", "")
                + (" [partial — has sorry, use for structural reference only]"
                   if e.get("status") == "partial" else "")
            ),
        }
        for e in (agent._store.get("polib_index") or [])
        if isinstance(e, dict) and e.get("status") in ("proved", "partial")
    ]
    blueprint = (
        agent._load_cached_blueprint(parsed, goal_lock, verbose=verbose)
        or agent._decomposer.decompose(parsed, goal_lock.goal, proved_lemmas=proved_lemmas)
    )
    agent._save_cached_blueprint(parsed, goal_lock, blueprint)
    agent._log(verbose, f"      nodes: {[n.node_id for n in blueprint.nodes]}")
    agent._log(verbose, f"      topo order: {blueprint.topo_order}")
    return blueprint


# ---------------------------------------------------------------------------
# Stage 4 - Per-node loop (parallel by dependency level)
# ---------------------------------------------------------------------------

def _step4_node_loop(
    agent: "FormalizerAgent",
    blueprint: "Blueprint",
    goal_lock: GoalLock,
    parsed: "ParsedTheorem",
    category: str,
    verbose: bool,
) -> tuple[list[str], dict[str, str]]:
    """Run ``_process_node`` for every blueprint node, grouped by dependency
    level so independent nodes can compile in parallel.

    Returns ``(proven_node_ids_in_topo_order, proven_dep_imports)`` so stage 5
    has a fresh view of what's available for downstream nodes."""
    agent._log(verbose, "[4/8] Formalizing nodes...")
    levels = agent._compute_parallel_levels(blueprint)
    proven_node_ids: list[str] = []
    proven_dep_imports: dict[str, str] = {}

    for level_idx, level_nodes in enumerate(levels):
        if len(level_nodes) == 1:
            node_id = level_nodes[0]
            status = agent._process_node(
                node_id, blueprint, goal_lock, parsed,
                category, list(proven_node_ids), verbose,
                proven_dep_imports=dict(proven_dep_imports),
            )
            if status in ("proved", "partial"):
                proven_node_ids.append(node_id)
                proven_dep_imports[node_id] = "Polib"
        else:
            workers = min(len(level_nodes), agent._config.max_parallel_nodes)
            agent._log(verbose,
                f"  [level {level_idx}] parallelizing {level_nodes} ({workers} workers)")
            snapshot_ids = list(proven_node_ids)
            snapshot_imports = dict(proven_dep_imports)
            level_results: dict[str, str] = {}

            with ThreadPoolExecutor(max_workers=workers) as executor:
                future_to_node = {
                    executor.submit(
                        agent._process_node,
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
                        agent._log(verbose, f"  [thread-err] {nid}: {exc}")
                        level_results[nid] = "pending"

            for nid in level_nodes:
                res = level_results.get(nid)
                if res in ("proved", "partial"):
                    proven_node_ids.append(nid)
                    proven_dep_imports[nid] = "Polib"

    return proven_node_ids, proven_dep_imports


# ---------------------------------------------------------------------------
# Stage 5 - Retry failed nodes
# ---------------------------------------------------------------------------

_MAX_RETRY_ITERS = 20


def _step5_retry_failed(
    agent: "FormalizerAgent",
    blueprint: "Blueprint",
    goal_lock: GoalLock,
    parsed: "ParsedTheorem",
    category: str,
    verbose: bool,
    proven_node_ids: list[str],
    proven_dep_imports: dict[str, str],
) -> None:
    """Retry nodes that failed in stage 4.

    Instead of restarting the whole pipeline N times (which would redo
    parse / goal / blueprint each time), retry just the failed nodes here.
    Each retry feeds the cross-run failure memory + newly-available dep
    signatures back into the generation prompt.

    Mutates ``proven_node_ids`` and ``proven_dep_imports`` in place as nodes
    flip from failed to proved/partial.
    """

    def _collect_failed() -> list[str]:
        _nodes = agent._session.data.get("nodes", {})
        return [
            nid for nid in blueprint.topo_order
            if _nodes.get(nid, {}).get("status") not in ("proved", "partial")
        ]

    failed_now = _collect_failed()
    if not failed_now:
        return

    agent._log(verbose, "\n[5/8] Retrying failed nodes...")
    max_node_retries = agent._config.max_node_retries
    retry_counts: dict[str, int] = {}
    consecutive_no_progress = 0
    iter_count = 0

    while failed_now and iter_count < _MAX_RETRY_ITERS:
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
                agent._log(verbose,
                    f"  [{nid}] skipped — waiting on failed dep(s): {blocked}")
                continue
            if retry_counts.get(nid, 0) >= max_node_retries:
                agent._log(verbose,
                    f"  [{nid}] retry budget exhausted ({max_node_retries})")
                continue
            retry_counts[nid] = retry_counts.get(nid, 0) + 1
            attempted_any = True
            node_data = agent._session.data.get("nodes", {}).get(nid, {})
            last_err = (node_data.get("last_error") or "(unknown)").strip()
            last_err_line = last_err.splitlines()[0][:140] if last_err else "(unknown)"
            agent._log(verbose, f"  [{nid}] previous failure: {last_err_line}")
            agent._log(verbose,
                f"  [{nid}] retry {retry_counts[nid]}/{max_node_retries}: "
                f"regenerate with updated dep signatures + cross-run failure memory")
            try:
                status = agent._process_node(
                    nid, blueprint, goal_lock, parsed,
                    category, list(proven_node_ids), verbose=False,
                    proven_dep_imports=dict(proven_dep_imports),
                )
            except GoalTamperedError:
                raise
            except Exception as exc:
                agent._log(verbose, f"  [{nid}] retry crashed: {exc}")
                status = "pending"

            if status in ("proved", "partial"):
                agent._log(verbose, f"  [{nid}] retry successfully → {status}")
                still_failing.discard(nid)
                if nid not in proven_node_ids:
                    proven_node_ids.append(nid)
                    proven_dep_imports[nid] = "Polib"
                any_progress = True
            else:
                agent._log(verbose, f"  [{nid}] still failing")

        failed_now = _collect_failed()
        if not attempted_any:
            agent._log(verbose,
                "  [retry-exhausted] remaining nodes are blocked or out of "
                "retry budget; stopping")
            break
        if not any_progress:
            consecutive_no_progress += 1
            if consecutive_no_progress >= 2:
                agent._log(verbose,
                    "  [retry-stall] no progress for 2 consecutive iterations; stopping")
                break
        else:
            consecutive_no_progress = 0

    if not failed_now:
        agent._log(verbose,
            f"  [retrying] all nodes resolved after {iter_count} iteration(s)")


# ---------------------------------------------------------------------------
# Stage 6 - Quality summary
# ---------------------------------------------------------------------------

def _step6_quality_summary(
    agent: "FormalizerAgent",
    blueprint: "Blueprint",
    verbose: bool,
) -> None:
    """Print per-node quality reports collected during stages 4-5."""
    agent._log(verbose, "[6/8] Checking formalization quality...")
    with agent._run_codes_lock:
        qr_snapshot = dict(agent._run_quality_reports)
        skipped_snapshot = set(agent._run_skipped_nodes)
    for node_id in blueprint.topo_order:
        qr = qr_snapshot.get(node_id)
        if qr is None:
            agent._log(verbose, f"  [{node_id}] — not reached (dependency failed)")
            continue
        tag = "PASS" if qr.passed else "FAIL"
        if node_id in skipped_snapshot:
            agent._log(verbose, f"  [{node_id}] Retrying... (loaded from Polib)")
        agent._log(verbose, f"    Quality: {tag} (score={qr.score:.2f})")
        for finding in qr.findings:
            agent._log(verbose, f"    • {finding}")


# ---------------------------------------------------------------------------
# Stage 7 - Polib validate + repair
# ---------------------------------------------------------------------------

def _step7_polib_repair(agent: "FormalizerAgent", verbose: bool) -> None:
    """Run PolibValidator on the assembled Polib.lean; downgrade session
    state for any node it removed so stage 8 classifies it as failed."""
    from agent.prover.tools.polib_validator import PolibValidator
    agent._log(verbose, "[7/8] Validating Polib...")
    validator = PolibValidator(
        polib_lean=agent._polib_mgr._polib_lean,
        workspace=Path(agent._config.polib_path),
        log_fn=lambda msg: agent._log(verbose, msg),
    )
    val_result = validator.validate_and_repair()
    for nid in val_result.all_removed:
        agent._session.mark_pending(
            nid, 0, "Polib validator removed broken section — re-run to re-prove",
        )


# ---------------------------------------------------------------------------
# Stage 8 - Collect results + assemble proof file
# ---------------------------------------------------------------------------

def _classify_final_status(
    nodes_proved: list[str],
    nodes_partial: list[str],
    nodes_failed: list[str],
) -> str:
    if nodes_failed and not (nodes_proved or nodes_partial):
        return "failed"
    if nodes_failed or nodes_partial:
        return "partial"
    return "success"


def _step8_collect_and_save(
    agent: "FormalizerAgent",
    parsed: "ParsedTheorem",
    blueprint: "Blueprint",
    tex_path: str | None,
    verbose: bool,
    nodes_proved: list[str],
    nodes_partial: list[str],
    nodes_failed: list[str],
    dep_graph_path: str,
    session_state_path: str,
) -> "FormalizationResult":
    """Read final per-node status from the session, assemble the output
    .lean file, and build the FormalizationResult to return to the caller."""
    from agent.prover.agent import FormalizationResult  # avoid circular import

    all_session_nodes = agent._session.data.get("nodes", {})
    for node_id in blueprint.topo_order:
        node_data = all_session_nodes.get(node_id, {})
        status = node_data.get("status")
        if status == "proved":
            nodes_proved.append(node_id)
        elif status == "partial":
            nodes_partial.append(node_id)
        else:
            nodes_failed.append(node_id)

    if agent._flog:
        agent._flog.finish_run()

    sorry_total = agent._sorry_get()

    if tex_path:
        lean_out_path, _, _ = agent._write_complete_proof_file(
            tex_path,
            parsed.name if parsed is not None else "(unknown)",
            nodes_proved, nodes_partial, nodes_failed, sorry_total,
        )
        agent._log(verbose, f"[8/8] Formalization saved → {lean_out_path}")

    return FormalizationResult(
        theorem_name=parsed.name,
        status=_classify_final_status(nodes_proved, nodes_partial, nodes_failed),
        nodes_proved=nodes_proved,
        nodes_partial=nodes_partial,
        nodes_failed=nodes_failed,
        total_sorry_count=sorry_total,
        error=None,
        dep_graph_path=dep_graph_path,
        session_state_path=session_state_path,
    )


# ---------------------------------------------------------------------------
# Failure-path helpers (used by the try/except wrapping stages 1-5)
# ---------------------------------------------------------------------------

def _collect_session_into(
    agent: "FormalizerAgent",
    blueprint: "Blueprint | None",
    nodes_proved: list[str],
    nodes_partial: list[str],
    nodes_failed: list[str],
) -> None:
    """Best-effort population of result lists from session state when an
    exception aborted stages 1-5."""
    if blueprint is None:
        return
    try:
        session_nodes = agent._session.data.get("nodes", {})
        for nid in blueprint.topo_order:
            nd = session_nodes.get(nid, {})
            st = nd.get("status")
            if st == "proved" and nid not in nodes_proved:
                nodes_proved.append(nid)
            elif st == "partial" and nid not in nodes_partial:
                nodes_partial.append(nid)
            elif st not in ("proved", "partial") and nid not in nodes_failed:
                nodes_failed.append(nid)
    except Exception:
        pass


def _build_failed_result(
    agent: "FormalizerAgent",
    parsed: "ParsedTheorem | None",
    exc: BaseException,
    nodes_proved: list[str],
    nodes_partial: list[str],
    nodes_failed: list[str],
    dep_graph_path: str,
    session_state_path: str,
    include_traceback: bool,
) -> "FormalizationResult":
    from agent.prover.agent import FormalizationResult  # avoid circular import

    if agent._flog:
        agent._flog.finish_run()
    err_msg = (f"{type(exc).__name__}: {exc}\n{traceback.format_exc()}"
               if include_traceback
               else f"{type(exc).__name__}: {exc}")
    return FormalizationResult(
        theorem_name=parsed.name if parsed is not None else "Unknown",
        status="failed",
        nodes_proved=nodes_proved,
        nodes_partial=nodes_partial,
        nodes_failed=nodes_failed,
        total_sorry_count=agent._sorry_get(),
        error=err_msg,
        dep_graph_path=dep_graph_path,
        session_state_path=session_state_path,
    )


# ---------------------------------------------------------------------------
# Top-level orchestrator
# ---------------------------------------------------------------------------

def formalize(
    agent: "FormalizerAgent",
    latex_source: str = "",
    category: str = "Polytope",
    verbose: bool = True,
    tex_path: str | None = None,
    parsed: "ParsedTheorem | None" = None,
) -> "FormalizationResult":
    """Run the 8-stage prover pipeline on a single theorem.

    The primary entry passes ``parsed=`` (a pre-built ``ParsedTheorem``
    coming from a JSON conjecture); ``latex_source`` is then unused and
    can be omitted.  The legacy LaTeX-only path remains supported: if
    ``parsed`` is None, ``latex_source`` MUST be a non-empty LaTeX string
    and the LLM-backed LaTeX parser will run as stage 1.

    Stages 1-5 (which call out to Claude + lake) are wrapped in a
    try/except so a crash still returns a structured FormalizationResult
    instead of propagating to the orchestrator.  Stages 6-8 run
    unconditionally on the success path and produce the final report.
    """
    polib_path = Path(agent._config.polib_path)
    store_path_str = str(agent._config.store_path)
    dep_graph_path = store_path_str
    session_state_path = store_path_str

    nodes_proved: list[str] = []
    nodes_partial: list[str] = []
    nodes_failed: list[str] = []
    blueprint: "Blueprint | None" = None

    # Reset per-run code collection
    with agent._run_codes_lock:
        agent._run_codes.clear()
        agent._run_quality_reports.clear()
        agent._run_skipped_nodes.clear()

    # Initialise per-run formalization logger
    run_id = datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%S") + f"_{_uuid.uuid4().hex[:6]}"
    log_dir = polib_path.parent / "logs"
    agent._flog = FormalizationLogger(log_dir, run_id, theorem_name="(pending)")

    try:
        parsed = _step1_resolve_theorem(agent, latex_source, parsed, verbose)
        goal_lock = _step2_lock_goal(agent, parsed, verbose)
        blueprint = _step3_blueprint(agent, parsed, goal_lock, verbose)
        proven_node_ids, proven_dep_imports = _step4_node_loop(
            agent, blueprint, goal_lock, parsed, category, verbose,
        )
        _step5_retry_failed(
            agent, blueprint, goal_lock, parsed, category, verbose,
            proven_node_ids, proven_dep_imports,
        )
    except GoalTamperedError as exc:
        return _build_failed_result(
            agent, parsed, exc, nodes_proved, nodes_partial, nodes_failed,
            dep_graph_path, session_state_path, include_traceback=False,
        )
    except Exception as exc:
        _collect_session_into(agent, blueprint, nodes_proved, nodes_partial, nodes_failed)
        return _build_failed_result(
            agent, parsed, exc, nodes_proved, nodes_partial, nodes_failed,
            dep_graph_path, session_state_path, include_traceback=True,
        )

    _step6_quality_summary(agent, blueprint, verbose)
    _step7_polib_repair(agent, verbose)
    return _step8_collect_and_save(
        agent, parsed, blueprint, tex_path, verbose,
        nodes_proved, nodes_partial, nodes_failed,
        dep_graph_path, session_state_path,
    )
