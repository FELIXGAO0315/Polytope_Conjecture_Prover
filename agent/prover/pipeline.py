"""Top-level prover pipeline orchestrator.

Single source of truth for the 8-stage formalization flow.  Each stage is a
free function taking ``agent`` (a FormalizerAgent or ProverAgent) plus the
outputs of earlier stages, and returns its own result.  ``formalize()`` is
the small orchestrator that strings them together with the shared
exception handler around stages 1-5.

The 8 stages mirror the ``[N/8]`` log messages the prover prints:

    1.  Receive pre-parsed conjecture   -> ParsedTheorem
    2.  Lock + validate goal signature  -> LockedGoal
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
from agent.prover.tools.goal_lock import LockedGoal, lock_goal

if TYPE_CHECKING:
    from agent.prover.agent import FormalizationResult, FormalizerAgent
    from agent.prover.tools.blueprint import Blueprint
    from agent.prover.tools.parsed_theorem import ParsedTheorem


# ---------------------------------------------------------------------------
# Stage 1 - Receive pre-parsed conjecture
# ---------------------------------------------------------------------------

def _step1_resolve_theorem(
    agent: "FormalizerAgent",
    parsed: "ParsedTheorem",
    verbose: bool,
) -> "ParsedTheorem":
    """Receive the conjecture to formalize.

    The pipeline is JSON-only: ``ProverAgent.prove_conjecture`` builds a
    ``ParsedTheorem`` directly from a ``ParsedConjecture`` (sourced from
    ``conjectures.json``) and passes it in.  No parsing happens here — this
    stage's only job is to log a structural summary so debugging later
    stages does not require re-deriving what step 1 saw, and to record the
    theorem name on the run logger.
    """
    n_hyps = len(parsed.hypotheses)
    conc_preview = parsed.conclusion[:80].replace("\n", " ")
    agent._log(verbose,
        f"[1/8] Received conjecture {parsed.name}: "
        f"{n_hyps} hypothesis(es), conclusion='{conc_preview}'")
    agent._flog.set_theorem_name(parsed.name)
    return parsed


# ---------------------------------------------------------------------------
# Stage 2 - Lock goal signature
# ---------------------------------------------------------------------------

def _step2_lock_goal(
    agent: "FormalizerAgent",
    parsed: "ParsedTheorem",
    verbose: bool,
) -> LockedGoal:
    """Lock the theorem's Lean signature.

    Truth source = ``_check_signature_static`` (deterministic Python regex,
    no LLM call).  ``_load_cached_goal`` already refuses to return unconfirmed
    entries, so any non-None cache hit short-circuits the extractor.  Best-
    effort signatures are NEVER persisted to the cache.
    """
    locked = agent._load_cached_goal(parsed, verbose=verbose)
    if locked is not None:
        agent._log(verbose, f"[2/8] Goal cached: {locked.lean_signature[:80]}...")
        return locked

    agent._log(verbose, "[2/8] Extracting & locking goal...")
    locked = lock_goal(
        parsed, agent._sdk_fast, agent._config.model_fast,
        max_attempts=3,
        log=(lambda msg: agent._log(verbose, msg)),
    )
    if locked.validator_confirmed:
        agent._save_cached_goal(parsed, locked)
    else:
        agent._log(True,
            "\n  *** Static check could not confirm the signature after 3 attempts. ***\n"
            f"  *** Best-effort signature: {locked.lean_signature[:100]} ***\n"
            "  *** Not saving to cache — re-extracted next run.\n"
        )
    agent._log(verbose, f"      signature: {locked.lean_signature[:80]}...")
    return locked


# ---------------------------------------------------------------------------
# Stage 3 - Blueprint decomposition
# ---------------------------------------------------------------------------

def _step3_blueprint(
    agent: "FormalizerAgent",
    parsed: "ParsedTheorem",
    locked: LockedGoal,
    verbose: bool,
) -> "Blueprint":
    """Decompose the proof into a DAG of nodes (cached by content hash)."""
    cached = agent._load_cached_blueprint(parsed, locked, verbose=verbose)
    if cached is not None:
        agent._log(verbose,
            f"[3/8] Blueprint cached: {len(cached.nodes)} node(s), "
            f"topo order: {cached.topo_order}")
        return cached

    agent._log(verbose, "[3/8] Decomposing blueprint...")
    # Only show fully-proved Polib entries to the planner.  Partial entries
    # are sorry-tainted: calling one transitively pulls its sorry into our
    # new proof's dependency closure, violating the no-new-sorry policy.
    proved_lemmas = [
        {"node_id": e["node_id"], "description": e.get("description", "")}
        for e in (agent._store.get("polib_index") or [])
        if isinstance(e, dict) and e.get("status") == "proved"
    ]
    blueprint = agent._decomposer.decompose(
        parsed, locked,
        proved_lemmas=proved_lemmas,
        log=(lambda msg: agent._log(verbose, msg)),
    )
    agent._save_cached_blueprint(parsed, locked, blueprint)
    agent._log(verbose, f"      nodes: {[n.node_id for n in blueprint.nodes]}")
    agent._log(verbose, f"      topo order: {blueprint.topo_order}")
    return blueprint


# ---------------------------------------------------------------------------
# Stage 4 - Per-node loop (parallel by dependency level)
# ---------------------------------------------------------------------------

def _step4_node_loop(
    agent: "FormalizerAgent",
    blueprint: "Blueprint",
    locked: LockedGoal,
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
                node_id, blueprint, locked, parsed,
                category, list(proven_node_ids), verbose,
                proven_dep_imports=dict(proven_dep_imports),
            )
            if status == "proved":
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
                        nid, blueprint, locked, parsed,
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
                if level_results.get(nid) == "proved":
                    proven_node_ids.append(nid)
                    proven_dep_imports[nid] = "Polib"

    return proven_node_ids, proven_dep_imports


# ---------------------------------------------------------------------------
# Stage 5 - Retry failed nodes
# ---------------------------------------------------------------------------

def _step5_retry_failed(
    agent: "FormalizerAgent",
    blueprint: "Blueprint",
    locked: LockedGoal,
    parsed: "ParsedTheorem",
    category: str,
    verbose: bool,
    proven_node_ids: list[str],
    proven_dep_imports: dict[str, str],
) -> None:
    """Retry nodes that failed in stage 4.

    The loop terminates when either (a) all nodes are settled, (b) every
    remaining node is out of per-node retry budget, or (c) two consecutive
    iterations make zero progress. There is no separate "max iterations"
    cap — the retry budget per node already bounds the total work.

    Mutates ``proven_node_ids`` and ``proven_dep_imports`` in place as nodes
    flip from failed to proved.
    """

    def _collect_failed() -> list[str]:
        _nodes = agent._session.data.get("nodes", {})
        return [
            nid for nid in blueprint.topo_order
            if _nodes.get(nid, {}).get("status") != "proved"
        ]

    failed_now = _collect_failed()
    if not failed_now:
        return

    agent._log(verbose, "\n[5/8] Retrying failed nodes...")
    max_node_retries = agent._config.max_node_retries
    retry_counts: dict[str, int] = {}
    consecutive_no_progress = 0
    iter_count = 0

    while failed_now:
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
                    nid, blueprint, locked, parsed,
                    category, list(proven_node_ids), verbose=verbose,
                    proven_dep_imports=dict(proven_dep_imports),
                )
            except GoalTamperedError:
                raise
            except Exception as exc:
                agent._log(verbose, f"  [{nid}] retry crashed: {exc}")
                status = "pending"

            if status == "proved":
                agent._log(verbose, f"  [{nid}] retry successfully → proved")
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
    """Post-flight Polib sanity check.

    Stage 4's per-save `_verify_polib_builds` already guards each entry
    transactionally, so most cross-node breakage is caught at save time.
    This stage is the safety net: it re-validates the assembled Polib and
    downgrades any node whose section turns out to be broken when the file
    is read as a whole. If nothing is removed, the stage is a no-op.
    """
    from agent.prover.tools.polib_validator import PolibValidator
    agent._log(verbose, "[7/8] Validating Polib (post-flight safety net)...")
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

def _classify_final_status(nodes_proved: list[str], nodes_failed: list[str]) -> str:
    """Under no-new-sorry policy a conjecture is ``"success"`` iff EVERY blueprint
    node was fully proved (zero sorry, zero failures).  Any failed node makes
    the whole thing ``"failed"`` — there is no intermediate ``"partial"`` state.
    """
    if not nodes_proved and not nodes_failed:
        return "failed"          # blueprint produced no nodes at all
    return "success" if not nodes_failed else "failed"


def _step8_collect_and_save(
    agent: "FormalizerAgent",
    parsed: "ParsedTheorem",
    blueprint: "Blueprint",
    output_stem: str,
    verbose: bool,
    nodes_proved: list[str],
    nodes_failed: list[str],
    dep_graph_path: str,
    session_state_path: str,
) -> "FormalizationResult":
    """Read final per-node status from the session, assemble the output
    .lean file, and build the FormalizationResult to return to the caller.

    Stale ``"partial"`` session entries (from before the no-new-sorry policy)
    are mapped to ``failed`` — they are sorry-tainted and not real proofs.
    """
    from agent.prover.agent import FormalizationResult  # avoid circular import

    all_session_nodes = agent._session.data.get("nodes", {})
    for node_id in blueprint.topo_order:
        status = all_session_nodes.get(node_id, {}).get("status")
        if status == "proved":
            nodes_proved.append(node_id)
        else:
            nodes_failed.append(node_id)

    if agent._flog:
        agent._flog.finish_run()

    lean_out_path, _, _ = agent._write_complete_proof_file(
        output_stem, parsed.name, nodes_proved, nodes_failed,
    )
    agent._log(verbose, f"[8/8] Formalization saved → {lean_out_path}")

    return FormalizationResult(
        theorem_name=parsed.name,
        status=_classify_final_status(nodes_proved, nodes_failed),
        nodes_proved=nodes_proved,
        nodes_failed=nodes_failed,
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
    nodes_failed: list[str],
) -> None:
    """Best-effort population of result lists from session state when an
    exception aborted stages 1-5.  Anything not ``"proved"`` counts as failed.
    """
    if blueprint is None:
        return
    try:
        session_nodes = agent._session.data.get("nodes", {})
        for nid in blueprint.topo_order:
            st = session_nodes.get(nid, {}).get("status")
            if st == "proved" and nid not in nodes_proved:
                nodes_proved.append(nid)
            elif st != "proved" and nid not in nodes_failed:
                nodes_failed.append(nid)
    except Exception:
        pass


def _build_failed_result(
    agent: "FormalizerAgent",
    parsed: "ParsedTheorem | None",
    exc: BaseException,
    nodes_proved: list[str],
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
        nodes_failed=nodes_failed,
        error=err_msg,
        dep_graph_path=dep_graph_path,
        session_state_path=session_state_path,
    )


# ---------------------------------------------------------------------------
# Top-level orchestrator
# ---------------------------------------------------------------------------

def formalize(
    agent: "FormalizerAgent",
    parsed: "ParsedTheorem",
    output_stem: str,
    category: str = "Polytope",
    verbose: bool = True,
) -> "FormalizationResult":
    """Run the 8-stage prover pipeline on one pre-parsed conjecture.

    ``parsed`` comes from ``ParsedConjecture.to_parsed_theorem()`` (built
    upstream from a row of ``conjectures.json``).  ``output_stem`` is the
    filename stem of the final ``.lean`` proof — the run writes
    ``output/{agent._proof_subdir}/{output_stem}.lean``.

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
        parsed = _step1_resolve_theorem(agent, parsed, verbose)
        locked = _step2_lock_goal(agent, parsed, verbose)
        blueprint = _step3_blueprint(agent, parsed, locked, verbose)
        proven_node_ids, proven_dep_imports = _step4_node_loop(
            agent, blueprint, locked, parsed, category, verbose,
        )
        _step5_retry_failed(
            agent, blueprint, locked, parsed, category, verbose,
            proven_node_ids, proven_dep_imports,
        )
    except GoalTamperedError as exc:
        return _build_failed_result(
            agent, parsed, exc, nodes_proved, nodes_failed,
            dep_graph_path, session_state_path, include_traceback=False,
        )
    except Exception as exc:
        _collect_session_into(agent, blueprint, nodes_proved, nodes_failed)
        return _build_failed_result(
            agent, parsed, exc, nodes_proved, nodes_failed,
            dep_graph_path, session_state_path, include_traceback=True,
        )

    _step6_quality_summary(agent, blueprint, verbose)
    _step7_polib_repair(agent, verbose)
    return _step8_collect_and_save(
        agent, parsed, blueprint, output_stem, verbose,
        nodes_proved, nodes_failed,
        dep_graph_path, session_state_path,
    )
