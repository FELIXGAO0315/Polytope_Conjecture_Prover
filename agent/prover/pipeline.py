"""Top-level prover pipeline orchestrator.

Single source of truth for the 9-stage formalization flow.  Each stage is a
free function taking ``agent`` (a FormalizerAgent or ProverAgent) plus the
outputs of earlier stages, and returns its own result.  ``formalize()`` is
the small orchestrator that strings them together with the shared
exception handler around stages 1-5.

The 9 stages mirror the ``[N/9]`` log messages the prover prints:

    1.  Receive pre-parsed conjecture   -> ParsedTheorem
    2.  Lock + validate goal signature  -> LockedGoal
    3.  Decompose into blueprint DAG    -> Blueprint
    4.  Per-node compile loop (parallel by dep level)
    5.  Retry failed nodes
    6.  Deep quality check (drift, axioms, semantic re-check)
    7.  Polib validate + repair
    8.  Collect results + assemble proof file
    9.  Write natural-language proof (only on clean success)

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
        f"[1/9] Received conjecture {parsed.name}: "
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
        agent._log(verbose, f"[2/9] Goal cached: {locked.lean_signature[:80]}...")
        return locked

    agent._log(verbose, "[2/9] Extracting & locking goal...")
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
            f"[3/9] Blueprint cached: {len(cached.nodes)} node(s), "
            f"topo order: {cached.topo_order}")
        return cached

    agent._log(verbose, "[3/9] Decomposing blueprint...")
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
    agent._log(verbose, "[4/9] Formalizing nodes...")
    agent._log(verbose,
        f"  [proof-agent] Starting session "
        f"(model={agent._config.model_main}, "
        f"effort={agent._config.proof_agent_effort}, "
        f"max_turns={agent._config.proof_agent_max_turns}, "
        f"timeout={agent._config.proof_agent_timeout_seconds}s)")
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
    """Retry nodes that stage 4 did not prove.

    Truth source is ``proven_node_ids`` (stage 4's actual return), NOT session
    state — session can carry stale/aliased "proved" entries from prior runs
    and silently make step 5 skip real failures. ``proven_node_ids`` and
    ``proven_dep_imports`` are mutated in place as retries succeed.

    Terminates when all nodes are settled, every remaining node is blocked or
    out of retry budget, or two consecutive iterations make zero progress.
    """
    proven_set = set(proven_node_ids)
    failed = [nid for nid in blueprint.topo_order if nid not in proven_set]
    if not failed:
        agent._log(verbose, "\n[5/9] Retrying failed nodes... (nothing to retry, skipped)")
        return

    agent._log(verbose, "\n[5/9] Retrying failed nodes...")
    max_retries = agent._config.max_node_retries
    retry_counts: dict[str, int] = {}
    no_progress_streak = 0
    iter_count = 0

    while failed:
        iter_count += 1
        any_progress = False
        attempted_any = False
        for nid in failed:
            blocked = [d for d in blueprint.get_node(nid).dependencies
                       if d not in proven_set]
            if blocked:
                agent._log(verbose, f"  [{nid}] skipped — waiting on failed dep(s): {blocked}")
                continue
            if retry_counts.get(nid, 0) >= max_retries:
                agent._log(verbose, f"  [{nid}] retry budget exhausted ({max_retries})")
                continue
            retry_counts[nid] = retry_counts.get(nid, 0) + 1
            attempted_any = True
            last_err = (agent._session.data.get("nodes", {}).get(nid, {})
                        .get("last_error") or "(unknown)").splitlines()[0][:140]
            agent._log(verbose,
                f"  [{nid}] retry {retry_counts[nid]}/{max_retries} — prev: {last_err}")
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
                agent._log(verbose, f"  [{nid}] retry successful → proved")
                proven_node_ids.append(nid)
                proven_dep_imports[nid] = "Polib"
                proven_set.add(nid)
                any_progress = True
            else:
                agent._log(verbose, f"  [{nid}] still failing")

        failed = [nid for nid in blueprint.topo_order if nid not in proven_set]
        if not attempted_any:
            agent._log(verbose,
                "  [retry-exhausted] remaining nodes are blocked or out of retry budget; stopping")
            break
        if not any_progress:
            no_progress_streak += 1
            if no_progress_streak >= 2:
                agent._log(verbose,
                    "  [retry-stall] no progress for 2 consecutive iterations; stopping")
                break
        else:
            no_progress_streak = 0

    if not failed:
        agent._log(verbose, f"  [retrying] all nodes resolved after {iter_count} iteration(s)")


# ---------------------------------------------------------------------------
# Stage 6 - Deep quality check
# ---------------------------------------------------------------------------

def _step6_deep_check(
    agent: "FormalizerAgent",
    blueprint: "Blueprint",
    locked: LockedGoal,
    parsed: "ParsedTheorem",
    verbose: bool,
) -> None:
    """Deep quality gate over the saved per-node code.

    Runs 4 independent checks on every node whose session status is
    ``"proved"`` (see ``agent.prover.tools.deep_check``):

      D1  QR sanity — the per-node report exists and passed.
      D2  Signature drift — saved code's declaration signature has the
          same binder count, binder-type multiset, and conclusion as the
          LOCKED / planner-supplied signature.  Catches "LLM added a
          spurious hypothesis under the same theorem name".  A textual
          mismatch is arbitrated by a defeq compile check (`example :
          <locked ∀-type> := NAME`) so notation noise can't kill a valid
          proof while real drift still fails the type checker.
      D3  Axiom sweep — no `axiom` decl in saved code.
      D4  Instance sweep — no SimplyCon3ConnectedMap construction.

    Any node that fails is (a) downgraded via ``session.mark_pending`` so
    step 8's success classifier reports it as failed (or unused, when the
    root proof never references it) AND (b) purged from Polib via
    ``polib_mgr.remove`` so a bad entry can't poison downstream proofs on
    later runs (skipped for alias-reused nodes — nothing was saved under
    their name, and the alias target belongs to another conjecture).  A
    "success" FormalizationResult can no longer coexist with a deep-check
    failure ON THE ROOT'S PROOF CLOSURE, and Polib can no longer carry a
    proof the deep-check rejected.
    """
    from agent.prover.tools.deep_check import check_node

    agent._log(verbose, "[6/9] Deep quality check...")
    with agent._run_codes_lock:
        code_snapshot = dict(agent._run_codes)
        qr_snapshot = dict(agent._run_quality_reports)
        skipped_snapshot = set(agent._run_skipped_nodes)

    session_nodes = agent._session.data.get("nodes", {})
    total = 0
    passed = 0
    downgraded = 0

    for node_id in blueprint.topo_order:
        node = blueprint.get_node(node_id)
        session_status = session_nodes.get(node_id, {}).get("status")
        if session_status != "proved":
            agent._log(verbose,
                f"  [{node_id}] — not checked (session={session_status!r})")
            continue

        total += 1
        expected_sig_full = (
            locked.lean_signature if node.is_main_target
            else (node.lean_signature or "")
        )
        alias_name = agent._polib_search.resolve_alias(node_id)
        result = check_node(
            node_id=node_id,
            is_main_target=node.is_main_target,
            saved_code=code_snapshot.get(node_id),
            qr=qr_snapshot.get(node_id),
            expected_sig_full=expected_sig_full,
            parsed=parsed,
            quality_checker=agent._quality,
            compiler=agent._compiler,
            alias_name=alias_name,
        )

        tag = "PASS" if result.passed else "FAIL"
        origin = ""
        if node_id in skipped_snapshot:
            origin = (f" (from Polib cache → {alias_name})" if alias_name
                      else " (from Polib cache)")
        agent._log(verbose, f"  [{node_id}] Deep check: {tag}{origin}")
        for f in result.findings:
            if "FAIL" in f or "WARN" in f:
                agent._log(verbose, f"    • {f}")

        if result.passed:
            passed += 1
        else:
            agent._log(True,
                f"  [{node_id}] downgrading — deep check failed "
                f"(step 8 reports it as failed, or unused if the root "
                f"proof never references it)")
            agent._session.mark_pending(
                node_id, 0,
                f"step-6 deep-check failure: {result.failure_summary}",
            )
            # Also purge the tainted entry from Polib so downstream proofs
            # on later runs can't build on it.  session.mark_pending only
            # touches the session view; Polib.lean would still carry the
            # rejected section without this call.  Aliased nodes wrote
            # nothing under their own name — the alias TARGET belongs to
            # another conjecture and passed its own gates, so it stays.
            if alias_name is not None:
                agent._log(verbose,
                    f"  [{node_id}] alias reuse rejected — nothing to purge "
                    f"(target `{alias_name}` untouched)")
            else:
                try:
                    agent._polib_mgr.remove(node_id)
                    agent._log(verbose,
                        f"  [{node_id}] purged from Polib (deep check rejected)")
                except Exception as exc:
                    agent._log(True,
                        f"  [{node_id}] WARNING: purge failed ({exc}); "
                        f"Polib may carry a stale rejected entry")
            downgraded += 1

    tail = f" ({downgraded} downgraded)" if downgraded else ""
    agent._log(verbose,
        f"  Deep check summary: {passed}/{total} nodes passed{tail}")


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
    agent._log(verbose, "[7/9] Validating Polib (post-flight safety net)...")
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
    main_target_id: str | None,
    nodes_proved: list[str],
    nodes_failed_blocking: list[str],
) -> str:
    """``"success"`` iff the ROOT theorem is proved (zero sorry) and no failed
    node is referenced by any surviving proof.

    The root theorem is the deliverable: it compiled sorry-free inside Polib,
    and step 7 re-validated the whole Polib build — so every declaration its
    proof actually pulls in is itself proved.  A failed blueprint node the
    root never references is planner over-decomposition, not a gap in the
    proof (the C201 incident: 3 alias-reused sub-lemmas were downgraded by an
    alias-blind deep check while the root proved itself without them, and the
    all-nodes rule reported the fully-proved theorem as "failed").
    ``nodes_failed_blocking`` must already exclude unused failures — see
    ``_split_unused_failures``.
    """
    if main_target_id is None or main_target_id not in nodes_proved:
        return "failed"
    return "success" if not nodes_failed_blocking else "failed"


def _split_unused_failures(
    main_target_id: str | None,
    nodes_proved: list[str],
    nodes_failed: list[str],
    run_codes: dict[str, str],
) -> tuple[list[str], list[str]]:
    """Partition ``nodes_failed`` into (blocking, unused).

    A failed node is *unused* when no proved node's saved code references it
    by name — the root proof simply never needed it.  The scan is a
    belt-and-suspenders redundancy: a failed node's declaration was purged
    from Polib in step 6, so a surviving proof referencing it would have
    already broken the step-7 whole-Polib build.  Comment lines are skipped
    so a prose mention of the planner name can't flag a false reference.
    Without a proved main target every failure is blocking — nothing can be
    "unused" when there is no root proof to be unused BY.
    """
    if main_target_id is None or main_target_id not in nodes_proved:
        return list(nodes_failed), []
    proved_code_lines: list[str] = []
    for nid in nodes_proved:
        for ln in (run_codes.get(nid) or "").splitlines():
            stripped = ln.strip()
            if stripped and not stripped.startswith("--"):
                proved_code_lines.append(ln)
    blob = "\n".join(proved_code_lines)
    blocking: list[str] = []
    unused: list[str] = []
    for fid in nodes_failed:
        if re.search(rf"\b{re.escape(fid)}\b", blob):
            blocking.append(fid)
        else:
            unused.append(fid)
    return blocking, unused


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

    main_target_id = next(
        (nid for nid in blueprint.topo_order
         if blueprint.get_node(nid).is_main_target), None)
    with agent._run_codes_lock:
        run_codes = dict(agent._run_codes)
    blocking, unused = _split_unused_failures(
        main_target_id, nodes_proved, nodes_failed, run_codes)
    if unused:
        agent._log(verbose,
            f"  [unused] {len(unused)} failed node(s) never referenced by "
            f"the root proof — recorded as unused, not as failure(s): {unused}")

    lean_out_path, _, _ = agent._write_complete_proof_file(
        output_stem, parsed.name, nodes_proved, blocking, unused,
    )
    agent._log(verbose, f"[8/9] Formalization saved → {lean_out_path}")

    return FormalizationResult(
        theorem_name=parsed.name,
        status=_classify_final_status(main_target_id, nodes_proved, blocking),
        nodes_proved=nodes_proved,
        nodes_failed=blocking,
        error=None,
        dep_graph_path=dep_graph_path,
        session_state_path=session_state_path,
        nodes_unused=unused,
    )


# ---------------------------------------------------------------------------
# Stage 9 - Natural-language proof (Markdown, only on clean success)
# ---------------------------------------------------------------------------

_NL_PROOF_PROMPT = """You are a professional mathematician writing an informal, paper-style proof for a research paper. Write in clear, connected prose — not a tactic replay.

# Theorem
**Name:** `{name}`

**Hypotheses:**
{hyps_block}

**Conclusion:** {conclusion}

# Proof outline (the blueprint the formaliser followed)
{blueprint_outline}

# Verified Lean 4 proof (ground truth — do not describe any step not present here)
```lean
{lean_text}
```

# Output requirements
- Pure Markdown; use LaTeX (`$…$` inline, `$$…$$` display) for math
- Begin with a short **Statement.** paragraph restating the theorem in prose
- Then a **Proof.** section explaining the argument informally
- End with `∎` on its own line
- Do NOT invent steps that are not present in the Lean proof
- Do NOT include Lean syntax — the reader is a human, not a proof assistant
- Do NOT wrap the whole response in a code fence

Return only the markdown body; no preamble, no explanation of what you're about to write."""


def _step9_nl_proof(
    agent: "FormalizerAgent",
    parsed: "ParsedTheorem",
    blueprint: "Blueprint",
    output_stem: str,
    result: "FormalizationResult",
    verbose: bool,
) -> None:
    """Write an informal, paper-style Markdown proof next to the .lean file.

    Only runs when every blueprint node was proved AND every quality report
    passed — anything else would produce a .md that describes a proof that
    doesn't fully exist.  Silent no-op on failure (no partial artifact).
    """
    if result.status != "success":
        return
    with agent._run_codes_lock:
        qr_snapshot = dict(agent._run_quality_reports)
    if qr_snapshot and not all(qr.passed for qr in qr_snapshot.values()):
        return

    out_dir = agent._output_root / agent._proof_subdir / output_stem
    lean_path = out_dir / f"{output_stem}.lean"
    md_path = out_dir / f"{output_stem}.md"

    try:
        lean_text = lean_path.read_text(encoding="utf-8")
    except OSError as exc:
        agent._log(verbose, f"[9/9] Writing proof in natural language...")
        agent._log(verbose, f"  Skipped — cannot read {lean_path.name}: {exc}")
        return

    agent._log(verbose, "[9/9] Writing proof in natural language...")

    blueprint_outline = "\n".join(
        f"- **{n.node_id}** ({n.node_type}): {n.description}".rstrip()
        for n in blueprint.nodes
    ) or "(single-node proof — no decomposition)"
    hyps_block = "\n".join(f"- {h}" for h in parsed.hypotheses) or "- (none)"

    prompt = _NL_PROOF_PROMPT.format(
        name=parsed.name,
        hyps_block=hyps_block,
        conclusion=parsed.conclusion,
        blueprint_outline=blueprint_outline,
        lean_text=lean_text,
    )

    try:
        md_body = agent._sdk._call(
            prompt,
            model=agent._config.model_main,
            effort="medium",
            allowed_tools=[],
        )
    except Exception as exc:
        agent._log(verbose, f"  Skipped — LLM call failed: {exc}")
        return

    try:
        md_path.write_text(md_body.strip() + "\n", encoding="utf-8")
    except OSError as exc:
        agent._log(verbose, f"  Skipped — cannot write {md_path.name}: {exc}")
        return

    agent._log(verbose, "  Done!")
    agent._log(verbose, f"  Markdown saved → {md_path}")


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
    """Run the 9-stage prover pipeline on one pre-parsed conjecture.

    ``parsed`` comes from ``ParsedConjecture.to_parsed_theorem()`` (built
    upstream from a row of ``conjectures.json``).  ``output_stem`` is the
    stem of both artifacts — the run writes
    ``output/{agent._proof_subdir}/{output_stem}/{output_stem}.lean`` and
    (on a clean success) a sibling ``{output_stem}.md`` with an informal
    natural-language proof.

    Stages 1-5 (which call out to Claude + lake) are wrapped in a
    try/except so a crash still returns a structured FormalizationResult
    instead of propagating to the orchestrator.  Stages 6-8 run
    unconditionally on the success path and produce the final report;
    stage 9 (NL proof) only fires when every node proved AND every
    quality check passed.
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

    # Stages 6-9 must still return a structured FormalizationResult even if
    # one of them throws — otherwise callers (Orchestrator, run.py, tests) get
    # an unhandled exception instead of the "always returns a result" contract
    # that stages 1-5 uphold above.  Stage 9 in particular is best-effort and
    # already fails silent internally, but wrapping the whole tail is cheap.
    try:
        _step6_deep_check(agent, blueprint, locked, parsed, verbose)
        _step7_polib_repair(agent, verbose)
        result = _step8_collect_and_save(
            agent, parsed, blueprint, output_stem, verbose,
            nodes_proved, nodes_failed,
            dep_graph_path, session_state_path,
        )
    except Exception as exc:
        _collect_session_into(agent, blueprint, nodes_proved, nodes_failed)
        return _build_failed_result(
            agent, parsed, exc, nodes_proved, nodes_failed,
            dep_graph_path, session_state_path, include_traceback=True,
        )

    # Stage 9 is the natural-language proof writer.  If it throws (e.g. the
    # LLM SDK crashes in an unusual way not caught inside `_step9_nl_proof`),
    # the .lean is already saved and the run is materially a success — log
    # the exception and return the successful result rather than downgrading.
    try:
        _step9_nl_proof(agent, parsed, blueprint, output_stem, result, verbose)
    except Exception as exc:
        agent._log(True,
            f"[9/9] WARNING: NL proof step crashed — .lean is still saved. "
            f"({type(exc).__name__}: {exc})")
    return result
