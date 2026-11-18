#!/usr/bin/env python3
"""F2b-llm_direct per-arm driver. K=2 generations of (generate -> downstream ->
status write) inside one isolated llm_direct arm workspace (cwd == arm dir).

Same shape as the F2b driver (f2b_driver.py), with exactly two differences:
  1. llm_propose_n is set PER GENERATION to the closed arm's pre-gate evaluated
     candidate count for the same seed+generation (the cap, read from
     scripts/ldno/f2b_caps.json, which is derived from the committed F2b results
     at 314ed95). The LLM is the only source (sources turned off in setup), so
     this caps the candidate budget at what the closed arm evaluated.
  2. An infra failure in the single propose call (API error / rate-limit /
     timeout / empty-or-truncated response — surfaced as a RuntimeError by the
     patched _llm_propose) aborts the arm with a non-zero exit so the run script
     reruns the seed from scratch. A valid-but-short response is NOT a failure;
     it is recorded as shortfall by the propose instrumentation.

Downstream is deterministic B (witness-pool replay -> plantri-pool replay ->
Eberhard-lattice walk -> plantri exhaustive screen), client=None, no RL/LLM/
Hopper/constructor, prover disabled — a verbatim replica of the F2b driver's
_downstream_B. No agent code is modified here.

Usage (cwd == arm_dir):
  python3 f2b_llmdirect_driver.py --seed 41 --k 2 --caps /path/to/f2b_caps.json
"""
import os, sys, time, json, argparse, threading

sys.path.insert(0, os.getcwd())  # resolve `agent` to this isolated arm copy

from agent.conjecture_generator import ConjectureGenerator
from agent.orchestrator.orchestrator import (
    Orchestrator, PVectorCEFinder, _write_ce_json, _eval_conclusion_violated,
)
from agent.orchestrator.tools.check_pvector import PVectorCheckAgent
from agent.plantri_ce_finder.agent import PlantriCEFinder
from agent.orchestrator.tools.conjecture_parser import ParsedConjecture
from agent.conjectures import get_conjectures_by_status, set_conjecture_status

EXIT_INFRA = 3  # non-zero exit signalling an infra crash (rerun the seed)


def _pv_jsonable(pv):
    if isinstance(pv, dict):
        return {str(k): v for k, v in pv.items()}
    return None


def _downstream_B(orch, pc):
    """Deterministic CE search (verbatim replica of F2b driver _downstream_B /
    orchestrator._run_ce_search lines 976-1026 minus the RL/LLM/Hopper/constructor
    parallel tracks). Finders use client=None — no API, fully deterministic."""
    pool_ce = orch._replay_witness_pool(pc)
    if pool_ce:
        return pool_ce
    plantri_pool_ce = orch._replay_plantri_pool(pc)
    if plantri_pool_ce:
        return plantri_pool_ce
    pvec_result = PVectorCEFinder(
        conjecture=pc, num_steps=200_000, num_restarts=60,
        stop_event=threading.Event(),
    ).run()
    if pvec_result:
        p_vec = pvec_result["p_vector"]
        _, detail = _eval_conclusion_violated(pc.conclusion, p_vec)
        report = PVectorCheckAgent(client=None).run(p_vec, pc)
        if report.all_passed:
            pvec_result["violation_detail"] = detail
            pvec_result["witness_edges"] = report.witness_edges
            try:
                _write_ce_json(pc, pvec_result, orch._ce_dir)
                pvec_result["json_written"] = True
            except Exception as exc:
                print(f"[Output] warning: could not write CE JSON: {exc}", flush=True)
            return pvec_result
    plantri_finder = PlantriCEFinder(pc, client=None)
    enum_ce, _survivors = plantri_finder.screen()
    if enum_ce:
        try:
            _write_ce_json(pc, enum_ce, orch._ce_dir)
            enum_ce["json_written"] = True
        except Exception as exc:
            print(f"[Output] warning: could not write CE JSON: {exc}", flush=True)
        return enum_ce
    return None  # survivor (no deterministic CE)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--seed", type=int, required=True)
    ap.add_argument("--k", type=int, default=2)
    ap.add_argument("--caps", required=True)
    args = ap.parse_args()

    caps = json.load(open(args.caps))["caps"][str(args.seed)]
    orch = Orchestrator()
    t0 = time.time()
    for G in range(1, args.k + 1):
        cap = int(caps[str(G)])
        gsep = "=" * 70
        print(f"\n{gsep}\n[llm_direct] Generation {G}/{args.k} "
              f"(seed={args.seed}, llm_propose_n cap={cap}, downstream=B)\n{gsep}",
              flush=True)
        tgen = time.time()
        try:
            ConjectureGenerator(
                client=orch.client,
                limit=0,                        # no cap on the hard filter
                g3_mode="fast",
                llm_propose_n=cap,              # [llm_direct] per-gen candidate cap
                propose_model=orch.config.model_fast,
                review_model=orch.config.model_main,
            ).run()
        except Exception as exc:
            # The only source is the LLM; a propose infra failure (RuntimeError
            # from the patched _llm_propose) zeros the generation -> crash/rerun.
            print(f"[llm_direct] GENERATION {G} ABORTED (infra failure): {exc}",
                  flush=True)
            print("[llm_direct] exiting non-zero so the run script reruns this seed",
                  flush=True)
            sys.exit(EXIT_INFRA)
        print(f"[llm_direct] gen{G} generation wall={time.time()-tgen:.1f}s", flush=True)

        new_specs = get_conjectures_by_status("new")
        print(f"[llm_direct] gen{G}: {len(new_specs)} new conjecture(s) -> downstream",
              flush=True)
        refuted = survivors = 0
        for spec in new_specs:
            pc = ParsedConjecture.from_conjecture_spec(spec)
            td = time.time()
            try:
                ce = _downstream_B(orch, pc)
            except Exception as exc:
                print(f"[llm_direct] downstream error {spec.name}: {exc}", flush=True)
                ce = None
            dt = time.time() - td
            if ce:
                set_conjecture_status(spec.name, "refuted",
                                      detail={"ce_p_vector": _pv_jsonable(ce.get("p_vector")),
                                              "violation": ce.get("violation_detail", "")})
                refuted += 1
                verdict = f"REFUTED by {ce.get('found_by','?')}"
            else:
                set_conjecture_status(spec.name, "prover_failed",
                                      detail={"outcome": "survivor_prover_disabled"})
                survivors += 1
                verdict = "SURVIVOR"
            print(f"[llm_direct] gen{G} {spec.name}: {verdict}  ({dt:.1f}s)", flush=True)
        print(f"[llm_direct] gen{G} downstream done: {refuted} refuted, "
              f"{survivors} survivors", flush=True)
    print(f"\n[llm_direct] ARM COMPLETE K={args.k} total_wall={time.time()-t0:.1f}s",
          flush=True)


if __name__ == "__main__":
    main()
