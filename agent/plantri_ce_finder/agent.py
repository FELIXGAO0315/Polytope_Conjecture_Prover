"""
agent/plantri_ce_finder/agent.py — plantri-led counterexample finder.

plantri (exhaustive enumeration of all polytope graphs with a given face
count) is the project's realizability oracle: within its reach
(PLANTRI_F2_MAX / PLANTRI_F2_MAX_M5) its verdicts are final in BOTH
directions. This finder runs the whole plantri-led CE search under one log
tag, in two roles:

  [plantri ce finding] plantri:      the exhaustive screen — analytic
      constructions first (known families / prisms, instant), then plantri
      enumeration of every arithmetic CE candidate within reach. A realizable
      candidate becomes a validated CE; an exhausted enumeration proves the
      candidate non-realizable, permanently (cached).

  [plantri ce finding] constructor:  the double check — candidates beyond
      exhaustive reach get exactly one stochastic construction attempt each
      (PolytopeConstructor). One-sided: a successful build is a verified CE
      with a witness graph; a failed build proves nothing. Every attempt is
      recorded in output/realizability_cache.json and seeds are salted with
      the cached attempt count, so the next program run draws fresh
      trajectories instead of replaying old ones.

A completed double check settles every IN-BOUNDS candidate, but it does not
stop the sibling tracks: LLM/RL/Hopper can propose p-vectors outside the
enumeration bounds, so they run out their own budgets before the orchestrator
concludes "no CE". Only a found CE aborts everyone.

Standalone: can be run independently or embedded in the orchestrator pipeline.
"""
from __future__ import annotations

import multiprocessing as _mp
import os
import threading
import time
import zlib
from concurrent.futures import FIRST_COMPLETED, ProcessPoolExecutor, wait as _fut_wait
from datetime import datetime, timezone
from typing import Optional

from agent.orchestrator.tools.check_pvector import (
    PVectorCheckAgent, check_pvector_worker, kill_pool_pgroups, worker_setpgrp,
)
from agent.orchestrator.tools.polytope_constructor import _cache_key, _failure_get
from agent.orchestrator.tools.pvec_eval import _eval_conclusion_violated

TAG = "[Plantri ce finding]"


def _nz(cand) -> dict[int, int]:
    return {k: v for k, v in cand.p_vec.items() if v > 0}


def _seed(cand) -> int:
    # Salted with the attempt count recorded in the realizability cache, so a
    # fresh program run draws a provably different trajectory than the last
    # one. (Still deterministic given the same cache state.)
    rec = _failure_get(_nz(cand))
    attempts = rec[1] if rec else 0
    key = f"{_cache_key(_nz(cand))}#a{attempts}"
    return zlib.crc32(key.encode()) & 0x7FFFFFFF


class PlantriCEFinder:
    """plantri-led CE search: decisive screen + one constructor double check.

    screen()        decides every candidate within exhaustive reach (final
                    verdicts, cached) and returns the undecided survivors.
    double_check()  gives each survivor one construction attempt; returns a
                    CE dict on success, None after a full sweep without one.
    """

    def __init__(
        self,
        conjecture,               # ParsedConjecture
        client=None,              # ClaudeSDKClient, optional (checker only)
        stop_event=None,          # threading.Event or _mp.Event
    ) -> None:
        self.conjecture = conjecture
        self.client = client
        self.stop_event = stop_event or threading.Event()

    # ── role 1: exhaustive screen (plantri proper — decisive, no API) ─────────

    def screen(self) -> tuple[Optional[dict], list]:
        """Exhaustive screen of all arithmetic CE candidates within reach.

        Phase 0  analytic constructions (known families / prisms) — instant.
        Phase 1  plantri exhaustive screen over ALL candidates: min-deg-5
                 candidates are decided in batched multi-target sweeps (one
                 shared generation tree per f2 value); the rest get budgeted
                 per-candidate decisions. Verdicts are final and cached.

        Returns (ce_info, survivors): either a validated CE, or the list of
        undecided candidates for double_check() to attack stochastically.
        Screen timeouts are recorded in the cache (timeout_used) so the
        plantri-decision stage never retries at a weaker budget.
        """
        from agent.orchestrator.tools.ce_enumerator import enumerate_ce_candidates
        from agent.orchestrator.tools.polytope_constructor import (
            plantri_screen_batch, _build_known, _build_prism, _plantri_decide,
            _pvec_of, _disk_merge,
        )

        print(f"{TAG} Start working ...")
        tag = f"{TAG} plantri:"
        conjecture = self.conjecture

        try:
            candidates = enumerate_ce_candidates(conjecture)
        except Exception as exc:
            print(f"{TAG} enumerator error: {exc} — skipping")
            return None, []
        if not candidates:
            print(f"{TAG} No arithmetic CE candidate exists within bounds — "
                  "conjecture is arithmetically tight in this region.")
            return None, []

        checker = (PVectorCheckAgent(client=self.client) if self.client
                   else PVectorCheckAgent())

        def _ce_record(cand, report, method: str, round_i: int) -> dict:
            _, detail = _eval_conclusion_violated(conjecture.conclusion, cand.p_vec)
            print(f"\n{tag} CE found❗ ({method}): {cand.p_vec}\n")
            report.print()
            print(f"{tag} 5 checks passed, CE is valid √")
            return {
                "p_vector": cand.p_vec,
                "found_by": "plantri ce finder",
                "found_at_round": round_i,
                "violation_detail": detail,
                "witness_edges": report.witness_edges,
            }

        def _validated(cand, graph, method: str, round_i: int) -> Optional[dict]:
            report = checker.run_silent(cand.p_vec, conjecture, witness_graph=graph)
            if report.all_passed:
                return _ce_record(cand, report, method, round_i)
            print(f"{tag} {method} witness for {cand.p_vec} failed validation: "
                  f"{report.failure_summary()}")
            return None

        def _note_plantri_timeout(pv: dict[int, int], spent: float) -> None:
            """Record an undecided plantri attempt in the shared cache so the
            decision stage's quick phase never retries at a budget <= one that
            already failed. Final verdicts are never overwritten."""
            key = ",".join(f"{k}:{v}" for k, v in sorted(pv.items()))

            def _entry(existing):
                if existing and existing.get("verdict") in ("realizable", "non_realizable"):
                    return None
                old = float(existing.get("timeout_used", 0.0)) if existing else 0.0
                if spent <= old:
                    return None
                e = dict(existing) if existing else {"verdict": "timeout", "count": -1}
                e["timeout_used"] = round(spent, 1)
                return e

            _disk_merge(key, _entry)

        t_start = time.time()

        # ── Phase 0: analytic constructions (pure Python, instant) ────────────
        for i, cand in enumerate(candidates, 1):
            nz = _nz(cand)
            G = _build_known(nz)
            if G is None:
                G = _build_prism(nz)
                if G is not None and _pvec_of(G) != nz:
                    G = None
            if G is not None:
                ce = _validated(cand, G, "analytic", i)
                if ce:
                    return ce, []

        # ── Phase 1: exhaustive plantri screen over EVERY candidate ───────────
        f2cap_m5 = int(os.environ.get("PLANTRI_F2_MAX_M5", "36"))
        f2cap_ad = int(os.environ.get("PLANTRI_F2_MAX", "26"))
        by_n: dict[int, list] = {}
        ad_list, unreachable = [], []
        for cand in candidates:
            nz = _nz(cand)
            n = sum(nz.values())
            if nz and min(nz) >= 5 and 4 <= n <= f2cap_m5 and max(nz) <= n - 1:
                by_n.setdefault(n, []).append(cand)
            elif nz and 4 <= n <= f2cap_ad and max(nz) <= n - 1:
                ad_list.append(cand)
            else:
                unreachable.append(cand)

        print(f"{tag} {len(candidates)} candidate p-vector(s) satisfy the "
              f"arithmetic constraints. Exhaustive enumeration can decide "
              f"{sum(len(g) for g in by_n.values()) + len(ad_list)} of "
              f"them directly; {len(unreachable)} have too many faces to "
              f"enumerate exhaustively.")

        batch_timeout = float(os.environ.get("CE_SCREEN_BATCH_TIMEOUT", "90"))
        screen_jobs = int(os.environ.get("CE_SCREEN_JOBS", "0")) or None
        n_nonreal = 0
        undecided: set = set()

        for n in sorted(by_n):
            group = by_n[n]
            res = plantri_screen_batch(
                [c.p_vec for c in group], timeout=batch_timeout,
                jobs=screen_jobs, stop_on_first=True)
            for cand in group:
                verdict, G = res.get(_cache_key(_nz(cand)), ("timeout", None))
                if verdict == "realizable":
                    ce = _validated(cand, G, f"plantri_batch_f2={n}", n)
                    if ce:
                        return ce, []
                    undecided.add(_cache_key(_nz(cand)))
                elif verdict == "nonrealizable":
                    n_nonreal += 1
                else:
                    undecided.add(_cache_key(_nz(cand)))
                    _note_plantri_timeout(_nz(cand), batch_timeout)

        ad_budget = float(os.environ.get("CE_SCREEN_AD_BUDGET", "240"))
        ad_per = float(os.environ.get("CE_SCREEN_AD_TIMEOUT", "20"))
        t_ad = time.time()
        for i, cand in enumerate(ad_list):
            if time.time() - t_ad > ad_budget:
                undecided.update(_cache_key(_nz(c)) for c in ad_list[i:])
                break
            nz = _nz(cand)
            G, verdict = _plantri_decide(nz, timeout=ad_per, jobs=screen_jobs)
            if verdict == "realizable" and G is not None and _pvec_of(G) == nz:
                ce = _validated(cand, G, "plantri_single", i + 1)
                if ce:
                    return ce, []
                undecided.add(_cache_key(nz))
            elif verdict == "nonrealizable":
                n_nonreal += 1
            else:
                undecided.add(_cache_key(nz))
                _note_plantri_timeout(nz, ad_per)

        undecided.update(_cache_key(_nz(c)) for c in unreachable)
        survivors = [c for c in candidates if _cache_key(_nz(c)) in undecided]
        t_screen = time.time() - t_start

        if not survivors:
            print(f"{tag} screen decided every candidate: {n_nonreal} "
                  f"non-realizable (proof by exhaustion), 0 undecided "
                  f"({t_screen:.0f}s) — no realizable CE exists in this region.")
            return None, []

        print(f"{tag} exhaustive enumeration finished ({t_screen:.0f}s): "
              f"{n_nonreal} candidate(s) proven non-realizable; "
              f"{len(survivors)} remain undecided → constructor double check.")
        return None, survivors

    # ── role 2: constructor double check (stochastic, one-sided) ──────────────

    def double_check(self, survivors: list, stop_event=None) -> Optional[dict]:
        """Give every screen survivor one construction attempt.
        Returns CE info dict, or None after a full sweep without one."""
        tag = f"{TAG} constructor:"
        stop = stop_event or self.stop_event
        if int(os.environ.get("CE_ENUM_REALIZE_MAX", "40")) == 0:
            print(f"{tag} disabled (CE_ENUM_REALIZE_MAX=0)")
            return None
        if not survivors:
            return None
        timeout = float(os.environ.get("CE_ENUM_REALIZE_TIMEOUT", "90"))
        pool = max(1, int(os.environ.get("CE_ENUM_REALIZE_PARALLEL", "4")))

        n_surv = len(survivors)
        milestones = {m for m in (n_surv // 3, (2 * n_surv) // 3) if 0 < m < n_surv}
        done = 0
        t_start = time.time()
        print(f"{tag} trying to build a polytope for each of {n_surv} "
              f"undecided candidate(s) ({timeout:.0f}s per attempt)...",
              flush=True)

        # Partition CPU with the LLM track's tier-4 check pool, which runs
        # concurrently — pool sizes × per-worker plantri splits ≈ cores.
        llm_par = max(1, int(os.environ.get("LLM_CE_CHECK_PARALLEL", "5")))
        plantri_jobs = max(1, (_mp.cpu_count() or 4) // (pool + llm_par))

        # Least-attempted candidates first, so the ones nobody ever tried get
        # their shot before the long-shot retries.
        survivors.sort(key=lambda c: (_failure_get(_nz(c)) or (0.0, 0))[1])

        # spawn, not fork: batch mode runs this from one of 7 worker threads,
        # and forking a threaded process can deadlock children.
        ex = ProcessPoolExecutor(
            max_workers=pool, mp_context=_mp.get_context("spawn"),
            initializer=worker_setpgrp, initargs=(os.getpid(),))
        try:
            futs = {
                ex.submit(check_pvector_worker, cand.p_vec, self.conjecture,
                          timeout, plantri_jobs, _seed(cand)): cand
                for cand in survivors
            }
            pending = set(futs)
            while pending:
                # Short-timeout wait instead of as_completed: a CE found by
                # another track must abort this thread within seconds, not
                # after the next in-flight candidate times out.
                if stop.is_set():
                    return None
                finished, pending = _fut_wait(
                    pending, timeout=5, return_when=FIRST_COMPLETED)
                for fut in finished:
                    cand = futs[fut]
                    done += 1
                    try:
                        report = fut.result()
                    except Exception as exc:
                        print(f"{tag} worker error on {cand.p_vec}: {exc}")
                        continue
                    if report.all_passed:
                        _, detail = _eval_conclusion_violated(
                            self.conjecture.conclusion, cand.p_vec)
                        print(f"\n{tag} CE found❗ ({done}/{n_surv}): {cand.p_vec}\n")
                        report.print()
                        print(f"{tag} 5 checks passed, CE is valid √")
                        return {
                            "p_vector": cand.p_vec,
                            "found_by": "plantri ce finder",
                            "found_at_round": done,
                            "violation_detail": detail,
                            "found_at": datetime.now(timezone.utc).isoformat(),
                            "witness_edges": report.witness_edges,
                        }
                    if done in milestones:
                        print(f"{tag} {done}/{n_surv} candidate(s) attempted, "
                              f"none realized so far "
                              f"({time.time() - t_start:.0f}s elapsed)",
                              flush=True)

            print(f"{TAG} double check over — all {n_surv} candidate(s) "
                  f"attempted, no CE found "
                  f"({time.time() - t_start:.0f}s, results cached).")
            return None
        finally:
            # On early CE success (ours or another track's), in-flight workers
            # are useless work — end them immediately instead of holding the
            # interpreter exit.
            kill_pool_pgroups(ex)   # before shutdown: it nulls _processes
            ex.shutdown(wait=False, cancel_futures=True)
