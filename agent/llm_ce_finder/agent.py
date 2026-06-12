"""
agent/tools/llm_ce_finder_tool.py — LLM-based counterexample finder.

Asks Claude to generate p-vector candidates over multiple rounds.
Each round builds on failure history so the LLM converges on harder regions.

Standalone: can be run independently or embedded in the orchestrator pipeline.
"""
from __future__ import annotations

import json
import multiprocessing as _mp
import os
import re
import threading
import time
from concurrent.futures import ProcessPoolExecutor
from datetime import datetime, timezone
from typing import Optional

from agent.llm_ce_finder.prompts.llm_ce_finder import LLM_CE_SYSTEM, LLM_CE_ROUND_PROMPT
from agent.orchestrator.tools.pvec_eval import is_counterexample

_LLM_CE_TIMEOUT = int(os.environ.get("LLM_CE_TIMEOUT", "180"))
# Early-stop futility threshold: consecutive candidates that pass tiers 1-3
# (arithmetically valid violations) but fail Tier-4 construction. When the
# wall is realization rather than generation, more LLM rounds cannot help —
# the orchestrator's Stage-2 re-entry (fresh seeds, doubled budget) is the
# designated fallback. A Tier-4 success (witness built) resets the counter.
_LLM_CE_TIER4_FUTILE = int(os.environ.get("LLM_CE_TIER4_FUTILE", "12"))
# Circuit breaker: consecutive failed CLI calls (exit != 0 / timeout) before
# the LLM track declares itself dead for this conjecture. A dead CLI (auth,
# usage limit, session conflicts) otherwise burns every remaining round.
_LLM_CE_CALL_BREAKER = int(os.environ.get("LLM_CE_CALL_BREAKER", "3"))
# Extended-thinking effort for CE rounds. "low" is deliberate: candidates are
# cheap to verify locally (tiers 1-3 instant, tier 4 is the real gate), so
# breadth beats depth. Measured: default/inherited effort thought for >240s
# per round (every round timed out at 180s); low answers in ~9s.
_LLM_CE_EFFORT = os.environ.get("LLM_CE_EFFORT", "low")


# ── JSON extraction ───────────────────────────────────────────────────────────

def _extract_json_from_text(text: str) -> Optional[dict]:
    """Extract the first valid JSON object from an LLM response."""
    m = re.search(r'```(?:json)?\s*(\{[\s\S]*?\})\s*```', text)
    if m:
        try:
            return json.loads(m.group(1))
        except json.JSONDecodeError:
            pass

    start = text.find('{')
    if start == -1:
        return None
    depth = 0
    for i in range(start, len(text)):
        if text[i] == '{':
            depth += 1
        elif text[i] == '}':
            depth -= 1
            if depth == 0:
                try:
                    return json.loads(text[start:i + 1])
                except json.JSONDecodeError:
                    break
    return None


# ── LLM CE finder ─────────────────────────────────────────────────────────────

class LLMCEFinder:
    """Asks Claude to find counterexample p-vectors over multiple rounds.

    Each round receives:
      - the conjecture statement + hypotheses + conclusion
      - a deduped list of all previously tried p-vectors (capped at 50)
      - the last 5 failures with reasons

    Strong code-level guarantees:
      - Duplicates within a round are skipped before any check is run.
      - Duplicates across rounds are detected via a frozenset key set — the LLM
        cannot sneak a repeat through even if it ignores the "ALREADY TRIED" list.
    """

    def __init__(
        self,
        conjecture,               # ParsedConjecture
        client,                   # ClaudeSDKClient
        num_rounds: int = 30,
        stop_event: threading.Event | None = None,
        check_agent=None,         # PVectorCheckAgent, injected by orchestrator
        model: str | None = None, # override model (defaults to client.model)
    ) -> None:
        self.conjecture = conjecture
        self.client = client
        self.num_rounds = num_rounds
        self.stop_event = stop_event or threading.Event()
        self.check_agent = check_agent
        self.model = model or client.model
        self._check_parallel = max(1, int(os.environ.get("LLM_CE_CHECK_PARALLEL", "5")))
        self._pool: ProcessPoolExecutor | None = None

    # ── parallel tier-4 checking ──────────────────────────────────────────────

    def _check_batch(self, cands: list[dict], checker) -> list:
        """Check candidates' realizability concurrently (one process each).

        Tier 4 dominates a round's wall time (default 30s per candidate); a
        serial loop over 5 candidates costs ~150s while RL/Hopper saturate the
        CPU. One spawn worker per candidate cuts that to one timeout's worth.
        """
        if len(cands) <= 1 or self._check_parallel == 1:
            return [checker.run_silent(c, self.conjecture) for c in cands]
        from agent.orchestrator.tools.check_pvector import (
            check_pvector_worker, worker_setpgrp,
        )
        if self._pool is None:
            # spawn, not fork: the orchestrator runs LLM finders from worker
            # threads, and forking a threaded process can deadlock children.
            self._pool = ProcessPoolExecutor(
                max_workers=self._check_parallel,
                mp_context=_mp.get_context("spawn"),
                initializer=worker_setpgrp,
                initargs=(os.getpid(),),
            )
        n_par = min(len(cands), self._check_parallel)
        plantri_jobs = max(1, (os.cpu_count() or 4) // n_par)
        futs = [self._pool.submit(check_pvector_worker, c, self.conjecture,
                                  30.0, plantri_jobs) for c in cands]
        reports = []
        for fut, cand in zip(futs, cands):
            try:
                reports.append(fut.result())
            except Exception as exc:
                print(f"[LLM ce finding] parallel check failed for {cand} "
                      f"({exc}) — retrying serially")
                reports.append(checker.run_silent(cand, self.conjecture))
        return reports

    # ── main loop ─────────────────────────────────────────────────────────────

    def run(self) -> Optional[dict]:
        """Search for a CE. Returns CE info dict or None if exhausted."""
        try:
            return self._run_rounds()
        finally:
            if self._pool is not None:
                # kill worker process groups (worker + plantri children) so a
                # CE found elsewhere doesn't leave this pool holding the exit;
                # must run before shutdown(), which nulls the process table
                from agent.orchestrator.tools.check_pvector import kill_pool_pgroups
                kill_pool_pgroups(self._pool)
                self._pool.shutdown(wait=False, cancel_futures=True)
                self._pool = None

    def _run_rounds(self) -> Optional[dict]:
        print("[LLM ce finding] Start working ...")
        from agent.orchestrator.tools.check_pvector import PVectorCheckAgent
        checker = self.check_agent or PVectorCheckAgent(client=self.client)

        # Preflight: a dead CLI (usage limit, auth, network) makes every round
        # burn its full timeout before the call breaker fires (3 × 360s). One
        # tiny call decides within a minute whether the track is worth running.
        preflight_timeout = int(os.environ.get("LLM_CE_PREFLIGHT_TIMEOUT", "60"))
        try:
            self.client._call("Reply with the single word OK.",
                              model=self.model, timeout=preflight_timeout,
                              stop_event=self.stop_event, max_attempts=1,
                              effort=_LLM_CE_EFFORT)
        except Exception as exc:
            print(f"[LLM ce finding] disabled — CLI preflight failed ({exc}); "
                  f"RL/Hopper/constructor tracks continue")
            return None

        failed: list[dict] = []
        all_tried: list[dict] = []
        tried_keys: set[frozenset] = set()
        tier4_deaths = 0  # consecutive tier-4-only failures (futility signal)
        consec_call_errors = 0  # consecutive CLI call failures (breaker)

        # Progress is summarised once every 3 rounds (window aggregation)
        window_new = 0
        window_dupes = 0
        window_violations = 0
        window_best_passed = -1
        window_best_tier: int | None = None

        for rnd in range(1, self.num_rounds + 1):
            if self.stop_event.is_set():
                print("[LLM ce finding] stopped — CE search settled by another track")
                return None

            try:
                prompt = self._build_prompt(rnd, failed, all_tried)
                full_prompt = f"[System]\n{LLM_CE_SYSTEM}\n\n[User]\n{prompt}"
                # Single attempt per round (failures just move to the next
                # round). The prompt demands silent verification + a ≤3-sentence
                # reasoning field, so a round is normally ~80s; the 180s default
                # is headroom for API latency spikes, not the expected cost.
                text = self.client._call(full_prompt, model=self.model,
                                         timeout=_LLM_CE_TIMEOUT,
                                         stop_event=self.stop_event, max_attempts=1,
                                         effort=_LLM_CE_EFFORT)
            except Exception as exc:
                consec_call_errors += 1
                print(f"[LLM ce finding] Round {rnd}/{self.num_rounds}: skipping ({exc})")
                if consec_call_errors >= _LLM_CE_CALL_BREAKER:
                    print(f"[LLM ce finding] {consec_call_errors} consecutive CLI "
                          f"failures — LLM track disabled for this conjecture "
                          f"(RL/Hopper continue; Stage 2 re-entry still runs)")
                    return None
                continue

            if self.stop_event.is_set():
                print("[LLM ce finding] stopped — CE search settled by another track")
                return None

            consec_call_errors = 0
            candidates = self._parse_candidates(text)
            skipped_dupes = 0
            best_passed_count = -1   # max checks passed by any violating candidate
            best_fail_tier = None    # 1-indexed tier that failed on the best candidate

            # Instant arithmetic filtering first; the surviving violators go
            # to the expensive tier-4 realizability checks as a parallel batch.
            to_check: list[tuple[int, dict, str]] = []
            for idx, cand in enumerate(candidates):
                # Hard dedup — LLM cannot repeat even if it ignores the prompt.
                cand_key = frozenset(cand.items())
                if cand_key in tried_keys:
                    skipped_dupes += 1
                    continue
                tried_keys.add(cand_key)
                all_tried.append(cand)

                ok, detail = is_counterexample(cand, self.conjecture)
                if not ok:
                    failed.append({"p_vec": cand, "reason": detail})
                    continue
                to_check.append((idx, cand, detail))

            violations_this_round = len(to_check)
            reports = self._check_batch([c for _, c, _ in to_check], checker)

            for (idx, cand, detail), report in zip(to_check, reports):
                if report.all_passed:
                    print(f"\n[LLM ce finding] Round {rnd}/{self.num_rounds}: CE found❗ — {cand} — {detail}\n")
                    report.print()
                    print(f"[LLM ce finding] 5 checks passed, CE is valid √")
                    return {
                        "p_vector": cand,
                        "found_by": "llm ce finder",
                        "found_at_round": rnd,
                        "violation_detail": detail,
                        "other_candidates_not_checked": candidates[idx + 1:],
                        "found_at": datetime.now(timezone.utc).isoformat(),
                        "witness_edges": report.witness_edges,
                    }

                # Track the best check result for the round summary
                passed_count = sum(1 for r in report.results if r.passed)
                if passed_count > best_passed_count:
                    best_passed_count = passed_count
                    best_fail_tier = next(
                        (i + 1 for i, r in enumerate(report.results) if not r.passed),
                        None,
                    )

                # Futility tracking: tiers 1-3 passed but the constructor
                # built nothing → the wall is realization, not generation.
                realiz = report.results[3] if len(report.results) > 3 else None
                if realiz is not None and all(r.passed for r in report.results[:3]):
                    if realiz.passed:
                        tier4_deaths = 0
                    elif realiz.critical:
                        tier4_deaths += 1

                failed.append({
                    "p_vec": cand,
                    "reason": f"realizability unproven: {report.failure_summary()}",
                })

            if tier4_deaths >= _LLM_CE_TIER4_FUTILE:
                print(f"[LLM ce finding] Round {rnd}/{self.num_rounds}: early stop — "
                      f"{tier4_deaths} consecutive candidate(s) passed tiers 1-3 but "
                      f"failed Tier-4 construction; realization (not generation) is "
                      f"the bottleneck — deferring to Stage 2 re-entry")
                return None

            window_new += len(candidates) - skipped_dupes
            window_dupes += skipped_dupes
            window_violations += violations_this_round
            if best_passed_count > window_best_passed:
                window_best_passed = best_passed_count
                window_best_tier = best_fail_tier

            if rnd % 3 == 0 or rnd == self.num_rounds:
                dupe_note = f", {window_dupes} dupe(s) skipped" if window_dupes else ""
                if window_violations > 0:
                    if window_best_tier is not None and window_best_passed > 0:
                        check_note = (
                            f"tier1-{window_best_tier - 1} passed, tier {window_best_tier} didn't"
                            if window_best_tier > 1
                            else f"tier {window_best_tier} didn't pass"
                        )
                    else:
                        check_note = "0 of 4 checks passed"
                    print(f"[LLM ce finding] Round {rnd}/{self.num_rounds}: "
                          f"{window_new} candidate(s), 0 valid, {check_note}{dupe_note} — next round")
                else:
                    print(f"[LLM ce finding] Round {rnd}/{self.num_rounds}: "
                          f"{window_new} candidate(s), 0 valid{dupe_note} — next round")
                window_new = window_dupes = window_violations = 0
                window_best_passed = -1
                window_best_tier = None

            failed = failed[-10:]
            all_tried = all_tried[-50:]

        print(f"[LLM ce finding] Exhausted {self.num_rounds} rounds without a CE.")
        return None

    # ── helpers ───────────────────────────────────────────────────────────────

    def _build_prompt(self, rnd: int, failed: list[dict], all_tried: list[dict]) -> str:
        hyp_block = "\n".join(
            f"  - {h}" for h in self.conjecture.hypotheses
        ) or "  (none)"

        lines: list[str] = []

        if all_tried:
            lines.append(
                f"ALREADY TRIED — do NOT repeat any of these {len(all_tried)} p-vectors:"
            )
            for pv in all_tried:
                lines.append(f"  {pv}")
            lines.append("")

        if failed:
            lines.append("Recent failures (last 5) with reasons:")
            for fa in failed[-5:]:
                lines.append(f"  {fa['p_vec']} → {fa['reason']}")
            lines.append("")

        prev_block = ("\n".join(lines) + "\n") if lines else ""

        return LLM_CE_ROUND_PROMPT.format(
            cid=self.conjecture.conjecture_id,
            statement=self.conjecture.statement_latex,
            hyp_block=hyp_block,
            conclusion=self.conjecture.conclusion,
            prev_block=prev_block,
        )

    def _parse_candidates(self, text: str) -> list[dict[int, int]]:
        data = _extract_json_from_text(text)
        if not data:
            return []
        results: list[dict[int, int]] = []
        for c in data.get("candidates", []):
            if not isinstance(c, dict):
                continue
            p_vec: dict[int, int] = {}
            for key, val in c.items():
                m = re.match(r'p(\d+)', str(key))
                if m and isinstance(val, (int, float)) and val >= 0:
                    p_vec[int(m.group(1))] = int(val)
            if p_vec:
                results.append(p_vec)
        return results
