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
        from agent.orchestrator.tools.check_pvector import PVectorCheckAgent
        checker = self.check_agent or PVectorCheckAgent(client=self.client)

        failed: list[dict] = []
        all_tried: list[dict] = []
        tried_keys: set[frozenset] = set()

        for rnd in range(1, self.num_rounds + 1):
            if self.stop_event.is_set():
                print("[LLM ce finding] Stopped and waiting ce candidate to be checked")
                return None

            try:
                prompt = self._build_prompt(rnd, failed, all_tried)
                full_prompt = f"[System]\n{LLM_CE_SYSTEM}\n\n[User]\n{prompt}"
                text = self.client._call(full_prompt, model=self.model, timeout=300,
                                         stop_event=self.stop_event)
            except Exception as exc:
                print(f"[LLM ce finding] Round {rnd}/{self.num_rounds}: skipping ({exc})")
                continue

            if self.stop_event.is_set():
                print("[LLM ce finding] Stopped and waiting ce candidate to be checked")
                return None

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
                    print(f"[LLM ce finding] Round {rnd}/{self.num_rounds}: CE found — {cand} — {detail}")
                    report.print()
                    return {
                        "p_vector": cand,
                        "found_by": "llm_finder",
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

                failed.append({
                    "p_vec": cand,
                    "reason": f"realizability unproven: {report.failure_summary()}",
                })

            dupe_note = f", {skipped_dupes} dupe(s) skipped" if skipped_dupes else ""
            new_count = len(candidates) - skipped_dupes
            if violations_this_round > 0:
                if best_fail_tier is not None and best_passed_count > 0:
                    check_note = (
                        f"tier1-{best_fail_tier - 1} passed, tier {best_fail_tier} didn't"
                        if best_fail_tier > 1
                        else f"tier {best_fail_tier} didn't pass"
                    )
                else:
                    check_note = "0 of 4 checks passed"
                print(f"[LLM ce finding] Round {rnd}/{self.num_rounds}: "
                      f"{new_count} candidate(s), 0 valid, {check_note}{dupe_note} — next round")
            else:
                print(f"[LLM ce finding] Round {rnd}/{self.num_rounds}: "
                      f"{new_count} candidate(s), 0 valid{dupe_note} — next round")

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
