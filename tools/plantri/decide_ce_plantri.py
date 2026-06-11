"""Exhaustively decide realizability of a conjecture's arithmetic CE candidates
using plantri (Brinkmann & McKay) with the allowed_deg plugin.

For each candidate p-vector, the dual simplicial polytope is a sphere
triangulation whose vertex-degree multiset equals the p-vector. plantri
enumerates ALL such triangulations (isomorph-free, exhaustive), so:

    count > 0  →  candidate is REALIZABLE  → verified counterexample exists
    count = 0  →  candidate is NON-REALIZABLE (proof by exhaustion)

This is a decision procedure, not a heuristic. Verdicts are printed as they
arrive.

Usage:
    python tools/plantri/decide_ce_plantri.py [--name auto_..._2] [--f2-max 24]
        [--timeout-per 3600] [--jobs 16]

Candidates are processed cheapest-first (fewest low-degree dual vertices).
Each candidate is split into --jobs parallel plantri parts (res/mod).
"""

from __future__ import annotations

import argparse
import subprocess
import sys
import time
from pathlib import Path

_PROJECT_ROOT = Path(__file__).resolve().parent.parent.parent
sys.path.insert(0, str(_PROJECT_ROOT))

PLANTRI_AD = Path(__file__).resolve().parent / "plantri_ad"


def spec_for(p_vec: dict[int, int]) -> str:
    """plantri_ad -F switch string: exact count for every degree in support."""
    return "".join(f"F{k}_{v}^{v}" for k, v in sorted(p_vec.items()))


def _kill_all(procs) -> None:
    for p in procs:
        try:
            p.kill()
            p.wait(timeout=5)
        except Exception:
            pass


def decide(
    p_vec: dict[int, int], jobs: int, timeout: float, stop_event=None
) -> tuple[str, int, float]:
    """Return (verdict, count, seconds).
    verdict ∈ realizable|non_realizable|timeout|stopped|error.
    `stop_event` (threading.Event, optional) aborts the decision early —
    set by the orchestrator to kill sibling decisions once a CE is found."""
    n = sum(p_vec.values())
    switch = "-" + spec_for(p_vec)
    t0 = time.time()
    procs = []
    try:
        # spawn inside the try block: a failure mid-spawn (e.g. ENOMEM) must
        # still kill the processes already started
        for r in range(jobs):
            procs.append(subprocess.Popen(
                [str(PLANTRI_AD), switch, str(n), f"{r}/{jobs}", "-u"],
                stdout=subprocess.DEVNULL, stderr=subprocess.PIPE, text=True,
            ))
        # poll loop so we can honor both the timeout and the stop_event
        while any(p.poll() is None for p in procs):
            if stop_event is not None and stop_event.is_set():
                _kill_all(procs)
                return "stopped", -1, time.time() - t0
            if time.time() - t0 > timeout:
                _kill_all(procs)
                return "timeout", -1, time.time() - t0
            time.sleep(0.25)
        total = 0
        for p in procs:
            _, err = p.communicate()
            for line in err.splitlines():
                if "triangulations generated" in line:
                    total += int(line.split()[0])
                    break
            else:
                if p.returncode != 0:
                    raise RuntimeError(err.strip()[:200])
    except Exception as exc:
        _kill_all(procs)
        print(f"    error: {exc}")
        return "error", -1, time.time() - t0
    verdict = "realizable" if total > 0 else "non_realizable"
    return verdict, total, time.time() - t0


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--name", default="auto_20260310_142638_2")
    ap.add_argument("--f2-max", type=int, default=24)
    ap.add_argument("--timeout-per", type=float, default=3600.0)
    ap.add_argument("--jobs", type=int, default=16)
    args = ap.parse_args()

    from agent.conjectures import load_conjectures
    from agent.orchestrator.tools.conjecture_parser import ParsedConjecture
    from agent.orchestrator.tools.ce_enumerator import enumerate_ce_candidates

    specs = load_conjectures()
    spec = next((s for s in specs if s.name == args.name), None)
    if spec is None:
        sys.exit(f"conjecture {args.name!r} not found")
    conj = ParsedConjecture.from_conjecture_spec(spec)
    cands = [c for c in enumerate_ce_candidates(conj) if c.f2 <= args.f2_max]
    # cheapest first: few low-degree (3/4) dual vertices explode the search least
    cands.sort(key=lambda c: (c.p_vec.get(3, 0) + c.p_vec.get(4, 0), c.f2))
    print(f"{len(cands)} candidates with f2 <= {args.f2_max} "
          f"(jobs={args.jobs}, timeout {args.timeout_per:.0f}s each)")

    results: list[dict] = []
    for i, c in enumerate(cands, 1):
        print(f"[{i}/{len(cands)}] {c.p_vec} (f2={c.f2}) ...", flush=True)
        verdict, count, secs = decide(c.p_vec, args.jobs, args.timeout_per)
        print(f"    {verdict.upper()} (count={count}) in {secs:.0f}s")
        results.append({"verdict": verdict})
        if verdict == "realizable":
            print("\n*** REALIZABLE CANDIDATE FOUND — the conjecture is REFUTED. ***")
            print("*** Re-run with plantri output enabled to extract the witness graph. ***")
            break

    n_non = sum(1 for r in results if r["verdict"] == "non_realizable")
    n_to = sum(1 for r in results if r["verdict"] == "timeout")
    print(f"\nSummary: {len(results)} decided/attempted — "
          f"{n_non} non-realizable, {n_to} timeout")


if __name__ == "__main__":
    main()
