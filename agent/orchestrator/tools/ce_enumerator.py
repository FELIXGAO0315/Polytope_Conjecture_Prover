"""Systematic enumeration of arithmetic CE candidates for a conjecture.

Stage 2 of the pipeline. Enumerates every p-vector within configurable bounds
that satisfies the *necessary* arithmetic conditions for a simple 3-polytope
(non-negativity, Dehn-Sommerville sum = 12) plus the conjecture's hypotheses,
while violating its conclusion. Candidates derive from the conjecture formula
alone — realizability is decided downstream by the 4-check validator.

Also provides the Inventory-entailment pre-check: a candidate that additionally
satisfies the per-map arithmetic content of every Inventory axiom (occupation
feasibility, the Jučovič inequality, …) is a *countermodel* — its existence
proves the conjecture's conclusion is not derivable from Inventory.lean, so
Stage 4 formalization cannot honestly succeed until either a CE is realized or
Inventory gains new (real) mathematical content.

Env-tunable bounds:
  CE_ENUM_F2_MAX      (default 36)  max total face count
  CE_ENUM_KMAX        (default 20)  max face size
  CE_ENUM_NLARGE_MAX  (default 2)   max number of faces of size >= 7
  CE_ENUM_MAX_RESULTS (default 400) cap on returned candidates
"""

from __future__ import annotations

import os
import threading
from dataclasses import dataclass
from itertools import combinations_with_replacement

from agent.orchestrator.tools.pvec_eval import _eval_hypothesis, _eval_conclusion_violated

# Enumeration is pure in (hypotheses, conclusion, bounds) — memoize so the
# pipeline doesn't recompute the same candidate list (Stage 2, entailment
# pre-check, …) several times per conjecture.
_ENUM_CACHE: dict[tuple, list["CECandidate"]] = {}
_ENUM_LOCK = threading.Lock()


@dataclass
class CECandidate:
    p_vec: dict[int, int]
    f2: int
    max_face: int


def _env_int(name: str, default: int) -> int:
    try:
        return int(os.environ.get(name, default))
    except ValueError:
        return default


def enumerate_ce_candidates(
    conjecture,
    f2_max: int | None = None,
    k_max: int | None = None,
    n_large_max: int | None = None,
    max_results: int | None = None,
) -> list[CECandidate]:
    """Enumerate DS-valid p-vectors that satisfy all hypotheses and violate the
    conclusion. Sorted for constructibility: small f2 first, small max face,
    more triangles."""
    f2_max = f2_max if f2_max is not None else _env_int("CE_ENUM_F2_MAX", 36)
    k_max = k_max if k_max is not None else _env_int("CE_ENUM_KMAX", 20)
    n_large_max = n_large_max if n_large_max is not None else _env_int("CE_ENUM_NLARGE_MAX", 2)
    max_results = max_results if max_results is not None else _env_int("CE_ENUM_MAX_RESULTS", 400)

    hyps = list(conjecture.hypotheses)
    conclusion = conjecture.conclusion

    cache_key = (tuple(hyps), conclusion, f2_max, k_max, n_large_max, max_results)
    with _ENUM_LOCK:
        if cache_key in _ENUM_CACHE:
            return list(_ENUM_CACHE[cache_key])

    out: list[CECandidate] = []

    # Large-face multisets (sizes >= 7), including the empty multiset.
    large_sets: list[tuple[int, ...]] = [()]
    for n in range(1, n_large_max + 1):
        large_sets.extend(combinations_with_replacement(range(7, k_max + 1), n))

    for large in large_sets:
        deficit = sum(k - 6 for k in large)        # Σ_{k≥7}(k−6)·p_k
        low_budget = 12 + deficit                   # 3p3 + 2p4 + p5 must equal this
        n_large = len(large)
        for p3 in range(low_budget // 3 + 1):
            for p4 in range((low_budget - 3 * p3) // 2 + 1):
                p5 = low_budget - 3 * p3 - 2 * p4
                base = p3 + p4 + p5 + n_large
                if base > f2_max:
                    continue
                for p6 in range(f2_max - base + 1):
                    p_vec: dict[int, int] = {}
                    if p3: p_vec[3] = p3
                    if p4: p_vec[4] = p4
                    if p5: p_vec[5] = p5
                    if p6: p_vec[6] = p6
                    for k in large:
                        p_vec[k] = p_vec.get(k, 0) + 1
                    if not p_vec:
                        continue
                    violated, _ = _eval_conclusion_violated(conclusion, p_vec)
                    if not violated:
                        continue
                    if not all(_eval_hypothesis(h, p_vec) for h in hyps):
                        continue
                    out.append(CECandidate(
                        p_vec=p_vec,
                        f2=base + p6,
                        max_face=max(p_vec),
                    ))

    out.sort(key=lambda c: (c.f2, c.max_face, -c.p_vec.get(3, 0)))
    result = out[:max_results]
    with _ENUM_LOCK:
        _ENUM_CACHE[cache_key] = result
    return list(result)


def inventory_countermodels(candidates: list[CECandidate]) -> list[CECandidate]:
    """Filter candidates down to true countermodels of Inventory's per-map
    arithmetic content (genus 0). A surviving candidate satisfies every linear
    constraint any Lean proof can extract from the axioms applied to the given
    `maps`, yet violates the conjecture conclusion — so the conclusion is not
    entailed by Inventory.

    Encoded constraints (faithful to polib/Inventory.lean statements):
      - euler_formula / handshake / regularity: automatically satisfied by any
        DS=12 p-vector with v = 2(f2−2), e = 3(f2−2).
      - occupation_conservation (REQUIRES m ≥ 6 since 2026-06-11) +
        occupation_bound: feasibility of total_occ requires
        0 ≤ 3·p3 ≤ Σ_{k≥4} ⌊k/2⌋·p_k — only applicable when max_face ≥ 6.
      - quad_occ_cancellation (m ≥ 6): combined with conservation + hex bound
        it yields exactly the Jučovič inequality below (given DS=12), so the
        single check covers Juc_InequalityPart / P6InequalityPart (now PROVED
        in Lean from these axioms) and JucovicTheorem / P6GenusG:
        3·p6 ≥ 12 − 2·p4 − 3·p5 + Σ_{k≥7}(⌊(k+1)/2⌋−6)·p_k.
      - p_range, equality_family: no constraint on the candidate's data.
    """
    survivors: list[CECandidate] = []
    for c in candidates:
        pv = c.p_vec
        p3, p4, p5, p6 = (pv.get(k, 0) for k in (3, 4, 5, 6))

        if c.max_face >= 6:
            # occupation feasibility (conservation is m≥6-guarded in Lean)
            occ_cap = sum((k // 2) * n for k, n in pv.items() if k >= 4)
            if 3 * p3 > occ_cap:
                continue

            # Jučovič / p6 inequality (≡ conservation + cancellation + hex bound)
            juc_rhs = 12 - 2 * p4 - 3 * p5 + sum(
                ((k + 1) // 2 - 6) * n for k, n in pv.items() if k >= 7
            )
            if 3 * p6 < juc_rhs:
                continue

        survivors.append(c)
    return survivors
