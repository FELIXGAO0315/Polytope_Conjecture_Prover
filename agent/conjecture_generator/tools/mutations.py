"""
agent/conjecture_generator/tools/mutations.py — conjecture mutation engine.

Builds NEW candidates out of every existing outcome, so the generator can
never run dry while results keep landing. This is the dalmatian dynamic the
shape filter used to block: a refuted bound is not a wall, it is a repair
template; a proved bound that is slack on the pool is an invitation to
sharpen.

Moves (all exact-Fraction arithmetic over the FULL verified pool, each
emitted candidate re-verified consistent before it leaves this module):

  repair-const   (refuted)   shift the RHS constant just past the worst
                             violator, snapped OUTWARD to denominator ≤ 6.
  repair-f2      (refuted)   raise / add the `f_2>=_N` atom to exclude every
                             known violator, keeping the original RHS.
  sharpen-const  (proved/survivor/stuck)  pull the constant to pool contact
                             when the bound is slack (snapped INWARD).
  weaken-hyp     (proved)    drop one hypothesis atom (or lower the f_2
                             threshold) while staying pool-consistent — a
                             strictly stronger theorem candidate.

Every emission still passes the generator's hard gates downstream (full-pool
consistency, overfit, vacuity, dedup, review). Mutations are a SOURCE, not a
bypass — no source is trusted.
"""
from __future__ import annotations

import math
import re
from fractions import Fraction
from typing import Optional

from agent.conjectures import ConjectureSpec, canonicalize_formula
from agent.orchestrator.tools.conjecture_parser import ParsedConjecture
from agent.orchestrator.tools.pvec_eval import (
    _compile_conclusion,
    _eval_hypothesis,
)

# How many mutation candidates to emit per run. Sources are ordered
# most-recent-outcome-first, so fresh information is always attacked first
# and the cohort rotates as new results land.
MUTATION_MAX = 12

# Three-strikes: a shape family refuted this many times keeps dying because
# its violator family scales with f_2 (hexagon bands exist at EVERY size),
# not because the constants were off — stop pouring CE cycles into it.
# Observed 2026-07-02: C125 (f_2≥31) → repair → C138 (f_2≥32) → re-refuted
# by the next band member {4:6, 6:26}; the treadmill never converges.
MAX_LINEAGE_REPAIRS = 3

_CONC_RE = re.compile(r"(.*then\s+p6\s*)(<=|>=)(\s*\()(.*)(\)\s*)$", re.DOTALL)
_F2_ATOM_RE = re.compile(r"\(f_2>=_(\d+)\)")
_ATOM_SPLIT_RE = re.compile(r"\s+and\s+")


def _sixth_out(x: float) -> Fraction:
    """Smallest k/6 ≥ x (outward snap for repairs)."""
    return Fraction(math.ceil(x * 6 - 1e-9), 6)


def _sixth_in(x: float) -> Fraction:
    """Largest k/6 ≤ x (inward snap for sharpening)."""
    return Fraction(math.floor(x * 6 + 1e-9), 6)


def _fmt(q: Fraction) -> str:
    if q.denominator == 1:
        return str(q.numerator)
    return f"{float(q):.10g}"


def _shift_rhs(formula: str, delta: Fraction) -> Optional[str]:
    """`…, then p6 OP (RHS)` → `…, then p6 OP ((RHS) + delta)`."""
    m = _CONC_RE.match(formula)
    if not m or delta == 0:
        return None
    head, op, opn, rhs, close = m.groups()
    sign = "+" if delta > 0 else "-"
    return f"{head}{op}{opn}({rhs.strip()}) {sign} {_fmt(abs(delta))}{close}"


class _Evaluated:
    """One formula compiled against the pool: support rows + signed slacks.

    slack is oriented so that NEGATIVE = violation, 0 = touching, for both
    bound directions (ge: p6 - rhs, le: rhs - p6)."""

    def __init__(self, formula: str, pool: list[dict[int, int]]):
        self.ok = False
        try:
            parsed = ParsedConjecture.from_conjecture_spec(
                ConjectureSpec(name="mut_0", formula=formula))
        except Exception:
            return
        kind, rhs_fn = _compile_conclusion(parsed.conclusion)
        if kind not in ("ge", "le") or rhs_fn is None:
            return
        self.kind = kind
        self.support: list[dict[int, int]] = []
        self.slacks: list[float] = []
        for pv in pool:
            try:
                if not all(_eval_hypothesis(h, pv) for h in parsed.hypotheses):
                    continue
                rhs = float(rhs_fn(pv))
                p6 = float(pv.get(6, 0))
            except Exception:
                continue
            self.support.append(pv)
            self.slacks.append((p6 - rhs) if kind == "ge" else (rhs - p6))
        self.ok = bool(self.support)

    @property
    def min_slack(self) -> float:
        return min(self.slacks)


def _consistent(formula: str, pool: list[dict[int, int]]) -> bool:
    ev = _Evaluated(formula, pool)
    return ev.ok and ev.min_slack >= -1e-9


def _repair(formula: str, pool: list[dict[int, int]]) -> list[tuple[str, str]]:
    """Refuted bound → constant shift + f_2-threshold raise, both verified."""
    ev = _Evaluated(formula, pool)
    if not ev.ok:
        return []
    worst = -ev.min_slack                      # > 0 for a refuted bound
    if worst <= 1e-9:
        return []                              # pool no longer refutes it
    out: list[tuple[str, str]] = []

    # constant shift: move the bound outward just past the worst violator.
    delta = _sixth_out(worst)
    signed = delta if ev.kind == "le" else -delta
    shifted = _shift_rhs(formula, signed)
    if shifted:
        shifted = canonicalize_formula(shifted)
        if _consistent(shifted, pool):
            out.append((shifted, "mutate:repair-const"))

    # f_2 raise: smallest threshold excluding every violating row.
    viol_f2 = [sum(pv.values()) for pv, s in zip(ev.support, ev.slacks)
               if s < -1e-9]
    if viol_f2:
        need = max(viol_f2) + 1
        m = _F2_ATOM_RE.search(formula)
        if m and int(m.group(1)) < need:
            cand = formula.replace(m.group(0), f"(f_2>=_{need})")
        elif not m:
            cand = re.sub(r"\)\s*,\s*then", f" and (f_2>=_{need})), then",
                          formula, count=1)
        else:
            cand = None
        if cand:
            cand = canonicalize_formula(cand)
            if _consistent(cand, pool):
                # Chain a constant-sharpen so the repaired bound lands ON the
                # pool hull instead of hovering slack above the excluded
                # violators — repairs should be extremal, not just legal.
                tightened = [c for c, src in _sharpen(cand, pool)
                             if src == "mutate:sharpen-const"]
                out.append((tightened[0] if tightened else cand,
                            "mutate:repair-f2"))
    return out


def _sharpen(formula: str, pool: list[dict[int, int]]) -> list[tuple[str, str]]:
    """Consistent bound → pull constant to pool contact; try dropping atoms."""
    ev = _Evaluated(formula, pool)
    if not ev.ok or ev.min_slack < -1e-9:
        return []
    out: list[tuple[str, str]] = []

    # constant sharpen: close the gap to the pool hull (only if truly slack).
    gap = _sixth_in(ev.min_slack)
    if gap > 0:
        signed = gap if ev.kind == "ge" else -gap
        cand = _shift_rhs(formula, signed)
        if cand:
            cand = canonicalize_formula(cand)
            if _consistent(cand, pool):
                out.append((cand, "mutate:sharpen-const"))

    # hypothesis weakening: drop one atom at a time (never is_simple);
    # a proved statement with one atom fewer is a strictly stronger target.
    m = re.match(r"if\s*\((.*)\)\s*,\s*then\s+(.*)", formula,
                 re.IGNORECASE | re.DOTALL)
    if m:
        atoms = [a.strip() for a in _ATOM_SPLIT_RE.split(m.group(1))]
        conc = m.group(2).strip()
        if len(atoms) > 2:
            for i, atom in enumerate(atoms):
                if "is_simple" in atom:
                    continue
                rest = atoms[:i] + atoms[i + 1:]
                cand = canonicalize_formula(
                    f"if ({' and '.join(rest)}), then {conc}")
                if _consistent(cand, pool):
                    out.append((cand, "mutate:weaken-hyp"))
    return out


def generate_mutations(
    signals: dict[str, list[dict]],
    pool: list[dict[int, int]],
    max_out: int = MUTATION_MAX,
) -> list[tuple[str, str]]:
    """Emit up to `max_out` (formula, source) mutation candidates.

    Refuted entries are attacked most-recent-first (freshest CE knowledge);
    proved/survivor/stuck entries are sharpened. Dedup here is only against
    this batch — the generator's known-formula dedup and hard gates do the
    real vetting downstream.
    """
    out: list[tuple[str, str]] = []
    seen: set[str] = set()

    def _take(cands: list[tuple[str, str]]) -> bool:
        for formula, src in cands:
            if formula in seen:
                continue
            seen.add(formula)
            out.append((formula, src))
            if len(out) >= max_out:
                return True
        return False

    sharpen_sources = (signals.get("proved") or []) \
        + (signals.get("prover_stuck") or []) \
        + (signals.get("survivor") or [])
    for e in sharpen_sources:
        if _take(_sharpen(e.get("formula", ""), pool)):
            return out

    # Lineage census for the three-strikes rule (lazy import: agent.py
    # imports this module at load time, but by the time generate_mutations
    # runs the cycle is fully resolved).
    from collections import Counter
    from agent.conjecture_generator.agent import ConjectureGenerator as _G
    lineage: Counter = Counter()
    refuted = signals.get("refuted") or []
    for e in refuted:
        s = _G._formula_shape(e.get("formula", ""))
        if s is not None:
            lineage[s] += 1

    for e in reversed(refuted):                        # most recent first
        shape = _G._formula_shape(e.get("formula", ""))
        if shape is not None and lineage[shape] >= MAX_LINEAGE_REPAIRS:
            continue                                   # three strikes — out
        if _take(_repair(e.get("formula", ""), pool)):
            return out
    return out
