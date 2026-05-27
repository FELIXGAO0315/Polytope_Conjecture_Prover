"""
agent/tools/check_pvector.py — PVectorCheckAgent

Rigorously validates whether a candidate p-vector is a genuine counterexample
by running four independent checks and printing [Check p-vector] lines.

Checks
------
1. Dehn-Sommerville + Euler consistency  (necessary conditions, full)
2. Hypotheses                            (per-hypothesis with computed values)
3. Conclusion violation                  (with margin magnitude)
4. Realizability                         (3-tier: known polytopes → proven families → Constructor)

Realizability tier design
--------------------------
Tier 1  Exact known simple polytopes — O(1) dict lookup, each entry verified DS=12.
Tier 2  Proven infinite families — only families with rigorous realizability proofs:
          • n-gonal prisms  (p4=n, p_n=2, any n≥3): standard construction
          • Fullerene family (p5=12, p6≥2): infinite series well-established;
            p6=0 is dodecahedron (Tier 1), p6=1 is known NON-realizable (Grünbaum 1967)
Tier 3  (dead code note): Eberhard's interior criterion would apply when
          sum_{k≠6}(6-k)*p_k < 12, but since (6-6)=0 the p_6 term never appears
          in the DS sum, so DS = sum_{k≠6}(6-k)*p_k always.  Check 1 requires DS=12,
          so this tier can never fire for valid inputs — it is intentionally omitted.
Tier 4  PolytopeConstructor — MANDATORY hard gate.  A witness graph must be built
          and its p-vector verified before a CE is accepted.  If construction fails
          (timeout, all strategies exhausted, or import error) the CE is REJECTED.
"""
from __future__ import annotations

import re
import warnings
from dataclasses import dataclass, field
from typing import Optional

try:
    import networkx as nx
    warnings.filterwarnings("ignore", message=".*hashes produced.*", module="networkx")
    _GRAPH_AVAILABLE = True
except ImportError:
    _GRAPH_AVAILABLE = False

try:
    from agent.tools.polytope_constructor import PolytopeConstructor, _pvec_of as _constructor_pvec_of
    _CONSTRUCTOR_OK = True
except ImportError:
    _CONSTRUCTOR_OK = False
    _constructor_pvec_of = None


# ══════════════════════════════════════════════════════════════════════════════
# Result types
# ══════════════════════════════════════════════════════════════════════════════

@dataclass
class CheckResult:
    passed: bool
    label: str
    detail: str
    critical: bool = True   # False → warning only, does not block all_passed


@dataclass
class CheckReport:
    results: list[CheckResult] = field(default_factory=list)

    @property
    def all_passed(self) -> bool:
        return all(r.passed for r in self.results if r.critical)

    def failure_summary(self) -> str:
        failed = [r for r in self.results if not r.passed and r.critical]
        return "; ".join(f"{r.label}: {r.detail[:80]}" for r in failed) or "unknown"

    def print(self) -> None:
        for r in self.results:
            mark = "✓" if r.passed else "✗"
            print(f"[Check p-vector] {mark} {r.label}: {r.detail}")


# ══════════════════════════════════════════════════════════════════════════════
# Check 1 — Dehn-Sommerville + Euler consistency
# ══════════════════════════════════════════════════════════════════════════════

def _check_dehn_sommerville(p_vec: dict[int, int]) -> CheckResult:
    """
    For a simple convex 3-polytope the following must ALL hold:
      (a) p_k >= 0 for all k, and k >= 3
      (b) sum_{k>=3}(6-k)*p_k = 12          (Dehn-Sommerville / Euler combined)
      (c) f2 = sum(p_k) >= 4                 (tetrahedron is the smallest)
      (d) V = 2(f2-2) >= 4, E = 3(f2-2) >= 6 (Euler: V-E+F=2 with 3-regularity)
    """
    problems = []

    # (a) non-negativity and minimum face size
    bad_k = [k for k in p_vec if k < 3]
    bad_v = {k: v for k, v in p_vec.items() if v < 0}
    if bad_k:
        problems.append(f"face sizes < 3: {bad_k}")
    if bad_v:
        problems.append(f"negative counts: {bad_v}")

    # (b) Dehn-Sommerville sum (only count positive entries to avoid noise from zeros)
    ds = sum((6 - k) * v for k, v in p_vec.items() if v > 0)
    if ds != 12:
        problems.append(f"Dehn-Sommerville sum = {ds} ≠ 12")

    # (c) minimum face count
    f2 = sum(v for v in p_vec.values() if v > 0)
    if f2 < 4:
        problems.append(f"f2 = {f2} < 4")

    # (d) Euler-derived quantities (for 3-regular graphs: 2E=3V, V-E+f2=2)
    V = 2 * (f2 - 2)
    E = 3 * (f2 - 2)
    if V < 4:
        problems.append(f"V = {V} < 4")

    if problems:
        return CheckResult(False, "Dehn-Sommerville + Euler",
                           " | ".join(problems))

    return CheckResult(
        True, "Dehn-Sommerville + Euler",
        f"DS=12 ✓  f2={f2}  V={V}  E={E}  (Euler: {V}-{E}+{f2}={V - E + f2})",
    )


# ══════════════════════════════════════════════════════════════════════════════
# Check 2 — Hypotheses (per-hypothesis with computed values)
# ══════════════════════════════════════════════════════════════════════════════

def _check_hypotheses(p_vec: dict[int, int], conjecture) -> CheckResult:
    from agent.orchestrator import _eval_hypothesis

    f2 = sum(v for v in p_vec.values() if v > 0)
    details = []
    failed = []

    for hyp in conjecture.hypotheses:
        ok = _eval_hypothesis(hyp, p_vec)

        annotation = ""
        if re.search(r'f_(?:\{2\}|2)', hyp):
            annotation = f" [f2={f2}]"
        else:
            m = re.search(r'p_\{?(\d+)\}?', hyp)
            if m:
                k = int(m.group(1))
                annotation = f" [p{k}={p_vec.get(k, 0)}]"

        mark = "✓" if ok else "✗"
        details.append(f"{mark} {hyp}{annotation}")
        if not ok:
            failed.append(hyp)

    passed = len(failed) == 0
    return CheckResult(
        passed, "Hypotheses",
        "  |  ".join(details) + ("" if passed else f"  →  FAILED: {failed}"),
    )


# ══════════════════════════════════════════════════════════════════════════════
# Check 3 — Conclusion violation with magnitude
# ══════════════════════════════════════════════════════════════════════════════

def _check_conclusion(p_vec: dict[int, int], conjecture) -> CheckResult:
    from agent.orchestrator import _eval_conclusion_violated
    import re as _re

    violated, detail = _eval_conclusion_violated(conjecture.conclusion, p_vec)

    p6 = float(p_vec.get(6, 0))
    # RHS may be negative; match optional leading minus sign
    rhs_match = _re.search(r'RHS=(-?[\d.]+)', detail)
    rhs = float(rhs_match.group(1)) if rhs_match else None

    if violated and rhs is not None:
        if conjecture.conclusion.strip().startswith('p_6') or conjecture.conclusion.strip().startswith('p_\\{6\\}'):
            # p6 >= RHS violated → margin = RHS - p6 > 0
            margin = rhs - p6
        else:
            # p6 <= RHS violated → margin = p6 - RHS > 0
            margin = p6 - rhs
        extra = f"  |  p6={p6},  RHS={rhs},  violation margin={margin:.4f}"
        if 0 < margin < 0.5:
            extra += "  ⚠ small margin — verify no floating-point precision issue"
    else:
        extra = ""

    return CheckResult(violated, "Conclusion violated", detail + extra)


# ══════════════════════════════════════════════════════════════════════════════
# Check 4 — Realizability
# ══════════════════════════════════════════════════════════════════════════════

# ── Tier 1: exact known simple polytopes (each verified DS=12) ────────────────
#
# Verification of DS = sum_{k}(6-k)*p_k for each entry:
#   tetrahedron      {3:4}:        (6-3)*4 = 12 ✓
#   cube             {4:6}:        (6-4)*6 = 12 ✓
#   dodecahedron     {5:12}:       (6-5)*12 = 12 ✓
#   triangular prism {3:2, 4:3}:   (6-3)*2 + (6-4)*3 = 6+6 = 12 ✓
#   pentagonal prism {4:5, 5:2}:   (6-4)*5 + (6-5)*2 = 10+2 = 12 ✓
#   trunc. tetrahedron {3:4, 6:4}: (6-3)*4 + (6-6)*4 = 12+0 = 12 ✓
#   trunc. octahedron {4:6, 6:8}:  (6-4)*6 + (6-6)*8 = 12+0 = 12 ✓

_KNOWN_POLYTOPES: list[tuple[dict[int, int], str]] = [
    ({3: 4},         "tetrahedron"),
    ({4: 6},         "cube"),
    ({5: 12},        "dodecahedron"),
    ({3: 2, 4: 3},   "triangular prism"),
    ({4: 5, 5: 2},   "pentagonal prism"),
    ({3: 4, 6: 4},   "truncated tetrahedron"),
    ({4: 6, 6: 8},   "truncated octahedron"),
]


# ── Tier 2: proven infinite families ─────────────────────────────────────────

def _match_family(p_vec: dict[int, int]) -> Optional[str | bool]:
    """
    Return a description string if p_vec belongs to a proven infinite family,
    False if it is a known NON-realizable combination, or None to fall through
    to Tier 4.

    Only families with rigorous realizability proofs are included here.
    All others are delegated to the Tier 4 constructor.
    """
    nonzero = {k: v for k, v in p_vec.items() if v > 0}
    large   = {k: v for k, v in nonzero.items() if k > 6}
    small   = {k: v for k, v in nonzero.items() if k <= 6}

    # ── Prism family: n-gonal prism = p4=n, p_n=2 for n ≥ 7 ──────────────────
    # DS verification: (6-4)*n + (6-n)*2 = 2n + 12 - 2n = 12 ✓ for all n
    # Realizability: direct construction for any n (see PolytopeConstructor._make_prism)
    if len(large) == 1:
        k_big, cnt = next(iter(large.items()))
        if cnt == 2 and small == {4: k_big}:
            return (f"prism family: {k_big}-gonal prism "
                    f"(p4={k_big}, p_{k_big}=2) — directly constructible")

    # ── Fullerene family: p5=12, p6≥2 ────────────────────────────────────────
    # DS verification: (6-5)*12 + (6-6)*p6 = 12 ✓ for any p6
    # Known non-realizable: p5=12, p6=1 (Grünbaum 1967, proven impossible)
    # p5=12, p6=0 is the dodecahedron — handled by Tier 1
    # p5=12, p6≥2: infinite realizable series (fullerene chemistry, well-established)
    if set(nonzero.keys()) <= {5, 6} and nonzero.get(5, 0) == 12:
        p6_count = nonzero.get(6, 0)
        if p6_count == 1:
            return False  # proven non-realizable
        if p6_count >= 2:
            return (f"fullerene family: p5=12, p6={p6_count} "
                    f"— realizable (infinite fullerene series, all p6≥2 proven)")
        # p6_count == 0 → dodecahedron, should have matched Tier 1 already

    return None


def _check_realizability(p_vec: dict[int, int], timeout: float = 30.0) -> CheckResult:
    nonzero = {k: v for k, v in p_vec.items() if v > 0}

    # ── Tier 1: exact known polytopes ─────────────────────────────────────────
    for known_pv, name in _KNOWN_POLYTOPES:
        if nonzero == known_pv:
            return CheckResult(True, "Realizability",
                               f"[Tier 1] exact match: {name}")

    # ── Tier 2: proven infinite families ──────────────────────────────────────
    family = _match_family(p_vec)
    if family is False:
        # Explicitly known non-realizable combination
        p6_val = nonzero.get(6, 0)
        p5_val = nonzero.get(5, 0)
        return CheckResult(
            False, "Realizability",
            f"[Tier 2] p5={p5_val}, p6={p6_val} is a known NON-realizable "
            f"combination (Grünbaum 1967) — CE rejected",
        )
    if family:
        return CheckResult(True, "Realizability", f"[Tier 2] {family}")

    # ── Note: Tier 3 (Eberhard interior) is intentionally omitted ─────────────
    # Since (6-6)=0, p_6 contributes nothing to the DS sum:
    #   DS = sum_{k}(6-k)*p_k = sum_{k≠6}(6-k)*p_k = ds_no_p6
    # Check 1 requires DS=12, so ds_no_p6=12 always here.
    # The Eberhard interior criterion (ds_no_p6 < 12) is therefore unreachable
    # for any p-vector that survived Check 1.  Delegating to Tier 4 is correct.

    # ── Tier 4: PolytopeConstructor — mandatory hard gate ─────────────────────
    # Construction must succeed to accept the CE.  Timeout or import failure
    # means the CE is REJECTED — DS=12 is necessary but not sufficient.
    if not _CONSTRUCTOR_OK:
        return CheckResult(
            False, "Realizability",
            "[Tier 4 Constructor] PolytopeConstructor unavailable (import failed) "
            "— cannot verify realizability; CE REJECTED",
        )

    G, method = PolytopeConstructor().build(p_vec, timeout=timeout)

    if G is None:
        return CheckResult(
            False, "Realizability",
            f"[Tier 4 Constructor] all construction strategies exhausted "
            f"(last attempt: {method}, timeout={timeout:.0f}s) "
            f"— realizability UNPROVEN; CE rejected (no witness graph)",
        )

    # Construction succeeded — verify the graph's p-vector matches the target.
    # This is a sanity defence-in-depth check against constructor bugs.
    if _constructor_pvec_of is not None:
        try:
            actual_pv = _constructor_pvec_of(G)
            if actual_pv is None:
                return CheckResult(
                    False, "Realizability",
                    f"[Tier 4 Constructor] {method}: graph built but graphcalc "
                    f"reports it is NOT a simple polytope — CE rejected",
                )
            if actual_pv != nonzero:
                return CheckResult(
                    False, "Realizability",
                    f"[Tier 4 Constructor] {method}: graph built but p-vector "
                    f"mismatch — built={actual_pv} ≠ target={nonzero}; CE rejected",
                )
        except Exception as verify_err:
            # Verification failed unexpectedly; treat as construction failure.
            return CheckResult(
                False, "Realizability",
                f"[Tier 4 Constructor] {method}: post-construction verification "
                f"raised {verify_err!r} — CE rejected (cannot confirm witness)",
            )

    return CheckResult(
        True, "Realizability",
        f"[Tier 4 Constructor] {method}: witness graph with "
        f"{G.number_of_nodes()} vertices, {G.number_of_edges()} edges, "
        f"p-vector verified — realizability PROVEN by explicit construction",
    )


# ══════════════════════════════════════════════════════════════════════════════
# Public API
# ══════════════════════════════════════════════════════════════════════════════

class PVectorCheckAgent:
    """
    Runs four checks on a candidate counterexample p-vector.

    Usage
    -----
        agent = PVectorCheckAgent()
        report = agent.run(p_vec, conjecture)
        if report.all_passed:
            ...
    """

    def __init__(self, client=None):
        pass  # client kept for API compatibility

    def run(
        self,
        p_vec: dict[int, int],
        conjecture,
        constructor_timeout: float = 30.0,
    ) -> CheckReport:
        """Run all checks and print [Check p-vector] lines."""
        report = self.run_silent(p_vec, conjecture, constructor_timeout=constructor_timeout)
        report.print()
        return report

    def run_silent(
        self,
        p_vec: dict[int, int],
        conjecture,
        constructor_timeout: float = 30.0,
    ) -> CheckReport:
        """Run all checks without printing — caller decides what to show."""
        report = CheckReport()
        report.results.append(_check_dehn_sommerville(p_vec))
        report.results.append(_check_hypotheses(p_vec, conjecture))
        report.results.append(_check_conclusion(p_vec, conjecture))
        report.results.append(_check_realizability(p_vec, timeout=constructor_timeout))
        return report
