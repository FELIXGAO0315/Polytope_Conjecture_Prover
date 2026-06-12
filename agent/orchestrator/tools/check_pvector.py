"""
agent/tools/check_pvector.py — PVectorCheckAgent

Rigorously validates whether a candidate p-vector is a genuine counterexample
by running five independent checks and printing [Check p-vector] lines.

Checks
------
1. Dehn-Sommerville + Euler consistency  (necessary conditions, full)
2. Hypotheses                            (per-hypothesis with computed values)
3. Conclusion violation                  (with margin magnitude)
4. Realizability                         (3-tier: known polytopes → proven families → Constructor)
5. Final ce validation check             (fully independent re-verification:
   own AST evaluator for hypotheses/conclusion — no pvec_eval — plus networkx
   Steinitz validation of the witness graph with embedding-traced p-vector)

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

import os
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
    from agent.orchestrator.tools.polytope_constructor import PolytopeConstructor, _pvec_of as _constructor_pvec_of
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
    # witness graph as a plain int edge list (JSON/pickle friendly) — set when
    # the realizability tier produced an explicit graph, so the CE JSON can
    # persist independently re-checkable evidence
    witness_edges: Optional[list] = None

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
    from agent.orchestrator.tools.pvec_eval import _eval_hypothesis

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
    from agent.orchestrator.tools.pvec_eval import _eval_conclusion_violated
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


def _check_realizability(
    p_vec: dict[int, int],
    timeout: float = 30.0,
    rl_verified: bool = False,
    witness_graph=None,
) -> tuple[CheckResult, "Optional[nx.Graph]"]:
    """Returns (result, witness_graph_or_None); the witness feeds Check 5's
    independent networkx re-validation."""
    nonzero = {k: v for k, v in p_vec.items() if v > 0}

    # ── Explicit witness graph (e.g. extracted from Hopper's dual hull) ───────
    # Not trusted: the graph is re-verified here with graphcalc and its
    # p-vector must match the candidate exactly. Falls through to the tiers
    # if verification fails.
    if witness_graph is not None:
        from agent.orchestrator.tools.polytope_constructor import _pvec_of
        wpv = _pvec_of(witness_graph)
        if wpv == nonzero:
            return CheckResult(
                True, "Realizability",
                "[witness] explicit graph verified as simple 3-polytope by "
                "graphcalc; p-vector matches candidate exactly",
            ), witness_graph

    # ── RL-verified flag is NOT trusted (hardened 2026-06-11) ─────────────────
    # The RL environment does verify its graph with graphcalc, but only the
    # p-vector crosses the process boundary — a bare flag cannot be re-checked
    # here, and trusting it would let an upstream bug mint an unverified CE.
    # Acceptance requires either an explicit witness_graph (verified above) or
    # the tier pipeline below. `rl_verified` is kept for API compatibility.

    # Exotic targets with very large faces (k >= 10) need more A* search time.
    kmax = max(nonzero.keys(), default=3)
    if kmax >= 10:
        timeout = max(timeout, 20.0)

    def _family_witness():
        """Best-effort explicit graph for Tier 1/2 textual citations, so
        Check 5 can still re-validate. None if no direct builder exists."""
        if not _CONSTRUCTOR_OK:
            return None
        try:
            from agent.orchestrator.tools.polytope_constructor import (
                _build_known, _build_prism, _pvec_of,
            )
            G = _build_known(nonzero) or _build_prism(nonzero)
            if G is not None and _pvec_of(G) == nonzero:
                return G
        except Exception:
            pass
        return None

    # ── Tier 1: exact known polytopes ─────────────────────────────────────────
    for known_pv, name in _KNOWN_POLYTOPES:
        if nonzero == known_pv:
            return CheckResult(True, "Realizability",
                               f"[Tier 1] exact match: {name}"), _family_witness()

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
        ), None
    if family:
        return CheckResult(True, "Realizability", f"[Tier 2] {family}"), _family_witness()

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
        ), None

    G, method = PolytopeConstructor().build(p_vec, timeout=timeout)

    if G is None:
        if method == "plantri_nonrealizable":
            return CheckResult(
                False, "Realizability",
                "[Tier 4 plantri] exhaustively NON-realizable — no sphere "
                "triangulation with this degree multiset exists (proof by "
                "exhaustion); candidate definitively rejected",
            ), None
        return CheckResult(
            False, "Realizability",
            f"[Tier 4 Constructor] all construction strategies exhausted "
            f"(last attempt: {method}, timeout={timeout:.0f}s) "
            f"— realizability UNPROVEN; CE rejected (no witness graph)",
        ), None

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
                ), None
            if actual_pv != nonzero:
                return CheckResult(
                    False, "Realizability",
                    f"[Tier 4 Constructor] {method}: graph built but p-vector "
                    f"mismatch — built={actual_pv} ≠ target={nonzero}; CE rejected",
                ), None
        except Exception as verify_err:
            # Verification failed unexpectedly; treat as construction failure.
            return CheckResult(
                False, "Realizability",
                f"[Tier 4 Constructor] {method}: post-construction verification "
                f"raised {verify_err!r} — CE rejected (cannot confirm witness)",
            ), None

    return CheckResult(
        True, "Realizability",
        f"[Tier 4 Constructor] {method}: witness graph with "
        f"{G.number_of_nodes()} vertices, {G.number_of_edges()} edges, "
        f"p-vector verified — realizability PROVEN by explicit construction",
    ), G


# ══════════════════════════════════════════════════════════════════════════════
# Check 5 — Final CE validation (fully independent re-verification)
#
# Checks 2/3 share the pvec_eval parser — a single point of failure that has
# already produced one bogus CE (the retracted C3 f2=8 counterexample came
# from a hypothesis-evaluation bug). This check re-derives everything through
# code paths that share NOTHING with pvec_eval or graphcalc:
#   (a) hypotheses + conclusion re-evaluated by a from-scratch substitution +
#       AST-whitelist evaluator working directly on the conjecture statement;
#   (b) the witness graph re-validated with networkx: 3-regular, planar,
#       3-connected (Steinitz ⇒ simple 3-polytope), and the p-vector is
#       re-derived by tracing every face of the planar embedding (unique for
#       3-connected planar graphs by Whitney) and must match the candidate.
# ══════════════════════════════════════════════════════════════════════════════

import ast as _ast

_ALLOWED_AST_NODES = (
    _ast.Expression, _ast.BoolOp, _ast.And, _ast.Or,
    _ast.UnaryOp, _ast.Not, _ast.USub, _ast.UAdd,
    _ast.BinOp, _ast.Add, _ast.Sub, _ast.Mult, _ast.Div,
    _ast.FloorDiv, _ast.Mod, _ast.Pow,
    _ast.Compare, _ast.Gt, _ast.GtE, _ast.Lt, _ast.LtE, _ast.Eq, _ast.NotEq,
    _ast.Constant, _ast.Load,
)


def _safe_eval_bool(expr: str) -> bool:
    """Evaluate a fully-substituted numeric/boolean expression. Any leftover
    name (i.e. an unrecognised variable) is rejected by the AST whitelist."""
    tree = _ast.parse(expr, mode="eval")
    for node in _ast.walk(tree):
        if not isinstance(node, _ALLOWED_AST_NODES):
            raise ValueError(
                f"disallowed element {type(node).__name__} in {expr!r}")
    return bool(eval(compile(tree, "<final-ce-check>", "eval"),
                     {"__builtins__": {}}, {}))


def _balance_parens(s: str) -> str:
    """Strip surplus outer parens (hypothesis lists can carry unbalanced ones
    from the upstream 'and' split, e.g. '((is_simple)' / '(f_2>=_13))')."""
    s = s.strip()
    while s.startswith("(") and s.count("(") > s.count(")"):
        s = s[1:].strip()
    while s.endswith(")") and s.count(")") > s.count("("):
        s = s[:-1].strip()
    return s


def _subst_pvec_tokens(s: str, p_vec: dict[int, int]) -> str:
    """Replace every conjecture-dialect variable with its numeric value,
    computed directly from the p-vector (independent of pvec_eval)."""
    f2 = sum(v for v in p_vec.values() if v > 0)

    def _sum_ge(n: int) -> int:
        return sum(v for k, v in p_vec.items() if k >= n and v > 0)

    # light LaTeX normalisation so LaTeX-sourced statements also evaluate
    s = s.replace("$", " ")
    s = re.sub(r'\\sum_\{k\s*(?:\\geq|\\ge|>=)\s*(\d+)\}\s*p_k', r'sum_pk_k>=\1', s)
    s = s.replace(r'\geq', '>=').replace(r'\leq', '<=')
    s = re.sub(r'\\text\{[^}]*\}', 'is_simple', s)
    s = re.sub(r'p_\{(\d+)\}', r'p\1', s)
    s = re.sub(r'f_\{2\}', 'f2', s)

    # longest tokens first — later patterns must not eat into earlier ones
    s = re.sub(r'sum_pk_k>=(\d+)', lambda m: str(_sum_ge(int(m.group(1)))), s)
    s = re.sub(r'f_2>=_(\d+)', lambda m: f"({f2} >= {int(m.group(1))})", s)
    s = s.replace("sum_pk_after_p6", str(_sum_ge(7)))
    s = s.replace("is_simple", "True")
    s = re.sub(r'\bf_?2\b', str(f2), s)
    s = re.sub(r'\bp_?(\d+)\b', lambda m: str(p_vec.get(int(m.group(1)), 0)), s)
    s = re.sub(r'(?<![<>=!])=(?!=)', '==', s)   # bare '=' → '=='
    return s


def _independent_violation_eval(p_vec: dict[int, int], conjecture) -> tuple[bool, str]:
    """Re-verify 'hypotheses hold AND conclusion violated' independently.

    Prefers the raw statement (own if/then split — does not trust the
    upstream hypothesis splitter either); falls back to the parsed
    hypothesis/conclusion strings.
    """
    stmt = (getattr(conjecture, "statement_latex", "") or "").strip()
    m = re.match(r'^\s*if\s*\((.*)\)\s*,\s*then\s+(.+)$', stmt, re.IGNORECASE)
    if m:
        hyp_srcs = [m.group(1)]
        conc_src = m.group(2)
        origin = "statement"
    else:
        hyp_srcs = list(getattr(conjecture, "hypotheses", []) or [])
        conc_src = getattr(conjecture, "conclusion", "") or ""
        origin = "hypotheses+conclusion"
    if not conc_src:
        return False, "independent re-eval: no conclusion to verify"

    for h in hyp_srcs:
        expr = _balance_parens(_subst_pvec_tokens(h, p_vec))
        if not expr:
            continue
        if not _safe_eval_bool(expr):
            return False, (f"independent re-eval ({origin}): hypothesis "
                           f"{h.strip()!r} is FALSE for this p-vector")
    conc_expr = _balance_parens(_subst_pvec_tokens(conc_src, p_vec))
    if _safe_eval_bool(conc_expr):
        return False, (f"independent re-eval ({origin}): conclusion "
                       f"{conc_src.strip()!r} HOLDS — not a counterexample")
    return True, (f"independent re-eval ({origin}): hypotheses TRUE, "
                  f"conclusion FALSE [{conc_expr}]")


def _validate_witness_graph(G, p_vec: dict[int, int]) -> tuple[bool, str]:
    """Independent Steinitz validation with networkx (graphcalc not used):
    3-regular + planar + 3-connected + embedding-traced p-vector match."""
    nonzero = {k: v for k, v in p_vec.items() if v > 0}
    n, m = G.number_of_nodes(), G.number_of_edges()

    if nx.number_of_selfloops(G) > 0:
        return False, "witness graph has self-loops"
    bad_deg = [v for v, d in G.degree() if d != 3]
    if bad_deg:
        return False, f"witness graph not 3-regular ({len(bad_deg)} vertices)"
    if not nx.is_connected(G):
        return False, "witness graph not connected"
    planar, emb = nx.check_planarity(G)
    if not planar:
        return False, "witness graph not planar"
    if nx.node_connectivity(G) < 3:
        return False, "witness graph not 3-connected (fails Steinitz)"

    # trace every face of the embedding (well-defined: Whitney uniqueness)
    sizes: list[int] = []
    visited: set = set()
    for u, v in emb.edges():
        if (u, v) in visited:
            continue
        face = emb.traverse_face(u, v, mark_half_edges=visited)
        sizes.append(len(face))
    F = len(sizes)
    if n - m + F != 2:
        return False, f"Euler failure on embedding: V-E+F = {n}-{m}+{F} != 2"
    traced: dict[int, int] = {}
    for s in sizes:
        traced[s] = traced.get(s, 0) + 1
    if traced != nonzero:
        return False, (f"embedding p-vector mismatch: traced={traced} "
                       f"!= candidate={nonzero}")
    return True, (f"witness re-validated by networkx: 3-regular, planar, "
                  f"3-connected, all {F} faces traced — p-vector matches "
                  f"(V={n}, E={m}, F={F})")


def _check_final_validation(p_vec: dict[int, int], conjecture, witness) -> CheckResult:
    label = "Final ce validation check"
    try:
        ok_formula, formula_detail = _independent_violation_eval(p_vec, conjecture)
    except Exception as exc:
        return CheckResult(
            False, label,
            f"independent re-evaluation could not verify the violation "
            f"({exc!r}) — CE rejected")
    if not ok_formula:
        return CheckResult(False, label, f"{formula_detail} — CE rejected")

    if witness is None:
        return CheckResult(
            True, label,
            f"{formula_detail} | no witness graph exported by the "
            f"realizability tier — graph re-validation skipped")
    if not _GRAPH_AVAILABLE:
        return CheckResult(
            True, label,
            f"{formula_detail} | networkx unavailable — graph re-validation "
            f"skipped")
    try:
        ok_graph, graph_detail = _validate_witness_graph(witness, p_vec)
    except Exception as exc:
        return CheckResult(
            False, label,
            f"{formula_detail} | witness graph re-validation raised {exc!r} "
            f"— CE rejected")
    return CheckResult(ok_graph, label, f"{formula_detail} | {graph_detail}")


# ══════════════════════════════════════════════════════════════════════════════
# Public API
# ══════════════════════════════════════════════════════════════════════════════

class PVectorCheckAgent:
    """
    Runs five checks on a candidate counterexample p-vector.

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
        rl_verified: bool = False,
        witness_graph=None,
    ) -> CheckReport:
        """Run all checks without printing — caller decides what to show."""
        report = CheckReport()
        report.results.append(_check_dehn_sommerville(p_vec))
        report.results.append(_check_hypotheses(p_vec, conjecture))
        report.results.append(_check_conclusion(p_vec, conjecture))
        realiz_result, witness = _check_realizability(
            p_vec,
            timeout=constructor_timeout,
            rl_verified=rl_verified,
            witness_graph=witness_graph,
        )
        report.results.append(realiz_result)
        report.results.append(_check_final_validation(p_vec, conjecture, witness))
        if witness is not None and _GRAPH_AVAILABLE:
            try:
                Gi = nx.convert_node_labels_to_integers(witness)
                report.witness_edges = sorted(
                    tuple(sorted(e)) for e in Gi.edges())
            except Exception:
                pass
        return report


def worker_setpgrp(parent_pid: int | None = None) -> None:
    """Pool-worker initializer: own process group, so that an early pool
    teardown can killpg() the worker TOGETHER with its plantri subprocesses
    (killing just the worker would orphan running plantri enumerations).

    Also registers PR_SET_PDEATHSIG: if the orchestrator dies WITHOUT running
    its finally blocks (Ctrl-C while the pool lives in a daemon thread, crash,
    SIGKILL), the kernel kills the worker — otherwise it would survive forever
    blocked on the pool's call queue, since sibling workers hold the queue
    pipe open and EOF never arrives."""
    os.setpgrp()
    from agent.procutil import set_pdeathsig
    set_pdeathsig(expected_ppid=parent_pid)


def kill_pool_pgroups(ex) -> None:
    """Forcibly end a ProcessPoolExecutor's workers AND their subprocesses.

    Workers are process-group leaders (see worker_setpgrp), so killpg reaches
    the plantri children too — plain Process.kill() would orphan them and
    leave enumerations burning CPU past their budget. Without this, a CE
    found early looks like a hang: the interpreter's atexit join waits up to
    a full candidate timeout for in-flight workers.

    Must be called BEFORE ex.shutdown() — shutdown nulls ex._processes."""
    import signal
    for p in list((getattr(ex, "_processes", None) or {}).values()):
        try:
            os.killpg(p.pid, signal.SIGKILL)
        except Exception:
            pass


def check_pvector_worker(
    p_vec: dict[int, int],
    conjecture,
    constructor_timeout: float = 30.0,
    plantri_jobs: int = 0,
    seed: int | None = None,
) -> CheckReport:
    """Process-pool entry point (module-level so it pickles; this module's
    imports are light enough for spawn workers). `plantri_jobs` caps each
    worker's internal plantri parallelism so that
    pool_size x plantri_jobs ~= available cores. `seed` makes the stochastic
    constructor tiers reproducible and lets retry rounds draw different
    trajectories instead of repeating a lost draw."""
    if plantri_jobs > 0:
        os.environ["PLANTRI_JOBS"] = str(plantri_jobs)
    if seed is not None:
        os.environ["CE_CONSTRUCT_SEED"] = str(seed)
        import random
        random.seed(seed)
    return PVectorCheckAgent().run_silent(
        p_vec, conjecture, constructor_timeout=constructor_timeout)
