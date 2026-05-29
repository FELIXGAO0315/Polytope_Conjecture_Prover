"""
agent/tools/pvec_eval.py — Pure polytope math: p-vector validation & LaTeX evaluation.

No dependencies on orchestrator or other agent modules — safe to import anywhere.
"""
from __future__ import annotations

import re
from typing import Optional


# ── Dehn-Sommerville ──────────────────────────────────────────────────────────

def _dehn_sommerville(p_vec: dict[int, int]) -> int:
    """Return sum((6-k)*p_k) — must equal 12 for a valid simple 3-polytope."""
    return sum((6 - k) * v for k, v in p_vec.items() if v > 0)


def is_valid_simple_polytope(p_vec: dict[int, int]) -> tuple[bool, str]:
    """Check Dehn-Sommerville + non-negativity + minimum size."""
    if not p_vec or all(v <= 0 for v in p_vec.values()):
        return False, "empty p-vector"
    if any(v < 0 for v in p_vec.values()):
        neg = {k: v for k, v in p_vec.items() if v < 0}
        return False, f"negative face counts: {neg}"
    ds = _dehn_sommerville(p_vec)
    if ds != 12:
        return False, f"Dehn-Sommerville fails: sum((6-k)·p_k) = {ds} ≠ 12"
    f2 = sum(p_vec.values())
    if f2 < 4:
        return False, f"f2 = {f2} < 4 (tetrahedron is the smallest)"
    return True, ""


def p_vec_props(p_vec: dict[int, int]) -> dict:
    """Compute derived properties for a p-vector dict."""
    f2 = sum(p_vec.values())
    two_e = sum(k * v for k, v in p_vec.items())
    e = two_e // 2
    v_count = two_e // 3  # 2e = 3v for simple polytopes
    kmax = max(p_vec.keys(), default=6)
    return {
        "p3": p_vec.get(3, 0),
        "p4": p_vec.get(4, 0),
        "p5": p_vec.get(5, 0),
        "p6": p_vec.get(6, 0),
        "sum_pk_after_p6": sum(v for k, v in p_vec.items() if k > 6),
        "f2": f2,
        "num_vertices": v_count,
        "num_edges": e,
        "p_vector": [p_vec.get(k, 0) for k in range(3, kmax + 1)],
    }


# ── LaTeX expression evaluator ────────────────────────────────────────────────

def _clean_latex_ws(s: str) -> str:
    """Remove LaTeX whitespace commands and collapse spaces."""
    s = re.sub(r'\\[;,!:]', ' ', s)
    s = re.sub(r'\\quad|\\qquad', ' ', s)
    s = s.replace(r'\ ', ' ')
    return re.sub(r'\s+', ' ', s).strip()


def _expand_fractions(s: str) -> str:
    r"""Replace \frac{A}{B} and \tfrac{A}{B} with (A/B)."""
    s = re.sub(r'\\[tds]?frac\{([^}]+)\}\{([^}]+)\}', r'(\1/\2)', s)
    return s


def _implicit_mul_to_explicit(s: str) -> str:
    r"""Replace LaTeX thin-space implicit multiplication with explicit *.

    In IRIS LaTeX, patterns like  5\,\sum  or  2\,p_k  mean multiplication.
    This must be applied BEFORE stripping \, as whitespace.
    """
    s = re.sub(r'(\d)\s*\\,\s*(\\[a-zA-Z]|[a-z_])', r'\1*\2', s)
    s = re.sub(r'(\))\s*\\,\s*(\\[a-zA-Z]|[a-z_])', r'\1*\2', s)
    return s


def _eval_rhs_expr(expr: str, p_vec: dict[int, int]) -> Optional[float]:
    """Evaluate a RHS expression from either LaTeX or JSON-format conjecture."""
    s = expr

    s = _expand_fractions(s)
    s = _implicit_mul_to_explicit(s)
    s = _clean_latex_ws(s)

    def _replace_sum(m: re.Match) -> str:
        k_min = int(m.group(1))
        return str(sum(v for k, v in p_vec.items() if k >= k_min))

    # LaTeX sum notation
    s = re.sub(r'\\sum_\{k\s*(?:\\geq|\\ge|>=)\s*(\d+)\}\s*p_k', _replace_sum, s)

    # JSON format: sum_pk_after_p6 = sum of p_k for k > 6
    sum_after_6 = sum(v for k, v in p_vec.items() if k > 6)
    s = re.sub(r'\bsum_pk_after_p6\b', str(sum_after_6), s)
    s = re.sub(r'\bsum_pk_k>=7\b', str(sum_after_6), s)

    # LaTeX p_{k} and p_k
    s = re.sub(r'p_\{(\d+)\}', lambda m: str(p_vec.get(int(m.group(1)), 0)), s)
    s = re.sub(r'p_(\d+)', lambda m: str(p_vec.get(int(m.group(1)), 0)), s)

    # JSON format: p3 p4 p5 p6 (no underscore) — must come after p_k replacements
    for k in [3, 4, 5, 6]:
        s = re.sub(rf'\bp{k}\b', str(p_vec.get(k, 0)), s)

    f2 = sum(p_vec.values())
    s = re.sub(r'f_\{2\}|f_2\b', str(f2), s)

    s = re.sub(r'\\[a-zA-Z]+', '', s)
    s = s.replace('{', '(').replace('}', ')')

    s = re.sub(r'(\))\s+(\d)', r'\1*\2', s)
    s = re.sub(r'(\d)\s+(\d)', r'\1*\2', s)
    s = re.sub(r'\s+', ' ', s).strip()

    try:
        return float(eval(s, {"__builtins__": {}}, {}))
    except Exception:
        return None


def _eval_hypothesis(hyp: str, p_vec: dict[int, int]) -> bool:
    """Return True if the hypothesis is satisfied by p_vec.

    Handles both LaTeX format (\\text{simple}, f_2 \\geq N) and
    JSON formula format ((is_simple), (f_2>=_19), (sum_pk_k>=7 >= 1)).
    """
    s = hyp.strip()
    s_nospace = s.replace(' ', '')

    # JSON: (is_simple) or is_simple — structural assumption, always True
    if re.fullmatch(r'\(?is_simple\)?', s):
        return True

    # JSON: (f_2>=_N) — f2 >= N
    m = re.match(r'\(?f_2>=_(\d+)\)?$', s_nospace)
    if m:
        return sum(p_vec.values()) >= int(m.group(1))

    # JSON: (f_2<=_N)
    m = re.match(r'\(?f_2<=_(\d+)\)?$', s_nospace)
    if m:
        return sum(p_vec.values()) <= int(m.group(1))

    # JSON: (sum_pk_k>=7 >= N) — sum of p_k for k>=7 >= N
    m = re.match(r'\(?sum_pk_k>=7\s*>=\s*(\d+)\)?$', s)
    if m:
        return sum(v for k, v in p_vec.items() if k >= 7) >= int(m.group(1))

    # JSON: (sum_pk_k>=7 <= N)
    m = re.match(r'\(?sum_pk_k>=7\s*<=\s*(\d+)\)?$', s)
    if m:
        return sum(v for k, v in p_vec.items() if k >= 7) <= int(m.group(1))

    # LaTeX: \text{...} — always true (simplicity is a structural assumption)
    if re.fullmatch(r'\\text\{[^}]*\}', s):
        return True

    # \sum_{k \geq N} p_k \geq M
    m = re.match(
        r'\\sum_\{k\s*(?:\\geq|\\ge|>=)\s*(\d+)\}\s*p_k\s*(?:\\geq|>=)\s*(\d+)', s
    )
    if m:
        k_min, bound = int(m.group(1)), int(m.group(2))
        return sum(v for k, v in p_vec.items() if k >= k_min) >= bound

    # \sum_{k \geq N} p_k \leq M
    m = re.match(
        r'\\sum_\{k\s*(?:\\geq|\\ge|>=)\s*(\d+)\}\s*p_k\s*(?:\\leq|<=)\s*(\d+)', s
    )
    if m:
        k_min, bound = int(m.group(1)), int(m.group(2))
        return sum(v for k, v in p_vec.items() if k >= k_min) <= bound

    # f_2 \geq N
    m = re.match(r'f_(?:\{2\}|2)\s*(?:\\geq|>=)\s*(\d+)', s)
    if m:
        return sum(p_vec.values()) >= int(m.group(1))

    # f_2 \leq N
    m = re.match(r'f_(?:\{2\}|2)\s*(?:\\leq|<=)\s*(\d+)', s)
    if m:
        return sum(p_vec.values()) <= int(m.group(1))

    # p_k \geq N
    m = re.match(r'p_\{?(\d+)\}?\s*(?:\\geq|>=)\s*(\d+)', s)
    if m:
        return p_vec.get(int(m.group(1)), 0) >= int(m.group(2))

    # p_k \leq N
    m = re.match(r'p_\{?(\d+)\}?\s*(?:\\leq|<=)\s*(\d+)', s)
    if m:
        return p_vec.get(int(m.group(1)), 0) <= int(m.group(2))

    # p_k = N
    m = re.match(r'p_\{?(\d+)\}?\s*=\s*(\d+)', s)
    if m:
        return p_vec.get(int(m.group(1)), 0) == int(m.group(2))

    # Unknown hypothesis — assume satisfied (conservative)
    return True


def _eval_conclusion_violated(conc: str, p_vec: dict[int, int]) -> tuple[bool, str]:
    """Return (is_violated, detail). Violated → p_vec is a counterexample.

    Handles both LaTeX (p_6, p_{6}) and JSON (p6) formats.
    """
    s = _clean_latex_ws(conc.strip())

    # p_6 / p_{6} / p6  >=  EXPR — violated when p6 < EXPR
    m = re.match(r'p_?\{?6\}?\s*(?:\\geq|>=)\s*(.+)', s, re.DOTALL)
    if m:
        rhs = _eval_rhs_expr(m.group(1).strip(), p_vec)
        if rhs is None:
            return False, "could not evaluate RHS"
        p6 = float(p_vec.get(6, 0))
        if p6 < rhs:
            return True, f"p6={p6} < RHS={rhs:.4f} (violation)"
        return False, f"p6={p6} >= RHS={rhs:.4f} (holds)"

    # p_6 / p_{6} / p6  <=  EXPR — violated when p6 > EXPR
    m = re.match(r'p_?\{?6\}?\s*(?:\\leq|<=)\s*(.+)', s, re.DOTALL)
    if m:
        rhs = _eval_rhs_expr(m.group(1).strip(), p_vec)
        if rhs is None:
            return False, "could not evaluate RHS"
        p6 = float(p_vec.get(6, 0))
        if p6 > rhs:
            return True, f"p6={p6} > RHS={rhs:.4f} (violation)"
        return False, f"p6={p6} <= RHS={rhs:.4f} (holds)"

    return False, f"unrecognised conclusion form: {conc[:80]}"


def is_counterexample(
    p_vec: dict[int, int], conjecture
) -> tuple[bool, str]:
    """Full CE check: polytope validity + hypotheses + conclusion violation."""
    ok, reason = is_valid_simple_polytope(p_vec)
    if not ok:
        return False, f"invalid polytope: {reason}"

    for hyp in conjecture.hypotheses:
        if not _eval_hypothesis(hyp, p_vec):
            return False, f"hypothesis not satisfied: {hyp[:60]}"

    violated, detail = _eval_conclusion_violated(conjecture.conclusion, p_vec)
    if not violated:
        return False, detail

    return True, detail
