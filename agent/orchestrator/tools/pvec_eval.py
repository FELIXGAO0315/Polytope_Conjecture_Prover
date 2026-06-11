"""
agent/tools/pvec_eval.py — Pure polytope math: p-vector validation & LaTeX evaluation.

No dependencies on orchestrator or other agent modules — safe to import anywhere.
"""
from __future__ import annotations

import re
from fractions import Fraction
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


def _eval_rhs_expr(expr: str, p_vec: dict[int, int]) -> Optional[Fraction]:
    """Evaluate a RHS expression from either LaTeX or JSON-format conjecture.

    Returns an exact Fraction (decimal literals like -4.5 and \\frac{..}{3}
    divisions are exact), so boundary comparisons p6 < RHS never flip due to
    binary floating-point rounding."""
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

    # JSON format: p3 p4 … pN (no underscore) — must come after p_k replacements
    # (was hardcoded to 3..6, which left p7/p8/… tokens unevaluated)
    s = re.sub(r'\bp(\d+)\b', lambda m: str(p_vec.get(int(m.group(1)), 0)), s)

    f2 = sum(p_vec.values())
    s = re.sub(r'f_\{2\}|f_2\b', str(f2), s)

    s = re.sub(r'\\[a-zA-Z]+', '', s)
    s = s.replace('{', '(').replace('}', ')')

    s = re.sub(r'(\))\s+(\d)', r'\1*\2', s)
    s = re.sub(r'(\d)\s+(\d)', r'\1*\2', s)
    s = re.sub(r'\s+', ' ', s).strip()

    try:
        # Wrap every numeric literal in Fraction so all arithmetic is exact
        # (1/3 stays 1/3; '4.5' becomes 9/2 — Fraction parses decimal strings).
        s_frac = re.sub(r'(\d+\.\d+|\d+)', r"F('\1')", s)
        return Fraction(eval(s_frac, {"__builtins__": {}}, {"F": Fraction}))
    except Exception:
        return None


# ── Compiled evaluators ───────────────────────────────────────────────────────
# The random walk calls hypothesis/conclusion evaluation millions of times per
# conjecture. Re-running the full regex pipeline + eval + Fraction parsing on
# every call is the dominant cost, so each conjecture string is compiled ONCE
# into a closure; per-call work is then dict lookups + precompiled bytecode.

from functools import lru_cache as _lru_cache


@_lru_cache(maxsize=None)
def _frac(s: str) -> Fraction:
    return Fraction(s)


def _compile_rhs(expr: str):
    """Compile a RHS expression into (evaluator, None) or (None, error).
    Variables: P_k = p_vec.get(k, 0), S_k = Σ_{j≥k} p_j, F2 = Σ p_j."""
    s = expr
    s = _expand_fractions(s)
    s = _implicit_mul_to_explicit(s)
    s = _clean_latex_ws(s)
    # name-based placeholders (digits after _ or a letter are protected from
    # the Fraction-wrap below by the (?<!\w) lookbehind)
    s = re.sub(r'\\sum_\{k\s*(?:\\geq|\\ge|>=)\s*(\d+)\}\s*p_k', lambda m: f"S_{m.group(1)}", s)
    s = re.sub(r'\bsum_pk_after_p6\b', 'S_7', s)
    s = re.sub(r'\bsum_pk_k>=7\b', 'S_7', s)
    s = re.sub(r'p_\{(\d+)\}', lambda m: f"P_{m.group(1)}", s)
    s = re.sub(r'p_(\d+)', lambda m: f"P_{m.group(1)}", s)
    s = re.sub(r'\bp(\d+)\b', lambda m: f"P_{m.group(1)}", s)
    s = re.sub(r'f_\{2\}|f_2\b', 'F2', s)
    s = re.sub(r'\\[a-zA-Z]+', '', s)
    s = s.replace('{', '(').replace('}', ')')
    s = re.sub(r'(\))\s+(\d)', r'\1*\2', s)
    s = re.sub(r'(\d)\s+(\d)', r'\1*\2', s)
    s = re.sub(r'(?<!\w)(\d+\.\d+|\d+)', r"F('\1')", s)

    p_keys = sorted({int(k) for k in re.findall(r'\bP_(\d+)\b', s)})
    s_keys = sorted({int(k) for k in re.findall(r'\bS_(\d+)\b', s)})
    needs_f2 = bool(re.search(r'\bF2\b', s))
    try:
        code = compile(s.strip(), '<rhs>', 'eval')
    except SyntaxError:
        return None

    def _eval(p_vec: dict[int, int]) -> Optional[Fraction]:
        env: dict = {'F': _frac}
        for k in p_keys:
            env[f'P_{k}'] = p_vec.get(k, 0)
        for k in s_keys:
            env[f'S_{k}'] = sum(v for kk, v in p_vec.items() if kk >= k)
        if needs_f2:
            env['F2'] = sum(p_vec.values())
        try:
            return Fraction(eval(code, {"__builtins__": {}}, env))
        except Exception:
            return None

    return _eval


_CONC_CACHE: dict[str, tuple] = {}


def _compile_conclusion(conc: str) -> tuple:
    """Return ('ge'|'le', rhs_evaluator) or ('unknown', None)."""
    s = _clean_latex_ws(conc.strip())
    m = re.match(r'p_?\{?6\}?\s*(?:\\geq|>=)\s*(.+)', s, re.DOTALL)
    if m:
        fn = _compile_rhs(m.group(1).strip())
        return ('ge', fn) if fn else ('unknown', None)
    m = re.match(r'p_?\{?6\}?\s*(?:\\leq|<=)\s*(.+)', s, re.DOTALL)
    if m:
        fn = _compile_rhs(m.group(1).strip())
        return ('le', fn) if fn else ('unknown', None)
    return ('unknown', None)


_UNKNOWN_HYPS_WARNED: set[str] = set()


_HYP_CACHE: dict[str, object] = {}


def _compile_hypothesis(hyp: str):
    """Compile one hypothesis string into a fast closure p_vec -> bool.

    Handles both LaTeX format (\\text{simple}, f_2 \\geq N) and
    JSON formula format ((is_simple), (f_2>=_19), (sum_pk_k>=7 >= 1)).

    Parentheses are stripped before matching: the conjecture parser splits
    nested "and" groups and can leave unbalanced parens on individual
    hypotheses (e.g. "((is_simple)" / "(f_2>=_13))").

    FAIL-CLOSED: an unrecognised hypothesis compiles to (lambda: False), so
    the candidate is rejected. The previous default of True silently skipped
    unparsable hypotheses and produced a false counterexample (C3:
    "(f_2>=_13))" never matched, so a CE with f2=8 passed an f2≥13 hypothesis).
    """
    s = _clean_latex_ws(hyp.strip())
    flat = re.sub(r'[()]', '', s).strip()      # parens carry no meaning in any form
    flat_nospace = flat.replace(' ', '')

    # Structural assumptions — always True
    if flat == 'is_simple' or re.fullmatch(r'\\text\{[^}]*\}', s):
        return lambda pv: True

    # f2 bounds: JSON f_2>=_N / f_2<=_N and LaTeX f_2 \geq N / \leq N
    m = (re.fullmatch(r'f_2(>=|<=)_(\d+)', flat_nospace)
         or re.match(r'f_(?:\{2\}|2)\s*(\\geq|\\leq|>=|<=)\s*(\d+)', flat))
    if m:
        op, n = m.group(1), int(m.group(2))
        if op in ('>=', '\\geq'):
            return lambda pv: sum(pv.values()) >= n
        return lambda pv: sum(pv.values()) <= n

    # Σ_{k≥K} p_k bounds: JSON sum_pk_k>=7 and LaTeX \sum_{k≥K} p_k
    m = re.fullmatch(r'sum_pk_k>=7\s*(>=|<=)\s*(\d+)', flat)
    if m:
        op, n = m.group(1), int(m.group(2))
        if op == '>=':
            return lambda pv: sum(v for k, v in pv.items() if k >= 7) >= n
        return lambda pv: sum(v for k, v in pv.items() if k >= 7) <= n
    m = re.match(
        r'\\sum_\{k\s*(?:\\geq|\\ge|>=)\s*(\d+)\}\s*p_k\s*(\\geq|\\leq|>=|<=)\s*(\d+)', flat
    )
    if m:
        k_min, op, n = int(m.group(1)), m.group(2), int(m.group(3))
        if op in ('>=', '\\geq'):
            return lambda pv: sum(v for k, v in pv.items() if k >= k_min) >= n
        return lambda pv: sum(v for k, v in pv.items() if k >= k_min) <= n

    # p_k bounds / equality
    m = re.match(r'p_\{?(\d+)\}?\s*(\\geq|\\leq|>=|<=|=)\s*(\d+)', flat)
    if m:
        k, op, n = int(m.group(1)), m.group(2), int(m.group(3))
        if op in ('>=', '\\geq'):
            return lambda pv: pv.get(k, 0) >= n
        if op in ('<=', '\\leq'):
            return lambda pv: pv.get(k, 0) <= n
        return lambda pv: pv.get(k, 0) == n

    # Unknown hypothesis — FAIL CLOSED (reject candidate), warn once per format
    if hyp not in _UNKNOWN_HYPS_WARNED:
        _UNKNOWN_HYPS_WARNED.add(hyp)
        print(f"[pvec_eval] WARNING: unrecognised hypothesis {hyp!r} — treating as "
              f"NOT satisfied (fail-closed). If this hypothesis is legitimate, add "
              f"a pattern for it in pvec_eval._compile_hypothesis.")
    return lambda pv: False


def _eval_hypothesis(hyp: str, p_vec: dict[int, int]) -> bool:
    """Return True if the hypothesis is satisfied by p_vec (compiled & cached:
    the regex parse runs once per hypothesis string, not once per call)."""
    fn = _HYP_CACHE.get(hyp)
    if fn is None:
        fn = _compile_hypothesis(hyp)
        _HYP_CACHE[hyp] = fn
    return fn(p_vec)


def _eval_conclusion_violated(conc: str, p_vec: dict[int, int]) -> tuple[bool, str]:
    """Return (is_violated, detail). Violated → p_vec is a counterexample.

    Handles both LaTeX (p_6, p_{6}) and JSON (p6) formats. Compiled & cached:
    the regex/eval pipeline runs once per conclusion string; per call is dict
    lookups + precompiled bytecode with exact Fraction arithmetic.
    """
    entry = _CONC_CACHE.get(conc)
    if entry is None:
        entry = _compile_conclusion(conc)
        _CONC_CACHE[conc] = entry
    kind, rhs_fn = entry

    if kind == 'unknown':
        return False, f"unrecognised conclusion form: {conc[:80]}"

    rhs = rhs_fn(p_vec)
    if rhs is None:
        return False, "could not evaluate RHS"
    p6 = p_vec.get(6, 0)              # int vs Fraction — comparison is exact

    if kind == 'ge':                  # violated when p6 < EXPR
        if p6 < rhs:
            return True, f"p6={float(p6)} < RHS={float(rhs):.4f} (violation)"
        return False, f"p6={float(p6)} >= RHS={float(rhs):.4f} (holds)"
    else:                             # 'le' — violated when p6 > EXPR
        if p6 > rhs:
            return True, f"p6={float(p6)} > RHS={float(rhs):.4f} (violation)"
        return False, f"p6={float(p6)} <= RHS={float(rhs):.4f} (holds)"


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
