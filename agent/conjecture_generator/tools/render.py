"""
agent/conjecture_generator/tools/render.py — txgraffiti → project formula DSL.

Converts Graffiti3 Conjecture objects into the canonical formula format used
across this repo:

    if ((is_simple)  and  (f_2>=_N)), then p6 >= (a*p3 + b*sum_pk_after_p6 + c)

Ported from the upstream Polytope repo's conjecture agent (same author).
"""
from __future__ import annotations

import re
from fractions import Fraction
from types import SimpleNamespace
from typing import Dict, List, Optional, Tuple

import numpy as np

from agent.conjectures import canonicalize_formula, canonicalize_hypothesis_tokens

_LINEAR_ALLOWED_VARS = {"p3", "p4", "p5", "p6", "sum_pk_after_p6"}
_COL_ALIASES = {
    "p_3": "p3",
    "p_4": "p4",
    "p_5": "p5",
    "p_6": "p6",
    "p3": "p3",
    "p4": "p4",
    "p5": "p5",
    "p6": "p6",
    "sum_pk_k>=7": "sum_pk_after_p6",
    "sum_pk_after_p6": "sum_pk_after_p6",
}


def _format_number(value: float) -> str:
    try:
        fval = float(value)
    except Exception:
        return str(value)
    if abs(fval) < 1e-12:
        fval = 0.0
    if abs(fval - round(fval)) < 1e-9:
        return str(int(round(fval)))
    return f"{fval:.10g}"


def _map_column_name(name: str) -> str:
    return _COL_ALIASES.get(name, name)


def _predicate_to_str(pred) -> str:
    if pred is None:
        return "true"
    try:
        raw = repr(pred)
    except Exception:
        return "true"
    for old, new in (("∧", " and "), ("∨", " or "), ("¬", " not "), ("TRUE", "true")):
        raw = raw.replace(old, new)
    raw = re.sub(r"\bsimple_polytope\b", "is_simple", raw)
    raw = re.sub(r"\bpolytope\b", "is_simple", raw)
    raw = raw.strip()
    if raw.startswith("(") and raw.endswith(")"):
        inner = raw[1:-1].strip()
        if inner:
            raw = inner
    return canonicalize_hypothesis_tokens(raw) or "true"


def _expr_to_code(expr) -> Optional[str]:
    """Convert a txgraffiti Expr to a python expression over props.get(...)."""
    try:
        import txgraffiti.graffiti3.exprs as exprs  # type: ignore
    except Exception:
        return None

    Const = exprs.Const
    ColumnTerm = exprs.ColumnTerm
    LinearForm = exprs.LinearForm
    BinOp = exprs.BinOp
    UnaryOp = exprs.UnaryOp
    LogOp = exprs.LogOp
    Func2Op = getattr(exprs, "Func2Op", None)

    def col_to_var(col: str) -> Optional[str]:
        name = _map_column_name(col)
        if name == "sum_pk_k>=7":
            name = "sum_pk_after_p6"
        if name not in _LINEAR_ALLOWED_VARS:
            return None
        return f"props.get('{name}', 0)"

    def _rec(node) -> Optional[str]:
        if isinstance(node, Const):
            # Prefer fraction literals in repr to avoid precision drift (e.g. 1/50).
            raw_repr = repr(node)
            frac_match = re.search(r"(-?\d+(?:\.\d+)?)/(-?\d+(?:\.\d+)?)", raw_repr)
            if frac_match:
                try:
                    val = float(Fraction(frac_match.group(1)) / Fraction(frac_match.group(2)))
                    return _format_number(val)
                except Exception:
                    pass
            return _format_number(getattr(node, "value", 0.0))
        if isinstance(node, ColumnTerm):
            return col_to_var(node.col)
        if isinstance(node, LinearForm):
            parts: List[str] = []
            if abs(float(node.intercept)) >= 1e-12:
                parts.append(_format_number(node.intercept))
            for coef, col in node.terms:
                v = col_to_var(col)
                if not v:
                    return None
                if abs(float(coef)) < 1e-12:
                    continue
                if abs(float(coef) - 1.0) < 1e-12:
                    parts.append(f"{v}")
                elif abs(float(coef) + 1.0) < 1e-12:
                    parts.append(f"-{v}")
                else:
                    parts.append(f"{_format_number(coef)}*({v})")
            if not parts:
                return "0"
            return " + ".join(parts).replace("+ -", "- ")
        if isinstance(node, BinOp):
            op_map = {
                np.add: "+", np.subtract: "-", np.multiply: "*",
                np.divide: "/", np.mod: "%", np.power: "**",
            }
            sym = op_map.get(getattr(node, "fn", None))
            l = _rec(getattr(node, "left", None))
            r = _rec(getattr(node, "right", None))
            if sym is None or l is None or r is None:
                return None
            return f"({l} {sym} {r})"
        if isinstance(node, UnaryOp):
            fn = getattr(node, "fn", None)
            arg = _rec(getattr(node, "arg", None))
            if arg is None:
                return None
            if fn is np.sqrt:
                return f"np.sqrt({arg})"
            if fn is np.abs:
                return f"abs({arg})"
            if fn is np.negative:
                return f"(-({arg}))"
            if fn is np.exp:
                return f"np.exp({arg})"
            return None
        if Func2Op and isinstance(node, Func2Op):
            name = getattr(node, "name", "min")
            l = _rec(getattr(node, "left", None))
            r = _rec(getattr(node, "right", None))
            if l is None or r is None:
                return None
            safe = "min" if name == "min" else ("max" if name == "max" else name)
            return f"{safe}({l}, {r})"
        if isinstance(node, LogOp):
            arg = _rec(getattr(node, "arg", None))
            if arg is None:
                return None
            base = getattr(node, "base", None)
            if base is None:
                return f"np.log({arg})"
            try:
                bval = float(base)
            except Exception:
                return None
            if abs(bval - 2.0) < 1e-12:
                return f"np.log2({arg})"
            if abs(bval - np.e) < 1e-12:
                return f"np.log({arg})"
            return f"(np.log({arg})/np.log({bval}))"
        return None

    return _rec(expr)


_PROPS_TO_PLAIN = {
    "props.get('p6', 0)": "p6",
    "props.get('p_6', 0)": "p6",
    "props.get('p3', 0)": "p3",
    "props.get('p_3', 0)": "p3",
    "props.get('p4', 0)": "p4",
    "props.get('p_4', 0)": "p4",
    "props.get('p5', 0)": "p5",
    "props.get('p_5', 0)": "p5",
    "props.get('sum_pk_after_p6', 0)": "sum_pk_after_p6",
    "props.get('sum_pk_k', 0)": "sum_pk_after_p6",
}


def _render_graffiti3_conjecture(obj) -> Optional[str]:
    """Render a txgraffiti.graffiti3 Conjecture object (p6 bounds only)."""
    try:
        from txgraffiti.graffiti3.relations import Ge, Le, AllOf  # type: ignore
    except Exception:
        return None

    rel = getattr(obj, "relation", None)
    cond = getattr(obj, "condition", None) or getattr(obj, "_resolved_condition", None)
    if rel is None:
        return None

    if isinstance(rel, AllOf):
        for part in getattr(rel, "parts", []):
            rendered = _render_graffiti3_conjecture(
                SimpleNamespace(relation=part, condition=cond))
            if rendered:
                return rendered
        return None

    is_ge = isinstance(rel, Ge)
    is_le = isinstance(rel, Le)
    if not (is_ge or is_le):
        return None

    lhs_code = _expr_to_code(getattr(rel, "left", None))
    rhs_code = _expr_to_code(getattr(rel, "right", None))
    if lhs_code is None or rhs_code is None:
        return None

    p6_names = ("p6", "p_6", "props.get('p6', 0)", "props.get('p_6', 0)")
    if lhs_code not in p6_names:
        if rhs_code in p6_names:
            lhs_code, rhs_code = rhs_code, lhs_code
            is_ge, is_le = is_le, is_ge
        else:
            return None

    for pat, repl in _PROPS_TO_PLAIN.items():
        lhs_code = lhs_code.replace(pat, repl)
        rhs_code = rhs_code.replace(pat, repl)

    # Upper bounds stay in `p6 <= expr` form — the only upper-bound form
    # pvec_eval._compile_conclusion can evaluate (upstream's `-p6 >= -expr`
    # convention compiles to 'unknown' here and would be unfalsifiable).
    op = "<=" if is_le else ">="
    cond_str = _predicate_to_str(cond)
    return canonicalize_formula(f"if ({cond_str}), then {lhs_code} {op} ({rhs_code})")


def _parse_linear(expr: str) -> Tuple[Dict[str, float], float]:
    expr_no_space = expr.replace(" ", "")
    coef = {key: 0.0 for key in ["p_3", "p_4", "p_5", "p_6", "sum_pk_k>=7"]}
    const = 0.0
    pattern = r"([+-]?(?:\d+(?:/\d+)?(?:\.\d+)?))\*(p_\d+|sum_pk_k>=7)"
    for match in re.finditer(pattern, expr_no_space):
        c_str, var = match.groups()
        try:
            value = float(Fraction(c_str)) if "/" in c_str else float(c_str)
        except Exception:
            value = 0.0
        if var in coef:
            coef[var] += value
    stripped = re.sub(pattern, "", expr_no_space)
    stripped = stripped.replace("(", "+").replace(")", "+")
    for match in re.finditer(r"([+-]?\d+(?:/\d+)?(?:\.\d+)?)", stripped):
        num = match.group(1)
        try:
            const += float(Fraction(num)) if "/" in num else float(num)
        except Exception:
            continue
    return coef, const


def _build_rhs(coeffs: Dict[str, float], const_val: float) -> str:
    terms: List[str] = []
    mapping = {
        "p_3": "p3",
        "p_4": "p4",
        "p_5": "p5",
        "sum_pk_k>=7": "sum_pk_after_p6",
        "sum_pk_after_p6": "sum_pk_after_p6",
    }
    for key, out_name in mapping.items():
        val = coeffs.get(key, 0.0)
        if abs(val) < 1e-12:
            continue
        terms.append(f"{val:.10g}*{out_name}")
    if abs(const_val) >= 1e-12 or not terms:
        terms.append(f"{const_val:.10g}")
    return " + ".join(terms)


def render_txgraffiti_conjecture(obj) -> Optional[str]:
    """Render any supported txgraffiti conjecture object to the formula DSL."""
    rendered = _render_graffiti3_conjecture(obj)
    if rendered:
        return rendered

    # String-repr fallback for objects the structured path cannot handle.
    s = str(obj)

    match_ge = re.search(r"<Conj\s*\((.*?)\)\s*→\s*\(p_6\s*>=\s*(.*)\)>", s)
    if match_ge:
        hyp_str, rhs_expr = match_ge.group(1), match_ge.group(2)
        coef, const = _parse_linear(rhs_expr)
        return canonicalize_formula(
            f"if ({hyp_str}), then p6 >= ({_build_rhs(coef, const)})")

    match_le = re.search(r"<Conj\s*\((.*?)\)\s*→\s*\(p_6\s*<=\s*(.*)\)>", s)
    if match_le:
        hyp_str, rhs_expr = match_le.group(1), match_le.group(2)
        coef, const = _parse_linear(rhs_expr)
        return canonicalize_formula(
            f"if ({hyp_str}), then p6 <= ({_build_rhs(coef, const)})")

    return None
