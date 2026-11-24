#!/usr/bin/env python3
"""Export the repository's *decided* conjectures into a trustworthy JSON dataset
for downstream LLM / RL training ("problem + machine-checkable ground truth").

Design contract (do NOT relax without explicit sign-off):

  * Only NEW files are written (everything lands under --out, default ``export/``).
    Nothing in the repository is modified and no LLM / API code is invoked.
  * Only two label classes are exported:
        label="false"  — refuted by an explicit, RE-VERIFIED counterexample
        label="true"   — proved by a Lean file that passes the repo's own
                         proof-qualification logic (agent/conjectures.py)
    unsolved / prover_failed / not_entailed / timeout … are all excluded.
  * The ``status`` field is never trusted on its own. Every counterexample is
    re-verified from scratch. CRUCIALLY the re-verification uses EXACT rational
    arithmetic (fractions.Fraction), NOT floats — see the "float artifact"
    note below.

Exact-arithmetic rationale (float-artifact bug, 2026):
  The DSL ``formula`` stores linear coefficients as ROUNDED DECIMALS, e.g.
  ``0.9285714286`` for 13/14. The pipeline's own evaluator parses these decimals
  literally, so a boundary case like C48 (witness {3:2,4:3}: exact RHS = 0,
  p6 = 0) computes a spurious RHS ≈ 2e-10 and is mislabeled a counterexample.
  Here every decimal coefficient is recovered with
  ``Fraction(str).limit_denominator(1000)`` (verified within 1e-8 of the
  decimal) and ALL comparisons are exact; a violation must be STRICT under exact
  arithmetic. Counterexamples that only "violate" under decimal rounding are
  dropped as ``float_artifact`` and reported so the ORIGINAL pipeline can
  re-adjudicate them.

Notation (confirmed against source — see pvec_eval / check_pvector):
  * ``is_simple`` / ``is_3_connected`` : structural, always satisfied.
  * ``f_2``               : total number of faces  = sum_{k>=3} p_k
  * ``p_k`` / ``p6``      : number of k-gonal faces (p6 = number of hexagons)
  * ``sum_pk_after_p6``   : sum of p_k for k > 6  (i.e. k >= 7)
  * ``sum_pk_k>=7``       : sum of p_k for k >= 7 (identical to the above)
  * Dehn-Sommerville      : sum_{k>=3} (6-k) * p_k = 12 for a simple 3-polytope
"""
from __future__ import annotations

import argparse
import json
import os
import re
import sys
from collections import Counter
from fractions import Fraction
from typing import Optional

# ── make the repo root importable so ``agent`` resolves regardless of CWD ─────
_THIS = os.path.abspath(__file__)
_REPO_ROOT = os.path.dirname(os.path.dirname(_THIS))
if _REPO_ROOT not in sys.path:
    sys.path.insert(0, _REPO_ROOT)

from agent.conjectures import (           # noqa: E402
    ConjectureSpec, canonicalize_formula, _entry_num, _has_active_sorry,
)
from agent.orchestrator.tools.conjecture_parser import (   # noqa: E402
    ParsedConjecture, _IF_THEN_RE, _strip_outer_parens, _flatten_and_groups,
)
from agent.orchestrator.tools.pvec_eval import (           # noqa: E402
    is_valid_simple_polytope,
)
from agent.orchestrator.tools.check_pvector import (        # noqa: E402
    _validate_witness_graph,
)

try:
    import networkx as nx
    _NX_OK = True
except ImportError:                       # pragma: no cover
    _NX_OK = False

_STRUCTURAL = frozenset({"is_simple", "is_3_connected"})
_FAILED_HDR = re.compile(r"^--\s*Failed\s*\((\d+)\)", re.MULTILINE)
_DEC_RE = re.compile(r"\d+\.\d+")
_MAX_DENOM = 1000
_CONV_TOL = 1e-8


class UnknownToken(Exception):
    """Raised when the renderer/parser meets a token it cannot map. Fatal for
    that record — the task forbids guessing an unrecognised symbol."""


class CoefficientError(Exception):
    """Raised when a decimal coefficient cannot be recovered as a small-
    denominator rational within tolerance."""


# ══════════════════════════════════════════════════════════════════════════════
# Exact rational recovery of decimal coefficients
# ══════════════════════════════════════════════════════════════════════════════

def _rationalize(dec_str: str) -> Fraction:
    """Recover the intended rational for a rounded decimal literal.

    Uses limit_denominator(1000) and verifies the result is within 1e-8 of the
    decimal — otherwise the decimal is not a small-denominator rational and we
    refuse to guess (CoefficientError)."""
    fr = Fraction(dec_str).limit_denominator(_MAX_DENOM)
    if abs(float(fr) - float(dec_str)) >= _CONV_TOL:
        raise CoefficientError(
            f"decimal {dec_str!r} → {fr} differs by "
            f"{abs(float(fr) - float(dec_str)):.2e} ≥ {_CONV_TOL:.0e}")
    return fr


def _collect_coefficients(formula: str) -> dict[str, str]:
    """Map every decimal literal in the formula to its exact fraction string.
    Raises CoefficientError if any decimal is not a small-denominator rational."""
    out: dict[str, str] = {}
    for dec in _DEC_RE.findall(formula):
        out[dec] = str(_rationalize(dec))
    return out


# ── shared variable→value substitution (returns a string with only numerics) ──

def _substitute_vars(expr: str, pv: dict[int, int]) -> str:
    """Replace every DSL variable with its integer value from the p-vector.
    Order matters: the sum-tokens contain 'pk'/'p6' substrings, so they must be
    substituted before the generic p_k rules."""
    S7 = sum(v for k, v in pv.items() if k >= 7)
    f2 = sum(pv.values())
    s = expr
    s = re.sub(r"\bsum_pk_after_p6\b", str(S7), s)
    s = re.sub(r"sum_pk_k>=7", str(S7), s)
    s = re.sub(r"f_\{2\}|f_2\b", str(f2), s)
    s = re.sub(r"p_\{(\d+)\}", lambda m: str(pv.get(int(m.group(1)), 0)), s)
    s = re.sub(r"p_(\d+)", lambda m: str(pv.get(int(m.group(1)), 0)), s)
    s = re.sub(r"\bp(\d+)\b", lambda m: str(pv.get(int(m.group(1)), 0)), s)
    # any residual ascii letter is an unrecognised variable
    if re.search(r"[A-Za-z]", s):
        raise UnknownToken(f"unrecognised variable while substituting: {expr!r} → {s!r}")
    return s


def _eval_numeric(s: str, rationalize: bool) -> Fraction:
    """Evaluate a numeric-only expression exactly.

    rationalize=True  → decimals recovered as small-denominator fractions
                        (the intended coefficients).
    rationalize=False → decimals taken literally (what the float pipeline does),
                        used only to report the spurious "float RHS"."""
    def repl(m: re.Match) -> str:
        tok = m.group(0)
        if "." in tok:
            fr = _rationalize(tok) if rationalize else Fraction(tok)
            return f"F({fr.numerator},{fr.denominator})"
        return f"F({tok})"
    s2 = re.sub(r"\d+\.\d+|\d+", repl, s)
    try:
        return Fraction(eval(s2, {"__builtins__": {}}, {"F": Fraction}))
    except Exception as exc:                # pragma: no cover
        raise UnknownToken(f"could not evaluate expression {s!r}: {exc!r}")


def _exact_rhs(expr: str, pv: dict[int, int]) -> Fraction:
    return _eval_numeric(_substitute_vars(expr, pv), rationalize=True)


def _decimal_rhs(expr: str, pv: dict[int, int]) -> Fraction:
    return _eval_numeric(_substitute_vars(expr, pv), rationalize=False)


# ── conclusion / hypothesis parsing (semantics mirror pvec_eval) ──────────────

def _parse_conclusion(concl: str) -> tuple[str, str]:
    """Return ('ge'|'le', rhs_expr). Handles negated-LHS forms:
    '-(p6) >= E' ≡ 'p6 <= -(E)'."""
    s = concl.strip()
    for pat, op, wrap in (
        (r"p_?\{?6\}?\s*(?:>=|\\geq)\s*(.+)", "ge", False),
        (r"p_?\{?6\}?\s*(?:<=|\\leq)\s*(.+)", "le", False),
        (r"-\s*\(?\s*p_?\{?6\}?\s*\)?\s*(?:>=|\\geq)\s*(.+)", "le", True),
        (r"-\s*\(?\s*p_?\{?6\}?\s*\)?\s*(?:<=|\\leq)\s*(.+)", "ge", True),
    ):
        m = re.match(pat, s, re.DOTALL)
        if m:
            rhs = m.group(1).strip()
            return op, (f"-({rhs})" if wrap else rhs)
    raise UnknownToken(f"unrecognised conclusion form: {concl!r}")


def _hyp_holds_exact(hyp: str, pv: dict[int, int]) -> bool:
    """Evaluate a hypothesis with exact integer arithmetic (no float)."""
    flat = hyp.strip().strip("()").strip()
    flat_ns = flat.replace(" ", "")
    if flat in _STRUCTURAL:
        return True
    f2 = sum(pv.values())
    S7 = sum(v for k, v in pv.items() if k >= 7)
    m = re.fullmatch(r"f_2(>=|<=)_(\d+)", flat_ns)
    if m:
        n = int(m.group(2))
        return f2 >= n if m.group(1) == ">=" else f2 <= n
    m = re.fullmatch(r"(?:sum_pk_k>=7|sum_pk_after_p6)(>=|<=)(\d+)", flat_ns)
    if m:
        n = int(m.group(2))
        return S7 >= n if m.group(1) == ">=" else S7 <= n
    m = re.fullmatch(r"p_?(\d+)(>=|<=|=)(\d+)", flat_ns)
    if m:
        k, op, n = int(m.group(1)), m.group(2), int(m.group(3))
        pk = pv.get(k, 0)
        return {">=": pk >= n, "<=": pk <= n, "=": pk == n}[op]
    raise UnknownToken(f"unrecognised hypothesis atom: {hyp!r}")


def exact_counterexample_check(pv: dict[int, int], hyp_atoms: list[str],
                               conc_atom: str) -> tuple[bool, str, dict]:
    """Exact re-verification of hypotheses + STRICT conclusion violation.

    Returns (is_ce, detail, info) where info carries the exact and decimal RHS
    for reporting float artifacts."""
    for h in hyp_atoms:
        if not _hyp_holds_exact(h, pv):
            return False, f"hypothesis not satisfied (exact): {h}", {}
    op, rhs_expr = _parse_conclusion(conc_atom)
    exact_rhs = _exact_rhs(rhs_expr, pv)
    try:
        dec_rhs = _decimal_rhs(rhs_expr, pv)
    except Exception:
        dec_rhs = None
    p6 = Fraction(pv.get(6, 0))
    if op == "ge":
        violated = p6 < exact_rhs
        dec_violated = (dec_rhs is not None and p6 < dec_rhs)
    else:
        violated = p6 > exact_rhs
        dec_violated = (dec_rhs is not None and p6 > dec_rhs)
    info = {
        "relation": op,
        "p6": int(p6),
        "exact_rhs": str(exact_rhs),
        "float_rhs": (float(dec_rhs) if dec_rhs is not None else None),
        "decimal_violated": dec_violated,
    }
    rel = "≥" if op == "ge" else "≤"
    detail = f"exact: p6={int(p6)} {rel}? RHS={exact_rhs} → violated={violated}"
    return violated, detail, info


# ══════════════════════════════════════════════════════════════════════════════
# Deterministic natural-language statement renderer (exact fractions)
# ══════════════════════════════════════════════════════════════════════════════

def _strip_wrapping_parens(s: str) -> str:
    s = s.strip()
    while s.startswith("(") and s.endswith(")"):
        depth = 0
        wraps = True
        for i, ch in enumerate(s):
            if ch == "(":
                depth += 1
            elif ch == ")":
                depth -= 1
            if depth == 0 and i < len(s) - 1:
                wraps = False
                break
        if wraps:
            s = s[1:-1].strip()
        else:
            break
    return s


def _render_rhs(expr: str) -> str:
    """Render an arithmetic RHS with EXACT fractions, e.g.
    '(13/14)·p_3 - (507/224)·S - (13/7)'. No evaluation → text is arithmetically
    identical to the (rationalized) source."""
    s = expr.strip()
    s = re.sub(r"\bsum_pk_after_p6\b", "S", s)
    s = re.sub(r"sum_pk_k>=7", "S", s)
    s = re.sub(r"f_\{2\}|f_2\b", "f_2", s)
    s = re.sub(r"p_\{(\d+)\}", r"p_\1", s)
    s = re.sub(r"p_(\d+)", r"p_\1", s)
    s = re.sub(r"\bp(\d+)\b", r"p_\1", s)

    # decimals → parenthesised exact fractions (integers stay bare)
    def dec(m: re.Match) -> str:
        fr = _rationalize(m.group(0))
        return str(fr.numerator) if fr.denominator == 1 else f"({fr.numerator}/{fr.denominator})"
    s = _DEC_RE.sub(dec, s)

    leftover = re.sub(r"p_\d+|f_2|S|\d+/\d+", "", s)
    if re.search(r"[A-Za-z]", leftover):
        raise UnknownToken(f"unrecognised token in RHS: {expr!r} (residue {leftover!r})")

    s = _strip_wrapping_parens(s)
    s = s.replace("*", "·")
    s = re.sub(r"\s+", " ", s).strip()
    # tidy signs:  '+ -' → '- ',  '- -' → '+ '
    s = re.sub(r"\+\s*-\s*", "- ", s)
    s = re.sub(r"-\s*-\s*", "+ ", s)
    # '- (2/3)·' → '-(2/3)·'  (match the requested compact coefficient form)
    s = re.sub(r"(^|[+\-·(])\s*-\s*\((\d+/\d+)\)·", r"\1-(\2)·", s)
    s = re.sub(r"\s+", " ", s).strip()
    return s


def _render_conclusion(concl: str) -> str:
    op, rhs_expr = _parse_conclusion(concl)
    rel = "≥" if op == "ge" else "≤"
    return f"p_6 {rel} {_render_rhs(rhs_expr)}"


def _render_hypothesis(hyp: str) -> Optional[str]:
    flat = hyp.strip().strip("()").strip()
    flat_ns = flat.replace(" ", "")
    if flat in _STRUCTURAL:
        return None
    m = re.fullmatch(r"f_2(>=|<=)_(\d+)", flat_ns)
    if m:
        return f"f_2 {'≥' if m.group(1) == '>=' else '≤'} {m.group(2)}"
    m = re.fullmatch(r"(?:sum_pk_k>=7|sum_pk_after_p6)(>=|<=)(\d+)", flat_ns)
    if m:
        return f"S {'≥' if m.group(1) == '>=' else '≤'} {m.group(2)}"
    m = re.fullmatch(r"p_?(\d+)(>=|<=|=)(\d+)", flat_ns)
    if m:
        sym = {">=": "≥", "<=": "≤", "=": "="}[m.group(2)]
        return f"p_{m.group(1)} {sym} {m.group(3)}"
    raise UnknownToken(f"unrecognised hypothesis atom: {hyp!r}")


_BASE_SETUP = (
    "Let P be a simple convex 3-polytope. For each k ≥ 3 let p_k denote the "
    "number of k-gonal faces of P, let f_2 = Σ_{k≥3} p_k be the total number "
    "of (2-dimensional) faces, and let S = Σ_{k≥7} p_k."
)


def render_statement(formula: str) -> tuple[str, list[str], str, dict[str, str]]:
    """Render a self-contained English statement (exact fractions, unified
    ≤/≥) from the DSL formula. Returns (statement, hyp_atoms, conclusion,
    coefficients_exact). Never encodes the answer."""
    mm = _IF_THEN_RE.match(formula)
    if not mm:
        raise UnknownToken(f"formula not in 'if ..., then ...' shape: {formula!r}")
    cond = _strip_outer_parens(mm.group("cond"))
    concl = mm.group("concl").strip()

    hyp_atoms = []
    for h in _flatten_and_groups(cond):
        h = h.strip()
        if not h:
            continue
        hyp_atoms.append(h if h.startswith("(") and h.endswith(")") else f"({h})")

    clauses = [c for h in hyp_atoms if (c := _render_hypothesis(h)) is not None]
    conc_txt = _render_conclusion(concl)
    coeffs = _collect_coefficients(formula)

    if clauses:
        stmt = f"{_BASE_SETUP} If {', and '.join(clauses)}, then {conc_txt}."
    else:
        stmt = f"{_BASE_SETUP} Then {conc_txt}."
    return stmt, hyp_atoms, concl, coeffs


# ══════════════════════════════════════════════════════════════════════════════
# Helpers
# ══════════════════════════════════════════════════════════════════════════════

def _pvec_list_to_dict(vec: list) -> dict[int, int]:
    return {i + 3: int(v) for i, v in enumerate(vec) if int(v or 0) != 0}


def _cache_key_str(pv: dict[int, int]) -> str:
    return ",".join(f"{k}:{pv[k]}" for k in sorted(pv))


def _dehn_sommerville(pv: dict[int, int]) -> int:
    return sum((6 - k) * v for k, v in pv.items() if v > 0)


def _build_witness_graph(wg: dict):
    if not _NX_OK:
        return None
    edges = wg.get("edges")
    if not edges:
        return None
    G = nx.Graph()
    nvert = wg.get("num_vertices")
    if isinstance(nvert, int):
        G.add_nodes_from(range(nvert))
    G.add_edges_from(tuple(e) for e in edges)
    return G


# ══════════════════════════════════════════════════════════════════════════════
# Counterexample re-verification (exact arithmetic + witness graph)
# ══════════════════════════════════════════════════════════════════════════════

def verify_counterexample(pv: dict[int, int], hyp_atoms: list[str], conc_atom: str,
                          witness_graph: dict) -> tuple[bool, str, Optional[str], dict]:
    """Returns (ok, detail, drop_reason, info). ``info`` carries exact/float RHS
    so float artifacts can be reported. drop_reason is None when ok."""
    ok_valid, why = is_valid_simple_polytope(pv)
    if not ok_valid:
        return False, f"invalid polytope: {why}", "reverify_invalid_polytope", {}

    is_ce, detail, info = exact_counterexample_check(pv, hyp_atoms, conc_atom)
    if not is_ce:
        # distinguish a float artifact (decimal said CE, exact says not) from a
        # genuine non-CE (hypothesis failed / decimal also agrees).
        if info.get("decimal_violated"):
            return False, detail, "float_artifact", info
        return False, detail, "reverify_not_counterexample", info

    if not witness_graph or not witness_graph.get("edges"):
        return False, "no witness graph edges", "empty_witness_graph", info
    if not _NX_OK:
        return False, "networkx unavailable", "networkx_unavailable", info
    G = _build_witness_graph(witness_graph)
    if G is None:
        return False, "could not build witness graph", "empty_witness_graph", info
    try:
        ok_graph, d3 = _validate_witness_graph(G, pv)
    except Exception as exc:                # pragma: no cover
        return False, f"witness validation raised {exc!r}", "reverify_witness_error", info
    if not ok_graph:
        return False, f"witness graph rejected: {d3}", "reverify_witness_failed", info

    return True, f"{detail} | {d3}", None, info


# ══════════════════════════════════════════════════════════════════════════════
# Main export
# ══════════════════════════════════════════════════════════════════════════════

def export(conj_path: str, ce_dir: str, no_ce_dir: str, realizability_path: str,
           out_dir: str) -> dict:
    with open(conj_path) as fh:
        buckets = json.load(fh)

    report: dict = {
        "buckets_read": {b: len(buckets.get(b, [])) for b in ("unsolved", "failed", "proved")},
        "counterexamples": {},
        "proofs": {},
        "realizability": {},
        "drops": Counter(),
        "float_artifacts": [],
        "closed_loop_float_note": "",
        "coefficient_conversion_failures": [],
        "realizability_conflicts": [],
        "conflict_derivation_summary": {},
        "duplicates": [],
        "reverify_failure_rate": None,
        "reverify_stop_triggered": False,
    }

    labeled: list[dict] = []
    canon_seen: dict[str, str] = {}
    verified_ce_pvec_keys: set[str] = set()

    import glob
    ce_json_by_num: dict[int, str] = {}
    for jf in sorted(glob.glob(os.path.join(ce_dir, "*", "*.json"))):
        num = _entry_num(os.path.splitext(os.path.basename(jf))[0])
        if num is not None:
            ce_json_by_num.setdefault(num, jf)

    # ── FALSE label: refuted conjectures with a re-verified counterexample ────
    n_ce_attempted = 0
    n_ce_reverify_failed = 0
    for entry in buckets.get("failed", []):
        name = entry.get("name", "")
        num = _entry_num(name)
        status = entry.get("status")
        short_id = f"C{num}" if num is not None else name
        if status != "refuted":
            report["drops"]["failed_not_refuted"] += 1
            continue
        jf = ce_json_by_num.get(num)
        if jf is None:
            report["drops"]["missing_witness"] += 1
            continue
        with open(jf) as fh:
            payload = json.load(fh)
        ce = payload.get("counterexample") or {}
        vec = ce.get("p_vector")
        if not isinstance(vec, list):
            report["drops"]["missing_witness"] += 1
            continue
        pv = _pvec_list_to_dict(vec)
        wg = ce.get("witness_graph") or {}
        formula = entry.get("formula", "")

        try:
            statement, hyp_atoms, conc_atom, coeffs = render_statement(formula)
        except UnknownToken as exc:
            report["drops"]["unknown_token"] += 1
            print(f"[export] {name}: unknown token — {exc}", file=sys.stderr)
            continue
        except CoefficientError as exc:
            report["drops"]["coefficient_conversion_failed"] += 1
            report["coefficient_conversion_failures"].append({"id": short_id, "detail": str(exc)})
            print(f"[export] {name}: coefficient conversion failed — {exc}", file=sys.stderr)
            continue

        n_ce_attempted += 1
        ok, detail, reason, info = verify_counterexample(pv, hyp_atoms, conc_atom, wg)
        if not ok:
            n_ce_reverify_failed += 1
            report["drops"][reason] += 1
            if reason == "float_artifact":
                report["float_artifacts"].append({
                    "id": short_id,
                    "formula_raw": formula,
                    "p_vector": {str(k): pv[k] for k in sorted(pv)},
                    "relation": info.get("relation"),
                    "p6": info.get("p6"),
                    "float_rhs": info.get("float_rhs"),
                    "exact_rhs": info.get("exact_rhs"),
                })
                print(f"[export] {name}: FLOAT ARTIFACT — decimal RHS≈{info.get('float_rhs')}, "
                      f"exact RHS={info.get('exact_rhs')}, p6={info.get('p6')} → not a CE",
                      file=sys.stderr)
            else:
                print(f"[export] {name}: CE re-verification FAILED — {detail}", file=sys.stderr)
            continue

        verified_ce_pvec_keys.add(_cache_key_str(pv))

        canon = canonicalize_formula(formula)
        if canon in canon_seen:
            report["drops"]["duplicate"] += 1
            report["duplicates"].append({"id": short_id, "duplicate_of": canon_seen[canon]})
            continue
        canon_seen[canon] = short_id

        props_pv = {str(k): pv[k] for k in sorted(pv)}
        record = {
            "id": short_id,
            "statement": statement,
            "formula_raw": formula,
            "hypotheses": hyp_atoms,
            "conclusion": conc_atom,
            "label": "false",
            "family": "simple_polytope_pvector",
            "params": {
                "hypotheses": hyp_atoms,
                "conclusion": conc_atom,
                "coefficients_exact": coeffs,
            },
            "certificate": {
                "type": "counterexample",
                "p_vector": props_pv,
                "f2": ce.get("f2", sum(pv.values())),
                "num_vertices": ce.get("num_vertices"),
                "num_edges": ce.get("num_edges"),
                "witness_graph": wg,
                "violation_detail": detail,
            },
            "difficulty": None,
            "source": {
                "bucket": "failed",
                "status": status,
                "found_by": payload.get("found_by"),
                "found_at_round": payload.get("found_at_round"),
            },
        }
        labeled.append(record)

    report["counterexamples"] = {
        "reverify_attempted": n_ce_attempted,
        "reverify_failed": n_ce_reverify_failed,
        "float_artifacts": len(report["float_artifacts"]),
        "exported": sum(1 for r in labeled if r["label"] == "false"),
    }

    # ── TRUE label: proved conjectures with a qualifying Lean file ────────────
    n_true = 0
    for entry in buckets.get("proved", []):
        name = entry.get("name", "")
        num = _entry_num(name)
        status = entry.get("status")
        short_id = f"C{num}" if num is not None else name
        cx = f"c{num}"
        lean_path = os.path.join(no_ce_dir, cx, f"{cx}.lean")
        if not os.path.isfile(lean_path):
            report["drops"]["no_lean_file"] += 1
            continue
        text = open(lean_path).read()
        if _has_active_sorry(text):
            report["drops"]["lean_has_sorry"] += 1
            continue
        fh_hdr = _FAILED_HDR.search(text)
        if fh_hdr and int(fh_hdr.group(1)) > 0:
            report["drops"]["lean_failed_header"] += 1
            continue
        if re.search(rf"^\s*(?:private\s+|protected\s+)?(?:theorem|lemma)\s+C{num}(?:_Main)?\b",
                     text, re.MULTILINE) is None:
            report["drops"]["no_root_theorem"] += 1
            continue

        formula = entry.get("formula", "")
        try:
            statement, hyp_atoms, conc_atom, coeffs = render_statement(formula)
        except UnknownToken as exc:
            report["drops"]["unknown_token"] += 1
            print(f"[export] {name}: unknown token — {exc}", file=sys.stderr)
            continue
        except CoefficientError as exc:
            report["drops"]["coefficient_conversion_failed"] += 1
            report["coefficient_conversion_failures"].append({"id": short_id, "detail": str(exc)})
            continue

        canon = canonicalize_formula(formula)
        if canon in canon_seen:
            report["drops"]["duplicate"] += 1
            report["duplicates"].append({"id": short_id, "duplicate_of": canon_seen[canon]})
            continue
        canon_seen[canon] = short_id

        md_path = os.path.join(no_ce_dir, cx, f"{cx}.md")
        proof_md = open(md_path).read() if os.path.isfile(md_path) else None
        labeled.append({
            "id": short_id,
            "statement": statement,
            "formula_raw": formula,
            "hypotheses": hyp_atoms,
            "conclusion": conc_atom,
            "label": "true",
            "family": "simple_polytope_pvector",
            "params": {
                "hypotheses": hyp_atoms,
                "conclusion": conc_atom,
                "coefficients_exact": coeffs,
            },
            "certificate": {
                "type": "proof",
                "lean_path": os.path.relpath(lean_path, _REPO_ROOT),
                "lean_source": text,
                "proof_markdown": proof_md,
            },
            "difficulty": None,
            "source": {"bucket": "proved", "status": status,
                       "found_by": None, "found_at_round": None},
        })
        n_true += 1

    report["proofs"] = {"exported": n_true}

    # ── realizability.json (with euler_feasible flag) ─────────────────────────
    with open(realizability_path) as fh:
        rcache = json.load(fh)

    realiz: list[dict] = []
    rc_counter = 0
    excl_timeout = excl_cf = excl_conflict = 0
    conflict_sources: Counter = Counter()
    for key, meta in rcache.items():
        verdict = meta.get("verdict")
        if verdict not in ("realizable", "non_realizable"):
            if verdict == "timeout":
                excl_timeout += 1
            else:
                excl_cf += 1
            continue
        pv = {int(kv.split(":")[0]): int(kv.split(":")[1]) for kv in key.split(",")}
        if verdict == "non_realizable" and key in verified_ce_pvec_keys:
            excl_conflict += 1
            tu = meta.get("timeout_used", 0.0)
            derivation = "timeout_truncated" if (tu and tu > 0) else "plantri_exhaustive"
            conflict_sources[derivation] += 1
            report["realizability_conflicts"].append({
                "p_vector_key": key,
                "p_vector": {str(k): pv[k] for k in sorted(pv)},
                "cache_verdict": verdict,
                "cache_count": meta.get("count"),
                "cache_timeout_used": tu,
                "derivation": derivation,
            })
            continue
        rc_counter += 1
        realiz.append({
            "id": f"rc-{rc_counter:06d}",
            "p_vector": {str(k): pv[k] for k in sorted(pv)},
            "label": verdict,
            "euler_feasible": _dehn_sommerville(pv) == 12,
            "family": "pvector_realizability",
        })

    report["realizability"] = {
        "realizable": sum(1 for r in realiz if r["label"] == "realizable"),
        "non_realizable": sum(1 for r in realiz if r["label"] == "non_realizable"),
        "emitted": len(realiz),
        "euler_infeasible": sum(1 for r in realiz if not r["euler_feasible"]),
        "excluded_timeout": excl_timeout,
        "excluded_construction_failed": excl_cf,
        "excluded_conflict_with_witness": excl_conflict,
    }
    if excl_conflict:
        report["conflict_derivation_summary"] = dict(conflict_sources)

    # ── closed-loop float note (req 7) ────────────────────────────────────────
    artifact_ids = [a["id"] for a in report["float_artifacts"]]
    report["closed_loop_float_note"] = (
        "The pipeline's own counterexample checker (agent/orchestrator/tools/"
        "pvec_eval.py) evaluates the DSL's ROUNDED-DECIMAL coefficients literally "
        "(each decimal is wrapped in Fraction(<decimal>) — exact on the decimal, "
        "but NOT recovered to its intended small-denominator rational). On boundary "
        "cases this manufactures a spurious tiny RHS and accepts a non-counterexample. "
        "This export instead recovers each coefficient via "
        "Fraction(str).limit_denominator(1000) and requires a STRICT violation under "
        "exact arithmetic. The following conjectures are currently marked 'refuted' "
        "in conjectures.json but do NOT hold as counterexamples under exact "
        "arithmetic — they must be re-adjudicated in the original pipeline: "
        + (", ".join(artifact_ids) if artifact_ids else "(none found)")
    )

    # ── tallies + reverify stop rule (float artifacts are a KNOWN class and are
    #    excluded from the failure-rate that triggers the 5% stop) ─────────────
    report["labels"] = {
        "true": sum(1 for r in labeled if r["label"] == "true"),
        "false": sum(1 for r in labeled if r["label"] == "false"),
        "total": len(labeled),
    }
    n_float = len(report["float_artifacts"])
    n_hard_fail = n_ce_reverify_failed - n_float
    report["drops"] = dict(report["drops"])
    if n_ce_attempted:
        rate = n_hard_fail / n_ce_attempted
        report["reverify_failure_rate"] = round(rate, 4)
        report["reverify_failure_rate_excludes"] = "float_artifact (reported separately)"
        report["reverify_stop_triggered"] = rate > 0.05

    os.makedirs(out_dir, exist_ok=True)
    with open(os.path.join(out_dir, "conjectures_labeled.json"), "w") as fh:
        json.dump(labeled, fh, indent=2, ensure_ascii=False)
    with open(os.path.join(out_dir, "realizability.json"), "w") as fh:
        json.dump(realiz, fh, indent=2, ensure_ascii=False)
    with open(os.path.join(out_dir, "export_report.json"), "w") as fh:
        json.dump(report, fh, indent=2, ensure_ascii=False)

    return report


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--conjectures", default=os.path.join(_REPO_ROOT, "conjectures", "conjectures.json"))
    ap.add_argument("--ce-dir", default=os.path.join(_REPO_ROOT, "output", "conjecture_with_ce"))
    ap.add_argument("--no-ce-dir", default=os.path.join(_REPO_ROOT, "output", "conjecture_without_ce"))
    ap.add_argument("--realizability", default=os.path.join(_REPO_ROOT, "output", "realizability_cache.json"))
    ap.add_argument("--out", default=os.path.join(_REPO_ROOT, "export"))
    args = ap.parse_args(argv)

    report = export(args.conjectures, args.ce_dir, args.no_ce_dir,
                    args.realizability, args.out)
    print(json.dumps(report, indent=2, ensure_ascii=False))
    if report.get("reverify_stop_triggered"):
        print("\n*** STOP: hard re-verification failure rate exceeds 5% — do NOT "
              "relax checks; investigate the failing counterexamples above. ***",
              file=sys.stderr)
        return 2
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
