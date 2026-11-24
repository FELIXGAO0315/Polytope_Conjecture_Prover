"""End-to-end tests for supplement_experiment/export_training_data.py.

Uses REAL repository artifacts:
  * C9   — a genuine, plantri-found counterexample (label="false")
  * C104 — a complete Lean proof, 0 sorry (label="true")
  * C48  — a FLOAT ARTIFACT: only "violates" under decimal rounding; exact
           rational arithmetic shows p6 = RHS, so it must be dropped.

and checks that tampering with a counterexample's p-vector so it no longer
violates the conclusion is correctly REJECTED by the re-verification gates.
"""
import glob
import json
import os
import sys

# this file lives at supplement_experiment/tests/test_export.py
_SUPPLEMENT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
_REPO_ROOT = os.path.dirname(_SUPPLEMENT)
if _REPO_ROOT not in sys.path:
    sys.path.insert(0, _REPO_ROOT)
sys.path.insert(0, _SUPPLEMENT)          # export_training_data.py now lives here

import export_training_data as ex   # noqa: E402


def _load_ce(num):
    jf = glob.glob(os.path.join(_REPO_ROOT, "output", "conjecture_with_ce",
                                f"C{num}", f"C{num}.json"))[0]
    return json.load(open(jf))


def _atoms(formula):
    _, hyps, conc, _ = ex.render_statement(formula)
    return hyps, conc


# ── statement renderer (exact fractions, unified ≤/≥) ─────────────────────────

def test_render_statement_c9():
    formula = "if ((is_simple) and (f_2>=_16)), then p6 >= (-2*sum_pk_after_p6 + 4)"
    stmt, hyps, conc, coeffs = ex.render_statement(formula)
    assert "simple convex 3-polytope" in stmt
    assert "f_2 ≥ 16" in stmt
    assert "p_6 ≥ -2·S + 4" in stmt
    assert "(is_simple)" in hyps and "(f_2>=_16)" in hyps
    assert coeffs == {}                       # integer coefficients only
    for banned in ("false", "true", "counterexample", "proof", "refuted"):
        assert banned not in stmt.lower()


C48_FORMULA = ("if ((is_simple)  and  (f_2>=_5)), then "
               "p6 >= (0.9285714286*p3 + -2.263392857*sum_pk_after_p6 + -1.857142857)")


def test_render_statement_exact_fractions_c48():
    stmt, hyps, conc, coeffs = ex.render_statement(C48_FORMULA)
    assert "(13/14)·p_3" in stmt          # 0.9285714286 → 13/14, parenthesised
    assert "≥" in stmt and "+ -" not in stmt   # unified sign / no '+ -'
    assert coeffs["0.9285714286"] == "13/14"
    assert coeffs["1.857142857"] == "13/7"


def test_render_unknown_token_raises():
    import pytest
    with pytest.raises(ex.UnknownToken):
        ex.render_statement("if ((is_simple) and (wobble>=_3)), then p6 >= (4)")


# ── real counterexample (C9) re-verifies under exact arithmetic ───────────────

def test_c9_counterexample_verifies():
    payload = _load_ce(9)
    ce = payload["counterexample"]
    pv = ex._pvec_list_to_dict(ce["p_vector"])
    hyps, conc = _atoms(
        "if ((is_simple) and (f_2>=_16)), then p6 >= (-2*sum_pk_after_p6 + 4)")
    ok, detail, reason, info = ex.verify_counterexample(pv, hyps, conc, ce["witness_graph"])
    assert ok, f"expected C9 CE to verify, got: {detail} ({reason})"


def test_c9_tampered_pvector_rejected():
    """p6 contributes 0 to Dehn-Sommerville, so bumping it keeps DS=12 valid but
    makes the conclusion hold → the tampered vector is no longer a CE."""
    payload = _load_ce(9)
    ce = payload["counterexample"]
    pv = ex._pvec_list_to_dict(ce["p_vector"])
    hyps, conc = _atoms(
        "if ((is_simple) and (f_2>=_16)), then p6 >= (-2*sum_pk_after_p6 + 4)")
    tampered = dict(pv)
    tampered[6] = tampered.get(6, 0) + 100
    ok, detail, reason, info = ex.verify_counterexample(tampered, hyps, conc, ce["witness_graph"])
    assert not ok, "tampered p-vector (conclusion now holds) must be rejected"


# ── C48 float artifact: exact arithmetic rejects it ───────────────────────────

def test_c48_is_float_artifact():
    """C48 with witness {3:2,4:3}: decimal RHS ≈ 2e-10 (spurious 'violation'),
    but exact RHS = 0 and p6 = 0 → NOT a counterexample."""
    hyps, conc = _atoms(C48_FORMULA)
    pv = {3: 2, 4: 3}                          # triangular prism, DS = 12
    ok, detail, reason, info = ex.verify_counterexample(pv, hyps, conc, {})
    assert not ok
    assert reason == "float_artifact", (reason, detail)
    assert info["exact_rhs"] == "0"
    assert info["p6"] == 0
    assert info["decimal_violated"] is True    # the pipeline's float path accepts it
    assert info["float_rhs"] is not None and info["float_rhs"] > 0


# ── real proof (C104) qualifies ───────────────────────────────────────────────

def test_c104_proof_qualifies():
    from agent.conjectures import _has_active_sorry
    import re
    lean = os.path.join(_REPO_ROOT, "output", "conjecture_without_ce", "c104", "c104.lean")
    text = open(lean).read()
    assert not _has_active_sorry(text)
    assert re.search(r"^\s*theorem\s+C104\b", text, re.MULTILINE)


# ── full export end-to-end ─────────────────────────────────────────────────────

def test_full_export(tmp_path):
    out = str(tmp_path / "export")
    report = ex.export(
        os.path.join(_REPO_ROOT, "conjectures", "conjectures.json"),
        os.path.join(_REPO_ROOT, "output", "conjecture_with_ce"),
        os.path.join(_REPO_ROOT, "output", "conjecture_without_ce"),
        os.path.join(_REPO_ROOT, "output", "realizability_cache.json"),
        out,
    )
    labeled = json.load(open(os.path.join(out, "conjectures_labeled.json")))
    realiz = json.load(open(os.path.join(out, "realizability.json")))
    ids = {r["id"] for r in labeled}

    c9 = next(r for r in labeled if r["id"] == "C9")
    assert c9["label"] == "false" and c9["certificate"]["type"] == "counterexample"

    c104 = next(r for r in labeled if r["id"] == "C104")
    assert c104["label"] == "true" and "theorem C104" in c104["certificate"]["lean_source"]

    # C48 must NOT be exported (dropped as a float artifact) and must be listed
    assert "C48" not in ids
    assert "C48" in {a["id"] for a in report["float_artifacts"]}
    assert "C48" in report["closed_loop_float_note"]

    assert report["labels"]["true"] >= 1 and report["labels"]["false"] >= 1
    # coefficients_exact present in params; realizability has euler_feasible
    assert all("coefficients_exact" in r["params"] for r in labeled)
    assert all(r["label"] in ("realizable", "non_realizable") for r in realiz)
    assert all(isinstance(r["euler_feasible"], bool) for r in realiz)
