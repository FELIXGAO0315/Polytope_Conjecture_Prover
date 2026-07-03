"""Prompts for the conjecture generator's LLM steps.

Two roles, both fed by signals derived from conjectures.json + registry
(proved = primary guide, refuted = gatekeeper, prover-stuck/survivor =
structure worth mimicking):
  - co-generator: CONJ_GEN_PROPOSE_PROMPT — propose new formulas directly
  - reviewer:     CONJ_GEN_REVIEW_PROMPT  — keep/drop merged candidates

Every LLM-proposed formula passes the SAME hard filter as Graffiti3 output
(consistency with all verified polytopes + dedup) before registration.
"""

CONJ_GEN_SYSTEM = """\
You output conjectures about simple convex 3-polytopes in a fixed DSL.

Form (one of):
  if (<hypotheses joined by ' and '>), then p6 >= (<linear expr>)
  if (<hypotheses joined by ' and '>), then p6 <= (<linear expr>)

Allowed hypothesis atoms:
  (is_simple) | (f_2>=_N) | (sum_pk_k>=7 >= j) |
  (p_3 = N) | (p_4 = N) | (p_5 = N) |
  (p_3 <= N) | (p_4 <= N) | (p_5 <= N) |
  (p_3 >= N) | (p_4 >= N) | (p_5 >= N)

Allowed RHS: linear combinations of {p3, p4, p5, sum_pk_after_p6} + rationals
with denominators in {1, 2, 3, 6}.

Always include (is_simple). Always respond with JSON only — no prose.
"""

# Background and quality criteria moved into the propose body where the
# longer context is cheaper to ignore — keeping the system prompt small lets
# Sonnet effort=low respond in seconds rather than triggering extended
# planning that times out at 150–300 s.

CONJ_GEN_PROPOSE_PROMPT = """\
Propose {n_propose} new p6-bound conjectures for simple convex 3-polytopes.

You DECIDE which structural shapes to target. Use the two blocks below to
spot where the registry is thin and where the pool actually has data.

━━━ VERIFIED POOL STRUCTURAL COMPOSITION ({n_rows} polytopes) ━━━━━━━━━━━━━━━━
How many polytopes live in each classical sub-class. A thin sub-class makes
LP-style bounds easy to fit but cheap to refute; a thick one means there's
real territory worth a conditional bound.
{pool_composition_block}

━━━ REGISTRY COVERAGE ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
How many existing conjectures touch each hypothesis shape. "UNTOUCHED" rows
are wide-open territory, "thin" rows are under-explored, "saturated" rows
are already crowded — avoid duplicating those.
{registry_coverage_block}

━━━ HIGH-TRL TEMPLATES ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
Already registered, sorted by IRIS-TRL desc. High TRL = tight + diverse +
spread; structurally mimic those, never duplicate.
{existing_block}

━━━ PROVED — Lean-verified theorems (strongest signal) ━━━━━━━━━━━━━━━━━━━━━━
Machine-checked truths. Extend them: sharper constants, neighbouring strata,
generalised or weakened hypotheses of the same bound family.
{success_block}

━━━ REFUTED (gatekeeper — same shape + shifted constants still counts) ━━━━━━
{failure_block}

━━━ CE-SURVIVED BUT UNPROVED (probably true; prover lacks tools) ━━━━━━━━━━━━
Beat every counterexample search, but the Lean prover could not close them
from the current axiom Inventory. Their hypothesis families are fertile —
propose variants with SIMPLER RHS shapes a counting/Euler argument reaches.
{stuck_block}

━━━ SURVIVORS (un-refuted after many CE attempts) ━━━━━━━━━━━━━━━━━━━━━━━━━━━
{survivor_block}

━━━ FOCUS CELLS (uncovered hypothesis territory this round) ━━━━━━━━━━━━━━━━━
{focus_block}

━━━ VERIFIED P-VECTORS (mentally test every proposal) ━━━━━━━━━━━━━━━━━━━━━━━
{verified_block}

━━━ TASK ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
Split your proposals across three modes:
  1. EXPLORE — target the FOCUS CELLS and other under-covered regions in the
     coverage table; combine hypothesis atoms into shapes the table doesn't
     list.
  2. SHARPEN — take a PROVED bound and propose a strictly stronger sibling
     (tighter constant, or one hypothesis atom removed).
  3. REPAIR — take a recent REFUTED bound and move it just past its
     counterexample (shift the constant, or add the hypothesis atom the CE
     fails). A repaired bound must clear every CE listed for that shape.
Each proposal is re-checked against {n_rows} verified p-vectors; RHS
coefficients with denominators > 6 are auto-rejected. Output JSON only:
{{
  "conjectures": [
    "if ((is_simple) and ...), then p6 >= (...)",
    ...
  ]
}}
"""

CONJ_GEN_REVIEW_PROMPT = """\
Decide keep/drop on each candidate. Output JSON only.

Drop a candidate iff any of:
  (a) any verified p-vector below satisfies the hypothesis AND violates the
      conclusion (cite it),
  (b) RHS has a fractional coefficient with denominator > 6 (LP overfit),
  (c) it matches a refuted-shape entry WITHOUT clearing that entry's cited
      CE (a genuine repair — constants moved past the counterexample — is
      legitimate and should be kept),
  (d) near-duplicate of another candidate in this batch.
A "keep" should be sharp on at least one verified p-vector.

Refuted shapes (gatekeeper):
{failure_block}

Verified p-vectors (counterexample check):
{verified_block}

Candidates:
{candidate_block}

Output:
{{
  "reviews": [
    {{"index": 1, "verdict": "keep", "reason": "one sentence"}},
    {{"index": 2, "verdict": "drop", "reason": "one sentence"}}
  ]
}}
Every candidate gets exactly one review keyed by its 1-based index.
"""
