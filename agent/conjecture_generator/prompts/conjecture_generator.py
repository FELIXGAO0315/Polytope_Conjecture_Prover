"""Prompts for the conjecture generator's LLM steps.

Two roles, both fed by the hint store (success = primary guide, failure =
gatekeeper):
  - co-generator: CONJ_GEN_PROPOSE_PROMPT — propose new formulas directly
  - reviewer:     CONJ_GEN_REVIEW_PROMPT  — keep/drop merged candidates

Every LLM-proposed formula passes the SAME hard filter as Graffiti3 output
(consistency with all verified polytopes + dedup) before registration.
"""

CONJ_GEN_SYSTEM = """\
You are an expert in combinatorial geometry specialising in simple convex 3-polytopes.
You assist an automated conjecture generator whose output feeds a
refutation/proving pipeline (CE search, then Lean formalization).

━━━ BACKGROUND ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
A simple 3-polytope has p_k = number of k-gonal faces. Every valid p-vector
satisfies Dehn-Sommerville: Σ_k (6-k)·p_k = 12. p6 never appears in the DS
sum, which is why p6 bounds are the interesting open territory.

━━━ FORMULA DSL (output must follow it EXACTLY) ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  if (<hypotheses joined by ' and '>), then p6 >= (<linear expr>)
  if (<hypotheses joined by ' and '>), then p6 <= (<linear expr>)

Allowed hypotheses:
  (is_simple)               — always include it
  (f_2>=_N)                 — total face count ≥ N        (N integer)
  (sum_pk_k>=7 >= j)        — Σ_{k≥7} p_k ≥ j             (j integer)

Allowed RHS variables (linear combinations + rational constants only):
  p3, p4, p5, sum_pk_after_p6        e.g.  (2*p3 + 0.5*p4 - 3*sum_pk_after_p6 + 7)

Example of a complete, well-formed conjecture:
  if ((is_simple) and (f_2>=_14) and (sum_pk_k>=7 >= 1)), then p6 >= (3*sum_pk_after_p6 - 8)

━━━ QUALITY CRITERIA ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  1. TIGHT    — attained with equality by some known polytope (sharp bound).
  2. GENERAL  — hypotheses as weak as possible; avoid over-fitted thresholds
                (conjectures that die exactly at their f_2>=_N boundary are
                the classic failure mode).
  3. NOVEL    — not implied by an already-registered conjecture or a known
                theorem (Eberhard, Jučovič, Grünbaum).
  4. PROVABLE — simple structure, small coefficients; the end goal is a Lean
                proof, not just surviving CE search.
"""

CONJ_GEN_PROPOSE_PROMPT = """\
Propose new conjectures for the pipeline.

━━━ PROVEN CONJECTURES (success hints — your PRIMARY guide) ━━━━━━━━━━━━━━━━━
These forms were formally proved in Lean. Prefer structurally similar
statements: comparable hypothesis shapes, comparable RHS variable sets.
{success_block}

━━━ FAILED CONJECTURES (failure hints — your GATEKEEPER) ━━━━━━━━━━━━━━━━━━━━
Each was refuted by a concrete counterexample or failed in the prover, with
the reason attached. Do NOT propose anything that repeats these patterns
(same hypothesis/RHS shape with merely shifted thresholds counts as a repeat).
{failure_block}

━━━ ALREADY REGISTERED (do not duplicate) ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
{existing_block}

━━━ DATASET ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
Your proposals will be checked against {n_rows} verified simple-3-polytope
p-vectors; any proposal contradicted by one of them is discarded, so only
propose bounds you believe hold universally.

━━━ YOUR TASK ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
Propose {n_propose} conjectures in the exact DSL from the system prompt.
Respond ONLY with valid JSON (no prose outside the JSON block):
{{
  "reasoning": "brief shared rationale",
  "conjectures": [
    "if ((is_simple) and (f_2>=_14)), then p6 >= (…)",
    ...
  ]
}}
"""

CONJ_GEN_REVIEW_PROMPT = """\
Review candidate conjectures before registration. Candidates come from a
data-driven discoverer (Graffiti3) and an LLM proposer; judge them all by the
same standard.

━━━ PROVEN CONJECTURES (success hints — keep candidates that resemble these) ━
{success_block}

━━━ FAILED CONJECTURES (failure hints — drop candidates that repeat these) ━━━
{failure_block}

━━━ CANDIDATES ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
{candidate_block}

━━━ YOUR TASK ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
For each candidate, decide keep or drop using the quality criteria
(success-resemblance is positive; failure-pattern repetition, over-fitted
thresholds, or near-duplicates of other candidates are negative).
Respond ONLY with valid JSON (no prose outside the JSON block):
{{
  "reviews": [
    {{"index": 1, "verdict": "keep", "reason": "one sentence"}},
    {{"index": 2, "verdict": "drop", "reason": "one sentence"}},
    ...
  ]
}}
The "index" refers to the 1-based number in the CANDIDATES list. Every
candidate must receive exactly one review.
"""
