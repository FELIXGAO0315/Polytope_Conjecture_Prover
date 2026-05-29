GOAL_EXTRACTION_PROMPT = """\
You are a Lean 4 expert. Convert the following LaTeX theorem into a Lean 4 type signature.

Theorem type: {theorem_type}
Name: {name}
Hypotheses:
{hypotheses}
Conclusion: {conclusion}
{hint}

Rules:
1. Output exactly one line (or multiline continuation) beginning with `theorem` or `lemma` and ending with `:= by`. Nothing else.
2. Hypothesis count must equal the number of MATHEMATICAL hypotheses listed above. Do not drop or merge hypotheses. Note: "simple" and "3-connected" are NOT separate hypotheses — see rule 7.
3. The conclusion must exactly represent the LaTeX conclusion — including ALL parts of it (inequalities, existential statements, etc.). Do NOT split the conclusion into multiple hypotheses.
4. CRITICAL: Never encode what you need to PROVE as a hypothesis (h1, h2, …). Hypotheses are the GIVEN conditions (assumptions), the conclusion is what must be PROVED.
5. Implicit additions (typeclass constraints like `[Fintype α]`, universe annotations) are allowed but must be appended AFTER all explicit hypotheses and marked with a `-- implicit` comment at the end.

6. CRITICAL — SimplyCon3ConnectedMap usage:
   When the theorem involves ANY of: face counts (p_3, p_4, p_5, p_6, p_k),
   edge counts, vertex counts, Euler formula, handshake lemma, genus of a
   surface, p-vector, simple 3-connected map, map on a surface, or polygon
   faces in a graph — you MUST use `SimplyCon3ConnectedMap 0` (genus-0 sphere).
   All IRIS conjectures about "simple" maps are about simple 3-polytopes = genus 0 = sphere.
   CORRECT:  theorem Foo (maps : SimplyCon3ConnectedMap 0) (h : ...) : ... := by
   WRONG:    theorem Foo (g : ℤ) (maps : SimplyCon3ConnectedMap g) ...
   WRONG:    theorem Foo (m : ℕ) (pVector : Fin (m - 2) → ℕ) ...
   Access fields as: maps.p_i k (face counts), maps.e (edges), maps.v (vertices).
   SUM BOUNDS — Use `maps.m` (the structure field) as the upper bound for all
   finite sums over face sizes. NEVER add a separate `{{K : ℕ}}` or `{{m : ℕ}}`
   parameter — `maps.m` already serves this role.
   Use `Finset.Ico 3 (maps.m + 1)` (not `Finset.filter (· ≥ 3) (Finset.range K)`).
   CORRECT:  ∑ k in Finset.Ico 3 (maps.m + 1), maps.p_i k
   CORRECT:  ∑ k in Finset.Ico 7 (maps.m + 1), f k * maps.p_i k
   WRONG:    ∑ k in Finset.filter (· ≥ 3) (Finset.range K), maps.p_i k  -- invents K

7. CRITICAL — f-vector notation:
   In IRIS conjectures `f_2` denotes the TOTAL number of 2-dimensional faces
   (i.e. the total face count). Translate it as:
     f_2  →  ∑ k in Finset.Ico 3 (maps.m + 1), maps.p_i k
   NEVER use `maps.p_i 2` for f_2 — that would be digons (2-gonal faces) which
   do not exist in simple polytopes. NEVER use `maps.f2` or `maps.f_2` — those
   fields do not exist.
   CORRECT:  h_f2 : ∑ k in Finset.Ico 3 (maps.m + 1), maps.p_i k ≥ 22
   WRONG:    h_f2 : maps.p_i 2 ≥ 22          -- maps.p_i 2 = digons, always 0
   WRONG:    h_f2 : maps.f2 ≥ 22             -- field does not exist

8. CRITICAL — "simple" and "3-connected" hypotheses:
   `SimplyCon3ConnectedMap` represents simple, 3-connected maps by convention.
   If the LaTeX hypotheses include `\text{{simple}}` or `\text{{3-connected}}`,
   do NOT add a separate Lean hypothesis for them. Omit those hypotheses entirely.
   Do NOT use `IsSimple`, `simple maps`, `maps.simple`, `maps.is_simple`,
   `h_simple : IsSimple maps`, or any variant — none of these are defined.
   WRONG:  theorem Foo (maps : SimplyCon3ConnectedMap 0) (h_simple : IsSimple maps) ...
   WRONG:  theorem Foo (maps : SimplyCon3ConnectedMap 0) (h : maps.simple) ...
   CORRECT: theorem Foo (maps : SimplyCon3ConnectedMap 0) (h_f2 : ...) ...

9. CRITICAL — Fractional coefficients: if the inequality has fractional coefficients
   like 1/3, multiply BOTH SIDES by the denominator to stay in ℤ/ℕ arithmetic.
   Example: p_6 ≥ (9/2)∑p_k + 9  becomes: 2 * maps.p_i 6 ≥ 9 * ∑ ... + 18

10. Do NOT output any prose, explanation, markdown fences, or anything other than the single signature line.

Output only the Lean 4 signature, nothing else.
"""

GOAL_VALIDATION_PROMPT = """\
You are a Lean 4 expert. Compare the following Lean 4 signature against the original LaTeX theorem.

Theorem type: {theorem_type}
Name: {name}
Hypotheses:
{hypotheses}
Conclusion: {conclusion}

Lean 4 signature:
{signature}

Check each of the following:
1. Do hypothesis counts match? (Exclude "simple"/"3-connected" — those are encoded in the structure name and must NOT appear as hypotheses.)
2. Is the conclusion accurately represented?
3. Are any mathematical conditions weakened or strengthened?
4. Are all implicit additions clearly marked with `-- implicit`?

5. CRITICAL — SimplyCon3ConnectedMap: the signature MUST use `SimplyCon3ConnectedMap 0`
   (NOT `(g : ℤ) (maps : SimplyCon3ConnectedMap g)`). All IRIS conjectures are about
   simple 3-polytopes = genus 0. Flag as FAILED if the signature uses a free `g : ℤ`.
   Suggest the corrected signature using `(maps : SimplyCon3ConnectedMap 0)`.

6. CRITICAL — Spurious sum-bound parameter: flag as FAILED if the signature adds
   `{{K : ℕ}}` or `{{m : ℕ}}` to bound a sum. Use `maps.m` instead.
   All finite sums over face sizes must use `Finset.Ico 3 (maps.m + 1)`.

7. CRITICAL — f_2 translation: the hypothesis for `f_2 ≥ N` MUST be
   `∑ k in Finset.Ico 3 (maps.m + 1), maps.p_i k ≥ N`.
   Flag as FAILED if it uses `maps.p_i 2 ≥ N` (digons), `maps.f2`, or `maps.f_2`.
   Suggest the corrected form using the sum.

8. CRITICAL — Simplicity hypotheses: flag as FAILED if the signature contains ANY of
   `IsSimple`, `maps.simple`, `maps.is_simple`, `simple maps`, `h_simple`, `h_3connected`.
   These predicates are not defined in the proof library. The suggested signature must
   remove those hypotheses entirely.

Respond with ONLY valid JSON in this exact format:
{{"passed": true/false, "issues": ["issue1", "issue2"], "suggested_signature": "theorem ..."}}

If passed is true, suggested_signature can repeat the input signature.
"""
