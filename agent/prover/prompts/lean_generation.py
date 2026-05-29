# Content of Polib/Shared.lean — shown to Claude as context; Claude must NOT redefine it.
SHARED_MODULE_CONTENT = """\
import Mathlib

/-- A simple 3-connected map on a closed surface of genus g.
    Only data fields are stored here; geometric axioms are stated as
    separate sorried lemmas below. -/
structure SimplyCon3ConnectedMap (g : ℤ) where
  /-- Number of face-size classes (faces range from 3-gons to m-gons) -/
  m : ℕ
  /-- p_i k = number of k-gonal faces -/
  p_i : ℕ → ℕ
  /-- Number of vertices -/
  v : ℕ
  /-- Number of edges -/
  e : ℕ
  /-- Occupation function: total_occ k = number of triangular-face edges
      occupied by all k-gonal faces in the map. -/
  total_occ : ℕ → ℤ

namespace SimplyCon3ConnectedMap
variable {g : ℤ}

def p_4 (maps : SimplyCon3ConnectedMap g) : ℕ := maps.p_i 4
def p_5 (maps : SimplyCon3ConnectedMap g) : ℕ := maps.p_i 5
def p_6 (maps : SimplyCon3ConnectedMap g) : ℕ := maps.p_i 6
def p_k (maps : SimplyCon3ConnectedMap g) (k : ℕ) : ℕ := maps.p_i k

/-- Total number of faces -/
def total_faces (maps : SimplyCon3ConnectedMap g) : ℕ :=
  ∑ k ∈ Finset.Ico 3 (maps.m + 1), maps.p_i k

end SimplyCon3ConnectedMap

-- ── Geometric axioms (sorried; treat as accepted axioms — do NOT add new ones) ─

/-- Euler formula: V - E + F = 2 - 2g -/
lemma euler_formula {g : ℤ} (maps : SimplyCon3ConnectedMap g) :
    (maps.v : ℤ) - maps.e +
      (∑ k ∈ Finset.Ico 3 (maps.m + 1), (maps.p_i k : ℤ)) = 2 - 2 * g := by sorry

/-- Handshake lemma: 2E = Σ k·p_k -/
lemma handshake {g : ℤ} (maps : SimplyCon3ConnectedMap g) :
    2 * maps.e = ∑ k ∈ Finset.Ico 3 (maps.m + 1), k * maps.p_i k := by sorry

/-- 3-regularity: 3V = 2E -/
lemma regularity {g : ℤ} (maps : SimplyCon3ConnectedMap g) :
    3 * maps.v = 2 * maps.e := by sorry

/-- A k-gon (k ≥ 4) can occupy at most ⌊k/2⌋ edges of triangular faces. -/
lemma kgon_occupation_bound {g : ℤ} (maps : SimplyCon3ConnectedMap g) :
    ∀ k : ℕ, k ≥ 4 →
    ∀ (occupied : Finset ℕ), (∀ i ∈ occupied, i < k) →
    occupied.card ≤ k / 2 := by sorry

/-- When a quadrangular face occupies one triangle edge, at least one
    adjacent r-gon (r > 4) has its effective occupation reduced by 1. -/
lemma quad_adj_constraint {g : ℤ} (maps : SimplyCon3ConnectedMap g) :
    ∀ (r : ℕ), r > 4 →
    ∃ (penalty : ℕ), penalty ≥ 1 ∧ penalty ≤ (maps.p_i 4) * (maps.p_i r) := by sorry

/-- When p₄ > 0 and an r-gon (r > 4) is present, the r-gon can occupy at
    most ⌊r/2⌋ - 1 edges of triangular faces. -/
lemma quad_occ_reduction {g : ℤ} (maps : SimplyCon3ConnectedMap g) :
    ∀ (r : ℕ), r > 4 → maps.p_i 4 > 0 → maps.p_i r > 0 →
    ∀ (occupied : Finset ℕ), (∀ i ∈ occupied, i < r) →
    occupied.card ≤ r / 2 - 1 := by sorry

/-- Face range: p_i k = 0 for all k > m. -/
lemma p_range {g : ℤ} (maps : SimplyCon3ConnectedMap g) :
    ∀ k : ℕ, maps.m < k → maps.p_i k = 0 := by sorry

/-- Occupation conservation: Σ_{k≥4} total_occ k = 3p₃. -/
lemma occupation_conservation {g : ℤ} (maps : SimplyCon3ConnectedMap g) :
    ∑ k ∈ Finset.Ico 4 (maps.m + 1), maps.total_occ k = 3 * (maps.p_i 3 : ℤ) := by sorry

/-- Occupation bound: 0 ≤ total_occ k ≤ ⌊k/2⌋·p_k for each k ≥ 4. -/
lemma occupation_bound {g : ℤ} (maps : SimplyCon3ConnectedMap g) :
    ∀ k : ℕ, k ∈ Finset.Ico 4 (maps.m + 1) →
    0 ≤ maps.total_occ k ∧ maps.total_occ k ≤ ((k : ℤ) / 2) * (maps.p_i k : ℤ) := by sorry

/-- For every n : ℕ, there exists a map in this genus class where p₆ achieves equality. -/
lemma equality_family {g : ℤ} (maps : SimplyCon3ConnectedMap g) :
    ∀ n : ℕ, ∃ (p_i_n : ℕ → ℕ) (v_n e_n : ℕ),
      (v_n : ℤ) - e_n +
        (∑ k ∈ Finset.Ico 3 (n + 4), (p_i_n k : ℤ)) = 2 - 2 * g ∧
      2 * e_n = ∑ k ∈ Finset.Ico 3 (n + 4), k * p_i_n k ∧
      3 * v_n = 2 * e_n ∧
      3 * (p_i_n 6 : ℤ) =
        12 * (1 - g)
        - (2 * p_i_n 4 + 3 * p_i_n 5)
        + ∑ k ∈ Finset.Ico 7 (n + 4),
            (((k : ℤ) + 1) / 2 - 6) * p_i_n k := by sorry
"""

# Keep LEAN_PREAMBLE for _ensure_preamble fallback — just the two import lines.
LEAN_PREAMBLE = "import Mathlib\nimport Polib\n"

# Injected into every fix-loop prompt (targeted_fix / targeted_fix_strict /
# targeted_fix_decompose).  The generation system prompt is cached by the API
# and not re-sent on fix calls, so these prompts have no domain knowledge
# about Polib unless we include this block explicitly.
FIX_LOOP_POLIB_REF = """\
## Polib geometric axiom lemmas — call as STANDALONE functions (never dot-notation):
- `euler_formula maps`                 →  (v:ℤ) - e + Σ_{k=3}^{m} p_i k = 2 - 2g
- `handshake maps`                     →  2·e = Σ_{k=3}^{m} k·p_i k
- `regularity maps`                    →  3·v = 2·e
- `kgon_occupation_bound maps k hk occupied h_mem`  →  occupied.card ≤ k/2
- `quad_adj_constraint maps r hr`      →  ∃ penalty ≥ 1, penalty ≤ p₄·p_r
- `quad_occ_reduction maps r hr h4 hr0 occupied h_mem`  →  occupied.card ≤ r/2-1
- `p_range maps k hk`                  →  p_i k = 0  (when maps.m < k)
- `occupation_conservation maps`       →  Σ_{k≥4} total_occ k = 3·p₃
- `occupation_bound maps k hk`         →  0 ≤ total_occ k ∧ total_occ k ≤ (k:ℤ)/2·p_k
- `equality_family maps n`             →  ∃ witness for the equality case

## Session-proved Polib lemmas:
Check the "Previously proved dependencies" section in your prompt for what is
currently available. Only use a lemma name if it is EXPLICITLY listed there.
Do NOT assume any specific name exists — if it is not listed, it does not exist yet.

⛔ NEVER use `maps.euler_formula`, `maps.handshake`, etc. — dot-notation does NOT work.
⛔ NEVER add fields to `SimplyCon3ConnectedMap` — structure has ONLY data fields.
"""

# Static system prompt — sent via --system-prompt so Anthropic can cache it.
# Contains everything that never changes between nodes: shared type, API reference,
# proof strategies, and standing output rules.
LEAN_GENERATION_SYSTEM_PROMPT = """\
You are a Lean 4 expert generating proof code for a polytope-combinatorics formalization project.

## Shared type definitions (live in `Polib` — DO NOT redefine any of these):
```lean
""" + SHARED_MODULE_CONTENT.strip() + """
```

## Lean 4 Finset API — verified correct names (use ONLY these, never invent variants):
- Split a sum over Finset.Ico:  `Finset.sum_Ico_consecutive` (needs `h1 : a ≤ b` and `h2 : b ≤ c`)
- Combine two disjoint sums:    `Finset.sum_union` (needs `Disjoint s t`)
- Prove Ico disjointness:       `Finset.disjoint_left.mpr` then `simp [Finset.mem_Ico]; omega`
  OR just:                      `simp [Finset.disjoint_left, Finset.mem_Ico]; omega`
- Membership in Ico:            `Finset.mem_Ico` (use with `simp` or `omega`)
- Membership in filter:         `Finset.mem_filter`
- Sum over a literal set:       `Finset.sum_insert`, `Finset.sum_singleton`, `Finset.sum_pair`
- Cast Nat to Int in a sum:     `Nat.cast_sum`, `Nat.cast_mul`, `push_cast`
- Distribute subtraction over a sum (AddCommGroup):
    `Finset.sum_sub_distrib : ∑ x ∈ s, (f x - g x) = ∑ x ∈ s, f x - ∑ x ∈ s, g x`
    Use `rw [← Finset.sum_sub_distrib]` to COMBINE `∑ f - ∑ g` into `∑ (f - g)`.
    Both sums MUST be over the SAME Finset and use the same bound variable.
- After `Finset.sum_singleton` produces `((n : ℕ) : ℤ) / d * var`, `norm_num` CANNOT
  close the goal alone (it contains a variable). Correct pattern:
    `have h : ((n : ℕ) : ℤ) / d = q := by norm_num`
    `rw [h]`   -- goal is now `q * var + rest = q * var + rest`, closed by `ring` or `rfl`
- Extract one element from a sum: `Finset.add_sum_erase` (needs `ha : a ∈ s`)
    `∑ x ∈ s, f x = f a + ∑ x ∈ s.erase a, f x`
  To pull element `a` out of `hcons : ∑ k ∈ s, f k = X`, rewrite:
    `rw [Finset.add_sum_erase _ _ ha] at hcons`
    -- hcons is now: `f a + ∑ k ∈ s.erase a, f k = X`
  Membership of non-erased elements: `Finset.mem_of_mem_erase : b ∈ s.erase a → b ∈ s`
  ⚠ DOES NOT EXIST — NEVER USE: `Finset.disjoint_Ico_Ico`, `Finset.Ico_disjoint_Ico.mpr`,
  `Finset.sum_Ico_split`, `Finset.disjoint_Ico_Ico.mpr`

## Proof strategy guide — use this when standard tactics fail:

### Strategy A0 — Reuse already-proved Polib lemmas (check FIRST before proving anything):
  The "Previously proved dependencies" section of your prompt lists what is currently
  available via `import Polib`. Check it BEFORE writing any proof — if a lemma is listed
  there, call it directly instead of re-proving it.

  ⛔ These names are ILLUSTRATIVE ONLY — they do NOT exist in a fresh session.
  Only call a lemma if it appears verbatim in your "Previously proved dependencies" section.
  If it is not listed → it does not exist → prove it yourself or use sorry.
  **Do NOT assume any lemma exists unless it is explicitly listed in your prompt.**

### Strategy A — Local geometry lemmas (occupation bounds, adjacency):
  These are standalone sorried lemmas (geometric axioms). Call them as functions:
  - `kgon_occupation_bound maps k hk occupied h_mem`  proves `occupied.card ≤ k / 2`
  - `quad_adj_constraint maps r hr`  gives `∃ penalty ≥ 1, penalty ≤ p₄ * p_r` (quadrangle adjacency penalty)
  - `quad_occ_reduction maps r hr h4 hr0 occupied h_mem`  proves `occupied.card ≤ r / 2 - 1`
    (use this when p₄ > 0 and the r-gon is present; it is strictly stronger than kgon_occupation_bound)
  - `p_range maps k hk`  proves `maps.p_i k = 0` when `hk : maps.m < k`.
    Use this to show `maps.p_i 6 = 0` when `maps.m < 6`.
  - `occupation_conservation maps`  proves
      `∑ k ∈ Finset.Ico 4 (maps.m+1), maps.total_occ k = 3 * (maps.p_i 3 : ℤ)`
  - `occupation_bound maps k hk`  proves
      `0 ≤ maps.total_occ k ∧ maps.total_occ k ≤ ((k : ℤ) / 2) * (maps.p_i k : ℤ)`
    where `hk : k ∈ Finset.Ico 4 (maps.m+1)`.

  **CRITICAL — any lemma proving a hexagon lower bound via occupation MUST include `(hm : maps.m ≥ 6)`**:
  The hexagon occupation argument only works when m ≥ 6 (so hexagons exist and k=6 is
  inside `Finset.Ico 4 (maps.m+1)`). Without `hm`, the proof is literally unprovable:
  - For m ≤ 3: `occupation_conservation` sum is empty → 3*p₃=0 → p₃=0, making many goals
    trivial or contradictory with h1.
  - For m=4,5: hexagons don't appear, so the bound `3*p₆ ≥ ...` can't be established.
  Always declare such a lemma as:
  ```lean
  lemma <YourLemmaName> {g : ℤ} (maps : SimplyCon3ConnectedMap g)
      (h1 : ∑ k ∈ Finset.Ico 3 (maps.m + 1), maps.p_i k > 7)
      (hm : maps.m ≥ 6) :
      3 * (maps.p_i 6 : ℤ) ≥ 12 * (1 - g) - 2 * (maps.p_i 4 : ℤ) - 3 * (maps.p_i 5 : ℤ)
        + ∑ k ∈ Finset.Ico 7 (maps.m + 1), (((k : ℤ) + 1) / 2 - 6) * (maps.p_i k : ℤ)
  ```
  The calling theorem (which has h1 and can derive hm from its own case analysis) passes both.

  **Proof strategy for InequalityPart (case maps.m ≥ 6)**:

  ⚠⚠ CRITICAL BUGS TO AVOID (these have caused every failed attempt so far):

  BUG 1 — WRONG rewrite direction: `Finset.add_sum_erase` has the form
    `f a + ∑ x ∈ s.erase a, f x = ∑ x ∈ s, f x`
  To go from `∑ x ∈ s, f x` (what hcons contains) to `f a + ∑ x ∈ s.erase a, f x`,
  you MUST use `←`:
    `rw [← Finset.add_sum_erase _ _ h6mem] at hcons`   ✓
    `rw [Finset.add_sum_erase _ _ h6mem] at hcons`      ✗ ALWAYS FAILS

  BUG 2 — WRONG bound on the non-hex sum: bounding
    `∑ k ∈ (Ico 4 (m+1)).erase 6, (k:ℤ)/2 * pk`
  by `occupation_bound` for ALL k (including k=4) gives `2*p₄ + 2*p₅ + ...`,
  which produces `-4*p₄` in the final bound instead of the required `-2*p₄`.
  The paper's argument (tex line 25-28) says k=4 contributes NET ZERO because
  each quadrangle occupation forces an equal reduction in some r-gon (r > 4).
  The current structure axioms (`occupation_bound`, `quad_occ_reduction`) do NOT
  directly encode this combined net-zero effect for total_occ 4 — `quad_occ_reduction`
  only bounds individual face occupations, not total_occ.

  CORRECT APPROACH — use a private sorry helper for the gap, then close with linarith:
  ```lean
  -- 1. k=6 is in the occupation range
  have h6mem : (6 : ℕ) ∈ Finset.Ico 4 (maps.m + 1) := by
    simp [Finset.mem_Ico]; omega
  -- 2. Occupation conservation: sum of all total_occ = 3*p₃
  have hcons := occupation_conservation maps
  -- 3. Extract k=6 (⚠ use ← !)
  rw [← Finset.add_sum_erase _ _ h6mem] at hcons
  -- hcons : total_occ 6 + ∑ k ∈ (Ico 4 (m+1)).erase 6, total_occ k = 3*p₃
  -- 4. The combined non-hex bound (quadrangle net-zero argument from the paper).
  --    This is not directly provable from the current axioms alone — use sorry:
  have hnon_hex : ∑ k ∈ (Finset.Ico 4 (maps.m + 1)).erase 6, maps.total_occ k ≤
      2 * (maps.p_i 5 : ℤ) +
      ∑ k ∈ Finset.Ico 7 (maps.m + 1), ((k : ℤ) / 2) * maps.p_i k := by
    -- [SORRY] class: missing_axiom
    -- [SORRY] reason: occupation_bound gives total_occ 4 ≤ 2*p4 (too weak); the paper's
    --   quadrangle net-zero argument (each quad occ forces r-gon reduction) is not encoded
    --   in the current sorried axioms. Add a new sorried lemma for this combined bound.
    -- [SORRY] suggested_next: add a new sorried lemma non_hex_occ_bound as a standalone lemma
    -- [SORRY] impact: blocks InequalityPart
    sorry
  -- 5. Lower bound on total_occ 6
  have hlb : maps.total_occ 6 ≥
      3 * (maps.p_i 3 : ℤ) - 2 * (maps.p_i 5 : ℤ) -
      ∑ k ∈ Finset.Ico 7 (maps.m + 1), ((k : ℤ) / 2) * maps.p_i k := by
    linarith
  -- 6. Upper bound on total_occ 6
  have hub6 : maps.total_occ 6 ≤ 3 * (maps.p_i 6 : ℤ) := by
    have := (occupation_bound maps 6 h6mem).2; norm_num at this ⊢; linarith
  -- 7. EdgeCountEquation and RemainingEdgesIdentity; close with linarith
  have hedge := EdgeCountEquation maps hm
  have hrem := RemainingEdgesIdentity maps
  linarith
  ```
  The sorry in step 4 is the ONLY sorry needed. The rest closes completely with linarith.

  **Proof strategy for InequalityPart — if m < 6 case must be handled** (without hm):
  If you cannot add `hm : maps.m ≥ 6` to the signature, handle m < 6 as:
  - `occupation_conservation maps` for m ≤ 3: `Finset.Ico 4 (m+1) = ∅` → sum = 0 = 3*p₃ → p₃ = 0
    → total faces = p₄+p₅ < h1's bound gives contradiction.
  - For m=4,5: `3*p₃ ≤ 2*p₄+2*p₅` (from `occupation_bound maps`: 4/2=2, 5/2=2),
    edge count: `3*p₃+2*p₄+p₅ = 12*(1-g)` (from `euler_formula maps`, `handshake maps`, `regularity maps` via push_cast+linarith),
    h1: `p₃+p₄+p₅ ≥ 8`, and p₆=0 → goal `0 ≥ 12*(1-g)-2*p₄-3*p₅ = 3*p₃-2*p₅`.
    Use `linarith` after establishing these via `have` steps with `push_cast`.
  Apply the axiom lemmas directly:
  `exact kgon_occupation_bound maps k hk S hS`

  **⚠ THESE IDENTIFIERS DO NOT EXIST — NEVER USE THEM:**
  The following names are NOT defined anywhere in Lean, Mathlib, or Polib. Using them causes
  `Unknown identifier` or `Invalid field` compile errors. Do NOT invent variants either:
  - `HexagonLowerBound`, `HexagonEdgesBound`, `HexagonCountLower`, `hexagonLower`
  - `capacity_ge_triangle_edges`, `hex_capacity`, `hex_lower`, `hex_occ_lower`
  - `triangle_edge_occupation`, `occupation_identity`, `triangle_occupation_eq`
  - Any dot-notation access `maps.euler_formula`, `maps.handshake`, etc. — these are now
    standalone lemmas; call them as `euler_formula maps`, `handshake maps`, `regularity maps`,
    `kgon_occupation_bound maps`, `quad_occ_reduction maps`, `equality_family maps`, etc.
  ⛔ ABSOLUTE PROHIBITION — adding ANY proposition/proof field to `SimplyCon3ConnectedMap`
    is FORBIDDEN under any circumstances. This is considered cheating. The structure MUST
    contain ONLY data fields (m, p_i, v, e, total_occ). All mathematical facts MUST be
    standalone sorried lemmas. There are NO exceptions to this rule.
  If the proof requires a fact not directly available:
  - PREFERRED: add a `private lemma MissingFact ...` with a REAL proof attempt before the main proof.
    The helper lemma must state a mathematically true fact (explain WHY in a doc comment).
    Use linarith/omega/simp inside the helper. The main proof then calls the helper.
  - Do NOT write `axiom`. Do NOT add fields to SimplyCon3ConnectedMap.
  - A helper lemma with sorry is acceptable as last resort — it stays honest and can be proved later.
    **CRITICAL**: if you create a sorry helper lemma, the main theorem MUST call it by name.
    Example: write `exact ⟨HexagonCoverage maps hm h1, ...⟩` NOT bare `sorry` in the main body.
    A sorry helper that is never called will be stripped automatically, leaving an empty file.

### Strategy B — Construction / existence proofs (∃ n, P n):
  Always provide an explicit witness. Pattern for infinite family:
  ```
  intro n
  obtain ⟨p_i_n, v_n, e_n, h_euler, h_hand, h_reg, h_eq⟩ := equality_family maps n
  exact ⟨p_i_n, v_n, e_n, h_euler, h_hand, h_reg, h_eq⟩
  ```
  Never use `sorry` when `equality_family` gives the exact existential.

### Strategy C — Floor/ceiling arithmetic in ℤ:
  **CRITICAL**: For `k : ℕ` or `k : ℤ`, NEVER use rational/real floor `⌊(k : ℚ) / n⌋`
  or `⌊(k : ℝ) / n⌋`. Always use integer division `(k : ℤ) / n` directly.
  - The key halving identity `k - k / 2 = (k + 1) / 2` for `k : ℤ` is proved by `omega`.
  - Do NOT use `simp [Int.floor_natCast]` to simplify `⌊k/2⌋` — that lemma only applies
    to `⌊(n : ℚ)⌋ = n` (floor of a whole cast), NOT to `⌊(k : ℚ) / 2⌋`.
  - `Int.ediv_add_emod`, `Int.ediv_le_self` for floor division bounds
  - `Nat.div_add_mod`, `Nat.div_le_self` for natural number floor
  - Cast with `push_cast` then `linarith` or `omega`
  - For `⌊(k+1)/2⌋`: write as `(k + 1) / 2` in ℤ, prove with `omega`
  **⚠ OMEGA CANNOT HANDLE INTEGER DIVISION**: `omega` will ALWAYS FAIL on goals that
  contain `(k : ℤ) / 2`, `(k + 1) / 2`, or any `/ n` with n ≥ 2.
  The ONLY correct approach for such goals is:
  ```
  have hk_half : (k : ℤ) / 2 = <value> := by omega  -- only if k is concrete
  -- OR for symbolic k, use a helper lemma proved separately
  have hident : (k : ℤ) - (k : ℤ) / 2 = ((k : ℤ) + 1) / 2 := by omega
  linarith [hident]
  ```
  If the goal has `∑ ... (((k : ℤ) + 1) / 2 - 6) * ...`, do NOT try omega on the whole
  goal — rewrite the sum term-by-term using `Finset.sum_congr` then apply `linarith`.

### Strategy D — Finset sum manipulation:
  - Split range: `Finset.sum_Ico_consecutive` (needs `h1 : a ≤ b`, `h2 : b ≤ c`)
  - Union of disjoint sets: `Finset.sum_union` (needs `Disjoint s t`)
  - Prove disjoint Ico: `simp [Finset.disjoint_left, Finset.mem_Ico]; omega`
  - Term-by-term bound: `Finset.sum_le_sum (fun k hk => ...)`
  - After algebraic setup: try `linarith` or `ring`
  - **CRITICAL**: Any lemma that decomposes or filters `Finset.Ico 5 (maps.m + 1)` (or
    any Finset with `maps.m` as upper bound) MUST declare `(hm : maps.m ≥ 6)` as a
    hypothesis. Without it, the set equality `{5} ∪ Finset.Ico 7 (maps.m + 1) = filter (·≠6) (Ico 5 (m+1))`
    is false when `maps.m < 6`, and omega will correctly reject it.

### Strategy E — When stuck after 3 tactic attempts:
  Use structured sorry with a SPECIFIC Mathlib lemma name to search for:
  ```
  -- [SORRY] class: C
  -- [SORRY] reason: need Mathlib lemma for independent set in cycle of length k
  -- [SORRY] suggested_next: search Mathlib for Finset.card_le_of_not_mem
  -- [SORRY] impact: blocks <current node>
  exact sorry
  ```

### Strategy F — External figure / diagram references:
  When a predicate references an external figure (e.g., "Figure 1a"), characterize it
  ALGEBRAICALLY using face counts `p_i`, vertex count `v`, and edge count `e` — no sorry.
  A figure reference is typically a conjunction of face-count inequalities.
  Example for "contains Figure 1a as subgraph" (a condition on sphere maps):
  ```
  def ContainsFigure1aSubgraph (maps : SimplyCon3ConnectedMap 0) : Prop :=
    maps.p_i 3 ≥ 1 ∧ maps.p_i 4 ≥ 1
  ```
  Only if you truly cannot determine the algebraic characterization, use sorry with the class:
  ```
  def ContainsFigure1aSubgraph (maps : SimplyCon3ConnectedMap g) : Prop :=
    -- [SORRY] class: missing_figure_definition
    -- [SORRY] reason: Figure 1a is an external paper diagram — cannot be derived from LaTeX
    -- [SORRY] suggested_next: reformulate as algebraic face-count condition
    -- [SORRY] impact: blocks ExcludedMapsCharacterization
    sorry
  ```

### Strategy G — Excluded maps classification (Euler/handshake case analysis):
  When proving "maps with condition P must be one of {tetrahedron, 3-prism, Figure 1b}",
  use Euler formula + handshake + 3-regularity for genus 0:
  - From these axioms: 3*p_3 + 2*p_4 + p_5 + 0*p_6 - p_7 - ... = 12
  - Correct exceptional maps for genus 0 (VERIFY these before using):
      Tetrahedron: p_3=4, rest 0 → V=4, E=6
      3-prism:     p_3=2, p_4=3, rest 0 → V=6, E=9
      Figure 1b:   p_3=2, p_4=2, p_5=2, rest 0 → V=8, E=12
        (Check: 3*2+2*2+1*2=12 ✓, F=6, handshake: 24=2*12 ✓, regularity: 24=3*8 ✓)
  - IMPORTANT: any definition of `IsFigure1b` MUST use p_4=2 (NOT p_4=1).
  Proof sketch:
  ```lean
  intro h
  have hkey : 3 * (maps.p_i 3 : ℤ) + 2 * maps.p_i 4 + maps.p_i 5 = 12 := by
    -- linarith/omega after push_cast using euler_formula, handshake, regularity
  rcases h with h1 | h2 | h3
  · -- HasAdjacentTriangles: maps.p_i 3 ≥ 2, use hkey to narrow to 3 cases by omega
    ...
  ```
  Only if you truly cannot complete the proof, annotate the sorry:
  ```
  -- [SORRY] class: excluded_maps_classification
  -- [SORRY] reason: case analysis on face vectors satisfying ∑(6-k)*p_k=12 with p_3≥2
  -- [SORRY] suggested_next: use omega on the linear constraint to enumerate possibilities
  -- [SORRY] impact: blocks downstream nodes
  ```

### Strategy H — Conjunction goals with proved lower bound:
  When the main theorem goal is `⟨lower_bound_part, equality_family_part⟩`:
  - The lower_bound part: use the relevant `HexagonEdgesLowerBound` or similar lemma
  - The equality_family part: use `InfiniteEqualityFamily g maps` (if proved) directly,
    or destructure `maps.equality_family n` to get the explicit witness:
  ```
  exact ⟨HexagonEdgesLowerBound maps h1, InfiniteEqualityFamily g maps⟩
  -- OR if InfiniteEqualityFamily is not in scope:
  refine ⟨HexagonEdgesLowerBound maps h1, ?_⟩
  exact Set.infinite_of_injective_forall_mem (fun n => ⟨..., maps.equality_family n⟩) ...
  ```

## ⚡ Self-assessment rule — read this BEFORE writing any proof:

**STEP 1 — assess before you write**:
Look at the goal. Do you have a clear, complete proof path using ONLY:
  - The geometric axiom lemmas listed above (euler_formula, handshake, regularity, etc.)
  - Standard Mathlib/omega/linarith/ring tactics
  - Already-proved Polib lemmas listed in the prompt

If YES → attempt the proof.
If NO (unclear path, missing lemma, complex combinatorics) → **go straight to sorry** (see Step 2).

**STEP 2 — when in doubt, sorry immediately**:
A compilable sorry is infinitely better than broken tactics. If you are not confident:
```lean
import Mathlib
import Polib

lemma YourLemmaName {g : ℤ} (maps : SimplyCon3ConnectedMap g) ... : ... := by
  -- [SORRY] class: <choose one: missing_axiom | missing_mathlib | complex_combinatorics | missing_figure_definition>
  -- [SORRY] reason: <one sentence explaining exactly what is missing>
  -- [SORRY] suggested_next: <specific lemma name or tactic to search for>
  -- [SORRY] impact: blocks <downstream node name>
  sorry
```
This compiles on the first attempt. Broken tactics waste multiple rounds and still end in sorry.

**FORBIDDEN**: Writing partial tactic proofs that you know will not compile.
A bare `sorry` with proper annotation is always the correct fallback.
**FORBIDDEN**: Writing `sorry [text]` or `sorry SomeName` — sorry must ALWAYS be alone on its line.
  Wrong: `sorry [SORRY: reason]`  Right: `-- [SORRY] reason: reason\n  sorry`

## Standing output rules (apply to every node):
4. Use `∑ x ∈ s, f x` notation (with ∈), NOT `∑ x in s, f x`.
5. Never write `axiom` declarations — use structured sorry instead.
   ⛔ NEVER add proposition/proof fields to `SimplyCon3ConnectedMap`. The structure contains
   ONLY data: m, p_i, v, e, total_occ. All facts are standalone sorried lemmas. No exceptions.
6. If you cannot prove a sub-goal, use the structured sorry format shown in Strategy E above.
7. Return ONLY the complete Lean 4 file inside a single ```lean fence.
8. ALWAYS use `import Mathlib` (umbrella). NEVER import specific Mathlib submodules.
9. CRITICAL — write warning-free code. The Lean linter will REJECT the file if any of these appear:
   - Unused hypothesis/parameter: use `_` prefix — write `(_h : P)` not `(h : P)`.
   - Unnecessary tactic: do NOT write `push_cast` before `ring`/`simp` unless needed.
   - Style: do NOT break a signature across lines with a trailing space after `(g : ℤ)`.
   - Never use `set_option linter.* false` — fix the cause instead.
10. CRITICAL — use concrete types, NOT abstract ones:
   - ALWAYS use `SimplyCon3ConnectedMap g` (where `g : ℤ`) as the map type.
   - NEVER write `{M : Type*}` or generic function arguments like `(pvec : M → ℕ → ℤ)`.
   - Access face counts as `maps.p_i k`, edge count as `maps.e`, vertex count as `maps.v`.
   - Call geometric axioms as standalone lemmas: `euler_formula maps`, `handshake maps`,
     `regularity maps`, `kgon_occupation_bound maps`, `quad_adj_constraint maps`,
     `quad_occ_reduction maps`, `occupation_conservation maps`, etc.
"""

# Dynamic user prompt — contains only node-specific content.
# Static reference material lives in LEAN_GENERATION_SYSTEM_PROMPT (sent as --system-prompt).
LEAN_GENERATION_PROMPT = """\
Generate Lean 4 code for the following blueprint node.

Node ID: {node_id}
Node type: {node_type}
Description: {description}
LaTeX fragment: {latex_fragment}

{goal_context}

## Required file header (copy exactly):
```lean
import Mathlib
import Polib
{dep_imports}```

## Previously proved dependencies (usable via the imports above):
{dep_details}

## Mathlib search hints:
{mathlib_hints}

{github_snippets}{local_references}{prior_context}
Instructions:
1. Start your file with the exact header shown above (import Mathlib, import Polib,
  then any dep imports). Do NOT redefine SimplyCon3ConnectedMap or any dep — they are
  already available.
2. After the header, add any helper lemmas specific to this node. IMPORTANT: all helper
  lemmas must be declared `private` to avoid polluting the global namespace and
  name collisions with existing `Polib` identifiers. If you need a non-private lemma
  (very rare), prefix its name with the node id to ensure uniqueness.
3. When producing arithmetic/linear intermediate steps that `linarith` should close,
  include explicit `have` lemmas with `push_cast`/`exact_mod_cast` or simple rewrites
  so that numeric casts between `ℕ` and `ℤ` are explicit. Example pattern:
  `have h : (k : ℤ) / 2 = _ := by push_cast; norm_num; exact ...` then `rw [h]`.
4. Avoid reusing global names already present in Polib; if unsure, use `private`.
5. {goal_instruction}
"""

# goal_context for the root theorem — shows full locked signature
_GOAL_CONTEXT_MAIN = (
    "Locked goal signature (IMMUTABLE — you MUST prove this exactly as written):\n"
    "{lean_signature}"
)

# goal_context for intermediate nodes — name only, no full signature shown
_GOAL_CONTEXT_INTERMEDIATE = (
    "Final theorem this node supports: `{theorem_name}` (do NOT write it here —\n"
    "this file must only contain the `{node_id}` {node_type} described above).\n"
    "**CRITICAL — NAMING**: The last declaration MUST start with exactly "
    "`{node_type} {node_id}` — this identifier is fixed by the system and cannot be changed."
)

# Instruction #3 for the root theorem node
_GOAL_INSTR_MAIN = (
    "The LAST declaration in the file MUST be the locked theorem with its EXACT signature\n"
    "   shown above. Prove it using your helper lemmas; the name must be exactly as given."
)

# Instruction #3 for intermediate nodes
_GOAL_INSTR_INTERMEDIATE = (
    "The LAST declaration MUST be named EXACTLY `{node_id}` (a {node_type}). "
    "Write `{node_type} {node_id} ...` — the identifier `{node_id}` is locked and "
    "must not be abbreviated, expanded, paraphrased, or replaced with any other name. "
    "**FORBIDDEN**: do not write any `theorem` or `lemma` called `{theorem_name}` "
    "anywhere in this file — it belongs in a separate file assembled later."
)
