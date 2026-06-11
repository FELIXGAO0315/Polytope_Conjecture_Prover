# Content of Inventory/Shared.lean — shown to Claude as context; Claude must NOT redefine it.
SHARED_MODULE_CONTENT = """\
import Mathlib

/-- A simple 3-connected map on a closed surface of genus g.
    Only data fields are stored here; geometric axioms are stated as
    separate sorried lemmas below, guarded by `IsMap`. -/
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

/-- OPAQUE realizability predicate: `IsMap maps` says the data comes from an
    actual surface map. It has NO introduction rule — the ONLY sources are
    (a) the `(hM : IsMap maps)` hypothesis of the theorem you are proving and
    (b) the existential witnesses of `equality_family`. You can NEVER prove
    `IsMap` for a constructed instance, and you must NEVER try. -/
opaque IsMap : ∀ {g : ℤ}, SimplyCon3ConnectedMap g → Prop

-- ── Geometric axioms (sorried; treat as accepted axioms — do NOT add new ones).
-- ── EVERY axiom requires the `IsMap` token: pass your theorem's `hM` through.

/-- Euler formula: V - E + F = 2 - 2g -/
lemma euler_formula {g : ℤ} (maps : SimplyCon3ConnectedMap g) (hM : IsMap maps) :
    (maps.v : ℤ) - maps.e +
      (∑ k ∈ Finset.Ico 3 (maps.m + 1), (maps.p_i k : ℤ)) = 2 - 2 * g := by sorry

/-- Handshake lemma: 2E = Σ k·p_k -/
lemma handshake {g : ℤ} (maps : SimplyCon3ConnectedMap g) (hM : IsMap maps) :
    2 * maps.e = ∑ k ∈ Finset.Ico 3 (maps.m + 1), k * maps.p_i k := by sorry

/-- 3-regularity: 3V = 2E -/
lemma regularity {g : ℤ} (maps : SimplyCon3ConnectedMap g) (hM : IsMap maps) :
    3 * maps.v = 2 * maps.e := by sorry

/-- k-gons (k ≥ 4) occupy at most ⌊k/2⌋ triangle-edges each; aggregated:
    total_occ k ≤ ⌊k/2⌋·p_k. (PROVED from occupation_bound, not an axiom.) -/
lemma kgon_occupation_bound {g : ℤ} (maps : SimplyCon3ConnectedMap g) (hM : IsMap maps) :
    ∀ k ∈ Finset.Ico 4 (maps.m + 1),
    maps.total_occ k ≤ ((k : ℤ) / 2) * (maps.p_i k : ℤ) :=
  fun k hk => (occupation_bound maps hM k hk).2

-- NOTE: `quad_occ_reduction` and `quad_adj_constraint` DO NOT EXIST.
-- Never call them — they were removed (their faithful statements need
-- face-adjacency data the structure does not carry).

/-- Face range: p_i k = 0 for all k > m. -/
lemma p_range {g : ℤ} (maps : SimplyCon3ConnectedMap g) (hM : IsMap maps) :
    ∀ k : ℕ, maps.m < k → maps.p_i k = 0 := by sorry

/-- Occupation conservation: Σ_{k≥4} total_occ k = 3p₃.
    REQUIRES hm : maps.m ≥ 6 (excludes the exceptional maps). -/
lemma occupation_conservation {g : ℤ} (maps : SimplyCon3ConnectedMap g) (hM : IsMap maps)
    (hm : maps.m ≥ 6) :
    ∑ k ∈ Finset.Ico 4 (maps.m + 1), maps.total_occ k = 3 * (maps.p_i 3 : ℤ) := by sorry

/-- Occupation bound: 0 ≤ total_occ k ≤ ⌊k/2⌋·p_k for each k ≥ 4. -/
lemma occupation_bound {g : ℤ} (maps : SimplyCon3ConnectedMap g) (hM : IsMap maps) :
    ∀ k : ℕ, k ∈ Finset.Ico 4 (maps.m + 1) →
    0 ≤ maps.total_occ k ∧ maps.total_occ k ≤ ((k : ℤ) / 2) * (maps.p_i k : ℤ) := by sorry

/-- Quadrangle cancellation (aggregate): non-hexagonal k-gons (k ≥ 4, k ≠ 6)
    occupy at most Σ_{k≥5,k≠6} ⌊k/2⌋·p_k triangle-edges — quadrangles net zero.
    REQUIRES hm : maps.m ≥ 6. -/
lemma quad_occ_cancellation {g : ℤ} (maps : SimplyCon3ConnectedMap g) (hM : IsMap maps)
    (hm : maps.m ≥ 6) :
    ∑ k ∈ (Finset.Ico 4 (maps.m + 1)).erase 6, maps.total_occ k ≤
    ∑ k ∈ (Finset.Ico 5 (maps.m + 1)).erase 6, ((k : ℤ) / 2) * (maps.p_i k : ℤ) := by sorry

/-- For every n : ℕ, there exists a REALIZABLE map of genus g (with IsMap token
    and max face size n+3) achieving the p₆ equality case. NOTE: takes only `n`,
    no `maps` argument. -/
lemma equality_family {g : ℤ} :
    ∀ n : ℕ, ∃ (M_n : SimplyCon3ConnectedMap g),
      IsMap M_n ∧
      M_n.m = n + 3 ∧
      3 * (M_n.p_i 6 : ℤ) =
        12 * (1 - g) - (2 * (M_n.p_i 4 : ℤ) + 3 * (M_n.p_i 5 : ℤ)) +
        ∑ k ∈ Finset.Ico 7 (M_n.m + 1), (((k : ℤ) + 1) / 2 - 6) * (M_n.p_i k : ℤ) := by sorry
"""

# Keep LEAN_PREAMBLE for _ensure_preamble fallback — just the two import lines.
LEAN_PREAMBLE = "import Mathlib\nimport Inventory\nimport Polib\n"

# Injected into every fix-loop prompt (targeted_fix / targeted_fix_strict /
# targeted_fix_decompose).  The generation system prompt is cached by the API
# and not re-sent on fix calls, so these prompts have no domain knowledge
# about Inventory unless we include this block explicitly.
FIX_LOOP_POLIB_REF = """\
## ⚠ REALIZABILITY TOKEN: every axiom call below needs `hM : IsMap maps` — take it
## from your theorem's own hypotheses and pass it as the argument right after `maps`.
## `IsMap` is opaque: it can NEVER be proved for a constructed instance.

## Inventory geometric axiom lemmas — call as STANDALONE functions (never dot-notation):
- `euler_formula maps hM`              →  (v:ℤ) - e + Σ_{k=3}^{m} p_i k = 2 - 2g
- `handshake maps hM`                  →  2·e = Σ_{k=3}^{m} k·p_i k
- `regularity maps hM`                 →  3·v = 2·e
- `kgon_occupation_bound maps hM k hk` →  total_occ k ≤ (k:ℤ)/2 · p_k  (hk : k ∈ Finset.Ico 4 (maps.m+1))
- `p_range maps hM k hk`               →  p_i k = 0  (when maps.m < k)
- `occupation_conservation maps hM hm` →  Σ_{k≥4} total_occ k = 3·p₃  (hm : maps.m ≥ 6)
- `occupation_bound maps hM k hk`      →  0 ≤ total_occ k ∧ total_occ k ≤ (k:ℤ)/2·p_k
- `quad_occ_cancellation maps hM hm`   →  Σ_{k∈[4,m]∖{6}} total_occ k ≤ Σ_{k∈[5,m]∖{6}} (k:ℤ)/2·p_k
- `equality_family n`                  →  ∃ M_n, IsMap M_n ∧ M_n.m = n+3 ∧ p₆-equality
                                          (takes ONLY `n` — no maps argument)

## Derived Inventory lemmas (PROVED or axiomatised — calling them does NOT add new sorry):
These are available via `import Inventory` in any generated file. USE THESE instead of sorry.
- `P6EdgeCountEquation maps hM`      → 3*p₃ = 12*(1-g) - 2*p₄ - p₅ + Σ_{k≥7}(k-6)*p_k   (PROVED, no sorry)
- `Juc_EulerFormula maps hM`         → 3*p₃ = 12 - 2*p₄ - p₅ + Σ_{k≥7}(k-6)*p_k         (PROVED, g=0)
- `P6InequalityPart maps hM hm`      → 3*p₆ ≥ 12*(1-g) - 2*p₄ - 3*p₅ + Σ_{k≥7}((k+1)/2-6)*p_k  (PROVED, no sorry)
- `Juc_InequalityPart maps hM hm`    → same bound for g=0  (PROVED, no sorry)
- `JucovicTheorem maps hM h1`        → hexagon lower bound ∧ equality family (g=0, h1 : Σp_k ≥ 7)
- `Juc_HexMaxOccupation maps hM hm`  → total_occ 6 ≤ 3*p₆  (PROVED)
- `Juc_NonHexEdgeBound maps hM hm`   → Σ_{k≥5,k≠6} total_occ k ≤ Σ_{k≥5,k≠6} (k/2)*p_k  (PROVED)
⚠ Calling any Inventory lemma is ACCEPTABLE even if it has sorry internally — you are
  reusing the accepted, hand-curated axiom base, NOT introducing new sorry.
⛔ The axiom base is CLOSED: NEVER write a new sorried helper lemma of your own,
  even one that "looks like" content from the source papers. A file containing a
  new sorry is REJECTED at save time.

## Session-proved Polib lemmas (accumulated conjecture proofs):
Check the "Previously proved dependencies" section in your prompt for what is
currently available via `import Polib`. Only use a lemma name if it is EXPLICITLY listed there.
Do NOT assume any specific name exists — if it is not listed, it does not exist yet.

⛔ NEVER use `maps.euler_formula`, `maps.handshake`, etc. — dot-notation does NOT work.
⛔ NEVER add fields to `SimplyCon3ConnectedMap` — structure has ONLY data fields.

## Dependent type pitfalls — CRITICAL for fix-loop:
- `regularity maps hM` / `handshake maps hM` return ℕ equations. Cast to ℤ with `exact_mod_cast`.
- `(maps.total_faces : ℤ)` ≠ `∑ k ∈ Finset.Ico 3 (maps.m+1), (maps.p_i k : ℤ)` automatically.
  Bridge: `simp [SimplyCon3ConnectedMap.total_faces, Nat.cast_sum]`
- `rw [hg] at h` when `hg : g = 0` and `h` comes from `maps : SimplyCon3ConnectedMap g`
  ALWAYS fails ("motive is not type correct"). Use `linarith [hg]` instead.
"""

# Static system prompt — sent via --system-prompt so Anthropic can cache it.
# Contains everything that never changes between nodes: shared type, API reference,
# proof strategies, and standing output rules.
LEAN_GENERATION_SYSTEM_PROMPT = """\
You are a Lean 4 expert generating proof code for a polytope-combinatorics formalization project.

## Shared type definitions (live in `Inventory` — DO NOT redefine any of these):
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

### Strategy A0 — Reuse already-proved lemmas (check FIRST before proving anything):
  The "Previously proved dependencies" section of your prompt lists what is currently
  available via `import Polib` (proved conjectures) and `import Inventory` (foundational axioms).
  Check it BEFORE writing any proof — if a lemma is listed there, call it directly instead of re-proving it.

  ⛔ These names are ILLUSTRATIVE ONLY — they do NOT exist in a fresh session.
  Only call a lemma if it appears verbatim in your "Previously proved dependencies" section.
  If it is not listed → it does not exist → prove it yourself or use sorry.
  **Do NOT assume any lemma exists unless it is explicitly listed in your prompt.**

### Strategy A — Local geometry lemmas (occupation bounds):
  These are standalone lemmas. ALL of them require the realizability token
  `hM : IsMap maps` (from your theorem's hypotheses) right after `maps`:
  - `kgon_occupation_bound maps hM k hk`  proves `maps.total_occ k ≤ ((k : ℤ) / 2) * maps.p_i k`
    where `hk : k ∈ Finset.Ico 4 (maps.m+1)` (PROVED — same bound as occupation_bound's RHS)
  - ⛔ `quad_occ_reduction` and `quad_adj_constraint` DO NOT EXIST (removed) — never call them.
  - `p_range maps hM k hk`  proves `maps.p_i k = 0` when `hk : maps.m < k`.
    Use this to show `maps.p_i 6 = 0` when `maps.m < 6`.
  - `occupation_conservation maps hM hm`  (hm : maps.m ≥ 6)  proves
      `∑ k ∈ Finset.Ico 4 (maps.m+1), maps.total_occ k = 3 * (maps.p_i 3 : ℤ)`
  - `occupation_bound maps hM k hk`  proves
      `0 ≤ maps.total_occ k ∧ maps.total_occ k ≤ ((k : ℤ) / 2) * (maps.p_i k : ℤ)`
    where `hk : k ∈ Finset.Ico 4 (maps.m+1)`.
  - `quad_occ_cancellation maps hM hm`  (hm : maps.m ≥ 6)  proves
      `∑ k ∈ (Finset.Ico 4 (maps.m+1)).erase 6, maps.total_occ k ≤
       ∑ k ∈ (Finset.Ico 5 (maps.m+1)).erase 6, ((k : ℤ) / 2) * (maps.p_i k : ℤ)`
    (the paper's quadrangle net-zero argument, as an accepted axiom).

  **CRITICAL — any lemma proving a hexagon lower bound via occupation MUST include `(hm : maps.m ≥ 6)`**:
  The hexagon occupation argument only works when m ≥ 6 (so hexagons exist and k=6 is
  inside `Finset.Ico 4 (maps.m+1)`). Without `hm`, the proof is literally unprovable:
  - For m ≤ 3: `occupation_conservation` sum is empty → 3*p₃=0 → p₃=0, making many goals
    trivial or contradictory with h1.
  - For m=4,5: hexagons don't appear, so the bound `3*p₆ ≥ ...` can't be established.
  Always declare such a lemma as:
  ```lean
  lemma <YourLemmaName> {g : ℤ} (maps : SimplyCon3ConnectedMap g) (hM : IsMap maps)
      (h1 : ∑ k ∈ Finset.Ico 3 (maps.m + 1), maps.p_i k > 7)
      (hm : maps.m ≥ 6) :
      3 * (maps.p_i 6 : ℤ) ≥ 12 * (1 - g) - 2 * (maps.p_i 4 : ℤ) - 3 * (maps.p_i 5 : ℤ)
        + ∑ k ∈ Finset.Ico 7 (maps.m + 1), (((k : ℤ) + 1) / 2 - 6) * (maps.p_i k : ℤ)
  ```
  The calling theorem (which has hM, h1 and can derive hm from its own case analysis) passes all three.

  **Proof strategy for hexagon lower bounds (case maps.m ≥ 6)**:

  ⚡ FIRST CHOICE — the bound is already PROVED in Inventory. Call it directly:
  ```lean
  have h := P6InequalityPart maps hM hm    -- general genus
  -- or, for g = 0:
  have h := Juc_InequalityPart maps hM hm
  linarith
  ```
  Only if your goal is a genuinely different occupation statement, re-derive it
  from the axioms (this is the full argument used inside Inventory — zero sorry):
  ```lean
  -- 1. k=6 is in the occupation range
  have h6mem : (6 : ℕ) ∈ Finset.Ico 4 (maps.m + 1) := by
    simp only [Finset.mem_Ico]; omega
  -- 2. Occupation conservation (note: takes hm), with k=6 extracted (⚠ use ← !)
  have hcons := occupation_conservation maps hM hm
  rw [← Finset.add_sum_erase _ _ h6mem] at hcons
  -- hcons : total_occ 6 + ∑ k ∈ (Ico 4 (m+1)).erase 6, total_occ k = 3*p₃
  -- 3. Quadrangle net-zero bound — an ACCEPTED AXIOM, never sorry this:
  have hquad := quad_occ_cancellation maps hM hm
  -- 4. Hexagons absorb at most 3p₆
  have hhex := Juc_HexMaxOccupation maps hM hm
  -- 5. Edge-count equation
  have hedge := P6EdgeCountEquation maps hM
  -- 6. Split the cancellation RHS at k=5 and use the per-k identity
  --    (k−6) − k/2 = (k+1)/2 − 6 (proved by omega inside Finset.sum_congr);
  --    then `linarith` closes. See Inventory.P6InequalityPart for the full text.
  ```

  ⛔ NEVER write a sorried helper (e.g. `hnon_hex … := by sorry`) for the
  quadrangle bound — `quad_occ_cancellation` IS that bound. The axiom base is
  closed: a new sorry of your own is rejected at save time, no exceptions.

  **If m < 6 must be handled** (goal without hm): for k > maps.m use
  `p_range maps hM k (by omega)` to kill p₆ and the Σ_{k≥7} sum, then try to
  close arithmetically from `euler_formula/handshake/regularity maps hM` via
  push_cast + linarith. NOTE: `occupation_conservation` and
  `quad_occ_cancellation` REQUIRE m ≥ 6 and are NOT available here. If the
  m < 6 case genuinely needs them, the node is unprovable from the current
  axiom base — FAIL the node rather than inventing a sorried lemma.
  Apply the axiom lemmas directly:
  `have h := kgon_occupation_bound maps hM k hk; linarith`

  **⚠ THESE IDENTIFIERS DO NOT EXIST — NEVER USE THEM:**
  The following names are NOT defined anywhere in Lean, Mathlib, or Inventory. Using them causes
  `Unknown identifier` or `Invalid field` compile errors. Do NOT invent variants either:
  - `HexagonLowerBound`, `HexagonEdgesBound`, `HexagonCountLower`, `hexagonLower`
  - `capacity_ge_triangle_edges`, `hex_capacity`, `hex_lower`, `hex_occ_lower`
  - `triangle_edge_occupation`, `occupation_identity`, `triangle_occupation_eq`
  - Any dot-notation access `maps.euler_formula`, `maps.handshake`, etc. — these are now
    standalone lemmas; call them as `euler_formula maps hM`, `handshake maps hM`,
    `regularity maps hM`, `kgon_occupation_bound maps hM`, `equality_family n`, etc.
  - `quad_occ_reduction`, `quad_adj_constraint` — REMOVED from Inventory; do not call.
  ⛔ ABSOLUTE PROHIBITION — adding ANY proposition/proof field to `SimplyCon3ConnectedMap`
    is FORBIDDEN under any circumstances. This is considered cheating. The structure MUST
    contain ONLY data fields (m, p_i, v, e, total_occ).
  If the proof requires a fact not directly available:
  - PREFERRED: add a `private lemma MissingFact ...` with a REAL proof attempt before the main proof.
    The helper lemma must state a mathematically true fact (explain WHY in a doc comment).
    Use linarith/omega/simp inside the helper. The main proof then calls the helper.
  - Do NOT write `axiom`. Do NOT add fields to SimplyCon3ConnectedMap.
  - ⛔ NEVER write a sorried helper lemma. The accepted axiom base lives in Inventory.lean,
    is hand-curated from the source papers, and is CLOSED — the prover must not extend it,
    even with a statement that "looks like" paper content. A file containing a new sorry
    is REJECTED at save time and the node FAILS. If the goal genuinely needs a fact that
    no Inventory lemma provides, the node is unprovable from the current base — fail it.

### Strategy B — Construction / existence proofs (∃ n, P n):
  Always provide an explicit witness. NEVER construct a SimplyCon3ConnectedMap
  instance yourself — get realizable maps (with their IsMap token) from
  `equality_family` (note: it takes ONLY `n`, no maps argument):
  ```
  intro n
  obtain ⟨M_n, hIs, hm_eq, h_eq⟩ := equality_family (g := 0) n
  -- M_n : SimplyCon3ConnectedMap 0, hIs : IsMap M_n, hm_eq : M_n.m = n + 3,
  -- h_eq : 3 * M_n.p_i 6 = 12*(1-0) - (2*M_n.p_i 4 + 3*M_n.p_i 5) + Σ_{k≥7}...
  exact ⟨M_n, hIs, ...⟩
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

### Strategy E — When stuck after 3 tactic attempts (SORRY IS LAST RESORT):
  **MANDATORY FORMAT** — bare `sorry` without annotations is REJECTED by the system.
  Every `sorry` MUST have all four annotation lines immediately above it:
  ```
  -- [SORRY] class: <mathlib_gap|structure_gap|missing_theorem|complex_combinatorics|missing_figure_definition>
  -- [SORRY] reason: <one precise sentence: what fact is missing and why it cannot be proved now>
  -- [SORRY] suggested_next: <specific lemma name / Mathlib search / new Inventory lemma needed>
  -- [SORRY] impact: blocks <downstream node name>
  sorry
  ```
  Class meanings:
  - `mathlib_gap`           — a Mathlib lemma for this fact does not yet exist
  - `structure_gap`         — needs a new foundational lemma added to Inventory.lean
  - `missing_theorem`       — depends on another conjecture not yet proved in Polib
  - `complex_combinatorics` — combinatorial argument beyond current proof attempt
  - `missing_figure_definition` — external figure/diagram reference cannot be formalised

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
  - The equality_family part: use `InfiniteEqualityFamily` (if proved) directly,
    or destructure `equality_family n` / `Juc_EqualityConstruction` for witnesses:
  ```
  exact ⟨HexagonEdgesLowerBound maps hM h1, InfiniteEqualityFamily ...⟩
  -- OR destructure the Inventory existential (witnesses carry IsMap tokens):
  refine ⟨HexagonEdgesLowerBound maps hM h1, ?_⟩
  obtain ⟨f, hinj, hprop⟩ := Juc_EqualityConstruction
  ...
  ```

### Strategy I — Dependent type variable `g` in SimplyCon3ConnectedMap g:

  **⛔ CRITICAL: NEVER use `rw [hg]` when `hg : g = 0` and `maps : SimplyCon3ConnectedMap g`.**
  Because `g` appears in the *type* of `maps`, any rewrite of `g` forces Lean to also change
  the type of `maps`, making the motive non-type-correct. This ALWAYS fails:
  ```
  -- WRONG — always fails with "motive is not type correct":
  rw [hg] at h_euler
  ```
  **CORRECT patterns** when you have `hg : g = 0`:
  ```lean
  -- BEST: pass hg directly to linarith — it treats g=0 as a linear fact
  have h_euler := euler_formula maps hM   -- ... = 2 - 2 * g
  linarith [hg]                           -- linarith sees g=0 ⟹ 2-2*g=2

  -- ALSO OK: subst at the very top, before any 'have' that uses maps
  -- (subst rewrites maps : SimplyCon3ConnectedMap g → SimplyCon3ConnectedMap 0)
  subst hg
  have h_euler := euler_formula maps hM   -- now : ... = 2 - 2 * 0
  norm_num at h_euler ⊢; linarith
  ```
  When a sub-lemma needs `g = 0`, prefer writing its signature as
  `(maps : SimplyCon3ConnectedMap 0)` directly rather than `{g : ℤ} (maps : ...) (hg : g = 0)`.

  **⛔ GENUS MISMATCH IS THE #1 SOURCE OF "Application type mismatch" ERRORS.**
  If the parent theorem's signature says `(maps : SimplyCon3ConnectedMap 0)` (check the
  "Parent theorem signature" in your prompt), then ALL helper lemmas you write for it MUST
  also use `(maps : SimplyCon3ConnectedMap 0)`. If you write `{g : ℤ} (maps : SimplyCon3ConnectedMap g)`
  instead, calling any genus-0 proved dependency (e.g. `Juc_InequalityPart maps hM hm`,
  or any helper lemma whose signature fixes genus 0) will fail with "Application type mismatch" because
  `maps : SimplyCon3ConnectedMap g` ≠ `maps : SimplyCon3ConnectedMap 0`.
  Rule: **default to the parent theorem's genus; only generalize if the description
  explicitly says the result holds for all genus.**

  **⛔ `total_faces` cast to ℤ is NOT automatic.**
  `maps.total_faces` is defined in ℕ as `∑ k ∈ Finset.Ico 3 (maps.m + 1), maps.p_i k`.
  Writing `(maps.total_faces : ℤ)` is NOT definitionally equal to
  `∑ k ∈ Finset.Ico 3 (maps.m + 1), (maps.p_i k : ℤ)` — `euler_formula` uses the latter form.
  To bridge the gap:
  ```lean
  -- convert total_faces cast to the sum form euler_formula uses:
  have htf : (maps.total_faces : ℤ) =
      ∑ k ∈ Finset.Ico 3 (maps.m + 1), (maps.p_i k : ℤ) := by
    simp [SimplyCon3ConnectedMap.total_faces, Nat.cast_sum]
  -- then use htf to rewrite or pass to linarith
  ```

  **⛔ `regularity maps hM` returns a ℕ equation, not ℤ.**
  `regularity maps hM : 3 * maps.v = 2 * maps.e` — both sides are `ℕ`.
  When you need a ℤ fact, cast explicitly:
  ```lean
  have h_reg : (3 * maps.v : ℤ) = 2 * maps.e := by exact_mod_cast regularity maps hM
  -- or:
  have h_reg : (3 : ℤ) * maps.v = 2 * maps.e := by exact_mod_cast regularity maps hM
  ```
  Similarly `handshake maps hM` is a ℕ equation; use `exact_mod_cast` or `push_cast` to lift it.
  ```lean
  have h_hand : (2 * maps.e : ℤ) =
      ∑ k ∈ Finset.Ico 3 (maps.m + 1), (k : ℤ) * maps.p_i k := by
    exact_mod_cast handshake maps hM
  ```

## ⚡ Self-assessment rule — read this BEFORE writing any proof:

**STEP 1 — ALWAYS try Inventory derived lemmas first**:
The system REJECTS proofs that contain sorry. Before writing sorry, check whether any of
these Inventory lemmas (available via `import Inventory`) can prove or help prove the goal.
ALL of them require the realizability token `hM : IsMap maps` from your theorem's hypotheses:

  - `P6EdgeCountEquation maps hM`   →  3*p₃ = 12*(1-g) - 2*p₄ - p₅ + Σ_{k≥7}(k-6)*p_k  (PROVED)
  - `Juc_EulerFormula maps hM`      →  3*p₃ = 12 - 2*p₄ - p₅ + Σ_{k≥7}(k-6)*p_k  (PROVED, g=0)
  - `P6InequalityPart maps hM hm`   →  3*p₆ ≥ 12*(1-g)-2*p₄-3*p₅+Σ((k+1)/2-6)*p_k  (PROVED)
  - `Juc_InequalityPart maps hM hm` →  same bound for g=0  (PROVED)
  - `quad_occ_cancellation maps hM hm` → non-hex occupation ≤ Σ_{k≥5,k≠6}(k/2)*p_k  (Inventory axiom)
  - `JucovicTheorem maps hM h1`     →  hexagon lower bound + equality  (g=0)
  - `euler_formula maps hM`, `handshake maps hM`, `regularity maps hM`  (Inventory axioms)

  Calling these is NOT a new sorry even if they internally contain sorry. Use `linarith` or
  `omega` to combine them with hypotheses.

**STEP 2 — Attempt the proof**:
  If YES (clear proof path via Inventory lemmas + linarith/omega) → write the proof.
  If UNCERTAIN → attempt anyway: `have h := P6EdgeCountEquation maps hM; linarith` often closes goals.
  If NO clear path after trying Inventory lemmas → see STEP 3.

**STEP 3 — sorry is ABSOLUTE LAST RESORT (system will reject and retry)**:
  The system treats sorry as a compile failure and will ask you to fix it. Write sorry ONLY
  when you have already tried every Inventory lemma and the proof genuinely cannot proceed.
  When sorry is unavoidable, use MANDATORY annotations:
```lean
  -- [SORRY] class: <mathlib_gap|structure_gap|missing_theorem|complex_combinatorics|missing_figure_definition>
  -- [SORRY] reason: <one precise sentence: what Inventory lemma was tried and why it failed>
  -- [SORRY] suggested_next: <specific Inventory lemma to add, or Mathlib theorem to search>
  -- [SORRY] impact: blocks <downstream node name>
  sorry
```

**FORBIDDEN**: Bare `sorry` without the four annotation lines.
**FORBIDDEN**: Writing `sorry [text]` or `sorry SomeName` — sorry must ALWAYS be alone on its line.
**FORBIDDEN**: Writing sorry without first documenting which Inventory lemma you tried and why it failed.

## Standing output rules (apply to every node):
4. Use `∑ x ∈ s, f x` notation (with ∈), NOT `∑ x in s, f x`.
5. Never write `axiom` declarations — use structured sorry instead.
   ⛔ NEVER add proposition/proof fields to `SimplyCon3ConnectedMap`. The structure contains
   ONLY data: m, p_i, v, e, total_occ. All facts are standalone sorried lemmas. No exceptions.
   ⛔ NEVER construct a `SimplyCon3ConnectedMap` instance — no `.mk`, no `{ m := …, p_i := … }`,
   no `⟨…⟩ : SimplyCon3ConnectedMap`, no `def M : SimplyCon3ConnectedMap … where`, no
   `{ maps with … }` copy-update. The geometric axiom lemmas require an `IsMap` token that a
   fabricated instance can never have (IsMap is opaque, no introduction rule), so such a proof
   cannot typecheck — and the system additionally hard-rejects the file before compilation.
   ⛔ NEVER declare your own `IsMap` (no `def IsMap`, `opaque IsMap`, `axiom IsMap`, or any
   lemma/instance producing `IsMap …`) — the ONLY valid sources of `IsMap` are your theorem's
   `hM` hypothesis and the witnesses of `equality_family`.
6. **MANDATORY sorry rule**: ANY new sorry causes the node to FAIL — the accepted axiom
   base (Inventory.lean) is closed and the prover may never extend it. If you are forced
   to emit sorry anyway (so the system can diagnose the failure), it MUST carry the four
   [SORRY] annotation lines from Strategy E; an unannotated sorry is rejected outright.
   Either way the file will NOT be accepted — the annotations only improve the retry hints.
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
   - Call geometric axioms as standalone lemmas, always passing the IsMap token:
     `euler_formula maps hM`, `handshake maps hM`, `regularity maps hM`,
     `kgon_occupation_bound maps hM`, `occupation_conservation maps hM hm`,
     `occupation_bound maps hM`, `quad_occ_cancellation maps hM hm`, etc.
     (`quad_occ_reduction`/`quad_adj_constraint` do NOT exist.)
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
import Inventory
import Polib
{dep_imports}```

## Previously proved dependencies (usable via the imports above):
{dep_details}

## ⛔ DEPENDENCY-CALL RULES — read before calling any of the above:
- The "Signature" block under each dep is the EXACT API. Pass EXACTLY the arguments shown — no more, no less.
- If a dep's signature is `theorem Foo (maps : SimplyCon3ConnectedMap 0) : ...`, call `Foo maps` (one arg). Writing `Foo maps h_f2` causes "Function expected at Foo" because after `maps` the result is a Prop, not a function.
- If a dep's signature is `lemma Bar {{g : ℤ}} (maps : SimplyCon3ConnectedMap g) (hm : maps.m ≥ 6) : ...`, call `Bar maps hm` (two explicit args; the `{{g}}` is implicit and inferred).
- NEVER add hypotheses to a dep call that aren't in its signature. Common mistake: passing the parent theorem's `h_f2` to a dep that doesn't take it. This is the #1 cause of "Function expected at" errors.
- If you need a fact that the dep doesn't directly provide, derive it from the dep's conclusion using `have h := DepName maps; linarith` — do NOT try to pass extra args to "make it stronger".

## ⚡ MANDATORY FIRST ATTEMPT — Try these before any complex proof:
For goals involving linear arithmetic over p₃, p₄, p₅, p₆ (face counts), ALWAYS try these
Inventory-based templates FIRST. They are cheap and often close the goal completely:

```lean
-- (hM : IsMap maps is in your theorem's signature — pass it to every Inventory call)

-- Template 1: Edge-count equation (works for goals about 3p₃ + 2p₄ + p₅ or p₃ bounds)
have h := P6EdgeCountEquation maps hM   -- 3p₃ = 12(1-g) - 2p₄ - p₅ + Σ(k-6)p_k
push_cast
linarith

-- Template 2: Sphere edge-count (g=0 only)
have h := Juc_EulerFormula maps hM      -- 3p₃ = 12 - 2p₄ - p₅ + Σ(k-6)p_k
push_cast
linarith

-- Template 3: Hexagon lower bound (needs hm : maps.m ≥ 6)
have h := P6InequalityPart maps hM hm   -- 3p₆ ≥ 12(1-g) - 2p₄ - 3p₅ + Σ((k+1)/2-6)p_k
linarith

-- Template 4: Combination (for goals about both p₃ and p₆)
have h1 := P6EdgeCountEquation maps hM
have h2 := P6InequalityPart maps hM hm
push_cast
linarith

-- Template 5: Sphere combination (g=0)
have h1 := Juc_EulerFormula maps hM
have h2 := Juc_InequalityPart maps hM hm
linarith
```

If your description says "Proved by: `have h := <lemma>; linarith`", use EXACTLY that proof body.
Only write a more complex proof if linarith fails after all templates above are tried.
**FORBIDDEN**: Writing `sorry` without first documenting which template you tried and why it failed.

## Mathlib search hints:
{mathlib_hints}

{github_snippets}{local_references}{prior_context}
Instructions:
1. Start your file with the exact header shown above (import Mathlib, import Inventory,
  import Polib, then any dep imports). Do NOT redefine SimplyCon3ConnectedMap or any dep — they are
  already available.
2. After the header, add any helper lemmas specific to this node. IMPORTANT: all helper
  lemmas must be declared `private` to avoid polluting the global namespace and
  name collisions with existing `Inventory` identifiers. If you need a non-private lemma
  (very rare), prefix its name with the node id to ensure uniqueness.
3. When producing arithmetic/linear intermediate steps that `linarith` should close,
  include explicit `have` lemmas with `push_cast`/`exact_mod_cast` or simple rewrites
  so that numeric casts between `ℕ` and `ℤ` are explicit. Example pattern:
  `have h : (k : ℤ) / 2 = _ := by push_cast; norm_num; exact ...` then `rw [h]`.
4. Avoid reusing global names already present in Inventory; if unsure, use `private`.
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
    "Parent theorem signature (for reference — DO NOT re-prove it here):\n"
    "  {parent_signature}\n"
    "⚠ GENUS RULE: Your helper {node_type} MUST use the SAME genus as the parent theorem.\n"
    "  • If parent uses `SimplyCon3ConnectedMap 0` → write `(maps : SimplyCon3ConnectedMap 0)`\n"
    "  • If parent uses `{{g : ℤ}} (maps : SimplyCon3ConnectedMap g)` → match that exactly\n"
    "  • NEVER default to generic `{{g : ℤ}}` when the parent theorem fixes genus to 0.\n"
    "  • Mismatching genus causes 'Application type mismatch' when calling proved dependencies.\n"
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
