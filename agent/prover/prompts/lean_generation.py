"""Shared Lean-side constants consumed by the prover pipeline.

Only one thing remains here:

  * ``SHARED_MODULE_CONTENT`` — the canonical Inventory header (data
    structure + opaque ``IsMap`` predicate + geometric axiom signatures).
    Hashed into the blueprint cache key so any change to the structure
    or to an axiom signature auto-invalidates cached blueprints.

The full ``LEAN_GENERATION_PROMPT`` / ``LEAN_GENERATION_SYSTEM_PROMPT`` /
``FIX_LOOP_POLIB_REF`` / per-goal context templates that used to live here
were retired together with the legacy ``_generate_lean`` fix-loop machinery;
``LEAN_PREAMBLE`` followed in the v3.5-plus cleanup (its only consumer,
``lean_codegen.ensure_preamble``, was dead code).
"""

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

/-- There is an infinite REALIZABLE family in genus g achieving the p₆ equality
    case, with max face sizes unbounded below by n+6. NOTE: takes no `maps`
    argument. -/
lemma equality_family {g : ℤ} :
    ∃ (f : ℕ → SimplyCon3ConnectedMap g), Function.Injective f ∧
      ∀ n : ℕ,
        IsMap (f n) ∧
        n + 6 ≤ (f n).m ∧
        3 * ((f n).p_i 6 : ℤ) =
          12 * (1 - g) - (2 * ((f n).p_i 4 : ℤ) + 3 * ((f n).p_i 5 : ℤ)) +
          ∑ k ∈ Finset.Ico 7 ((f n).m + 1),
            (((k : ℤ) + 1) / 2 - 6) * ((f n).p_i k : ℤ) := by sorry
"""
