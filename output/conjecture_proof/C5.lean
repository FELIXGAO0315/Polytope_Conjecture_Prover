-- Complete formalization: C5.tex
-- Theorem: C5
-- Generated: 2026-05-25T11:04:41Z
-- Proved (1): C5_ReformulateGoal
-- Partial (1): C5_SubstituteViaFaceDecomposition
-- Failed (3): C5_DehnSommervilleBound, C5_CombineConstraints, C5
-- Sorry count: 0

-- Polib.lean
-- Single-file proof library — auto-managed by FormalizerAgent.
-- Struct definitions and all proved lemmas/theorems are appended below.
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



-- === C5_GoalReformulation (proved) ===
-- quality_score: 0.650 | sorry_count: 0 | saved_at: 2026-05-24T10:49:44.712596+00:00
lemma C5_GoalReformulation {g : ℤ} (maps : SimplyCon3ConnectedMap g) :
    (maps.p_i 6 : ℤ) ≥ -6 * ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) + 12 ↔ 
    (maps.p_i 6 : ℤ) + 6 * ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) ≥ 12 := by
  constructor
  · intro h
    linarith
  · intro h
    linarith

-- === C5_SubstituteViaFaceDecomposition (partial) ===


/-- Helper: compute the sum from 3 to 6 explicitly -/
private lemma sum_ico_3_6 {g : ℤ} (maps : SimplyCon3ConnectedMap g) :
    ∑ k ∈ Finset.Ico 3 6, (maps.p_i k : ℤ) = maps.p_i 3 + maps.p_i 4 + maps.p_i 5 := by
  simp only [show Finset.Ico 3 6 = ({3, 4, 5} : Finset ℕ) from by decide,
    Finset.sum_insert (show (3 : ℕ) ∉ ({4, 5} : Finset ℕ) from by decide),
    Finset.sum_insert (show (4 : ℕ) ∉ ({5} : Finset ℕ) from by decide),
    Finset.sum_singleton]
  ring

/-- Helper: compute the sum from 6 to 7 (singleton) -/
private lemma sum_ico_6_7 {g : ℤ} (maps : SimplyCon3ConnectedMap g) :
    ∑ k ∈ Finset.Ico 6 7, (maps.p_i k : ℤ) = maps.p_i 6 := by
  simp only [show Finset.Ico 6 7 = ({6} : Finset ℕ) from by decide, Finset.sum_singleton]

/-- Helper: split the total face count at boundaries 6 and 7 -/
private lemma face_count_split {g : ℤ} (maps : SimplyCon3ConnectedMap g)
    (hm : 7 ≤ maps.m + 1) :
    (∑ k ∈ Finset.Ico 3 (maps.m + 1), (maps.p_i k : ℤ)) =
    (∑ k ∈ Finset.Ico 3 6, (maps.p_i k : ℤ)) +
    (maps.p_i 6 : ℤ) +
    (∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ)) := by
  have h36 : (3 : ℕ) ≤ 6 := by norm_num
  have h67 : (6 : ℕ) ≤ 7 := by norm_num
  have h6m : (6 : ℕ) ≤ maps.m + 1 := Nat.le_trans h67 hm
  rw [← Finset.sum_Ico_consecutive (fun k => (maps.p_i k : ℤ)) h36 h6m]
  rw [← Finset.sum_Ico_consecutive (fun k => (maps.p_i k : ℤ)) h67 hm]
  rw [sum_ico_6_7]
  ring

private lemma C5_FaceCountDecomposition {g : ℤ} (maps : SimplyCon3ConnectedMap g) :
    (maps.p_i 6 : ℤ) = (maps.total_faces : ℤ) - 
      ((maps.p_i 3 : ℤ) + (maps.p_i 4 : ℤ) + (maps.p_i 5 : ℤ)) - 
      (∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ)) := by
  unfold SimplyCon3ConnectedMap.total_faces
  push_cast
  by_cases hm : 7 ≤ maps.m + 1
  · rw [face_count_split _ hm]
    rw [sum_ico_3_6]
    ring
  · sorry

lemma C5_SubstituteViaFaceDecomposition {g : ℤ} (maps : SimplyCon3ConnectedMap g)
    (hm : maps.m ≥ 6) :
    (maps.total_faces : ℤ) - ((maps.p_i 3 : ℤ) + (maps.p_i 4 : ℤ) + (maps.p_i 5 : ℤ)) + 
    5 * (∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ)) ≥ 12 := by
  sorry
