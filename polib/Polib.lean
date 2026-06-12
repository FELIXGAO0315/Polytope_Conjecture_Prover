-- Polib.lean
-- Dynamic proof accumulation — auto-managed by FormalizerAgent.
-- Foundational axioms are in Inventory.lean; proved conjectures are appended here.
import Mathlib
import Inventory

-- === BEGIN PROVED CONTENT ===

-- === C2_DomainConstraintsFromMap (proved) ===
-- quality_score: 1.000 | sorry_count: 0 | saved_at: 2026-05-31T08:22:06.580990+00:00
lemma C2_DomainConstraintsFromMap {g : ℤ} (maps : SimplyCon3ConnectedMap g)
  (hM : IsMap maps) :
  ((maps.v : ℤ) - maps.e + (maps.total_faces : ℤ) = 2 - 2 * g) ∧
  ((2 : ℤ) * maps.e = (3 : ℤ) * maps.v) ∧
  ((∑ k ∈ Finset.Ico 3 (maps.m + 1), ((6 : ℤ) - k) * (maps.p_i k : ℤ)) = 12 * (1 - g)) ∧
  ((maps.total_faces : ℤ) = ∑ k ∈ Finset.Ico 3 (maps.m + 1), (maps.p_i k : ℤ))
:= by
  have h_euler := euler_formula maps hM
  have h_hand := handshake maps hM
  have h_reg := regularity maps hM
  have h_tf : (maps.total_faces : ℤ) = ∑ k ∈ Finset.Ico 3 (maps.m + 1), (maps.p_i k : ℤ) := by
    simp [SimplyCon3ConnectedMap.total_faces, Nat.cast_sum]
  have h_reg_z : (3 : ℤ) * maps.v = 2 * maps.e := by exact_mod_cast h_reg
  have h_hand_z : (2 : ℤ) * maps.e = ∑ k ∈ Finset.Ico 3 (maps.m + 1), (k : ℤ) * (maps.p_i k : ℤ) := by
    exact_mod_cast h_hand
  
  refine ⟨?_, ?_, ?_, h_tf⟩
  
  · -- Euler's formula with total_faces
    linarith [h_euler, h_tf]
  
  · -- Regularity: 2e = 3v
    linarith [h_reg_z]
  
  · -- Dehn–Sommerville relation: ∑(6-k)·p_k = 12(1-g)
    have sum_expand : ∑ k ∈ Finset.Ico 3 (maps.m + 1), ((6 : ℤ) - k) * (maps.p_i k : ℤ) =
                      (6 : ℤ) * (∑ k ∈ Finset.Ico 3 (maps.m + 1), (maps.p_i k : ℤ)) -
                      ∑ k ∈ Finset.Ico 3 (maps.m + 1), (k : ℤ) * (maps.p_i k : ℤ) := by
      have h : ∑ k ∈ Finset.Ico 3 (maps.m + 1), ((6 : ℤ) - k) * (maps.p_i k : ℤ) =
               ∑ k ∈ Finset.Ico 3 (maps.m + 1), ((6 : ℤ) * (maps.p_i k : ℤ) - (k : ℤ) * (maps.p_i k : ℤ)) := by
        apply Finset.sum_congr rfl
        intro k _
        ring
      rw [h, Finset.sum_sub_distrib, Finset.mul_sum]
    linarith [sum_expand, h_hand_z, h_tf, h_reg_z, h_euler]

-- === C2_LowerDegreeFacesBound (proved) ===
-- quality_score: 1.000 | sorry_count: 0 | saved_at: 2026-05-31T08:31:08.340350+00:00
theorem C2_LowerDegreeFacesBound (maps : SimplyCon3ConnectedMap 0)
    (hM : IsMap maps) :
    3 * (maps.p_i 3 : ℤ) + 2 * (maps.p_i 4 : ℤ) + (maps.p_i 5 : ℤ) ≥
    12 + ∑ k ∈ Finset.Ico 7 (maps.m + 1), (k - 6 : ℤ) * (maps.p_i k : ℤ) := by
  have h := P6EdgeCountEquation maps hM
  push_cast
  linarith

-- === C1 (proved) ===
-- quality_score: 1.000 | sorry_count: 0 | saved_at: 2026-06-11T16:56:26.106160+00:00
theorem C1 (maps : SimplyCon3ConnectedMap 0) (hM : IsMap maps) : maps.p_i 6 ≥ 0 := by
  have h := P6EdgeCountEquation maps hM
  push_cast at *
  omega
