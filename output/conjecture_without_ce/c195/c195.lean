-- Complete formalization: c195
-- Theorem: C195
-- Generated: 2026-07-03T16:41:14Z
-- Proved (2): C195_FaceCountP5Zero, C195_WeightedSumBound
-- Failed (4): C195_CaseLargeS, C195_DehnSommervilleP5Zero, C195_CaseSmallS, C195

-- Polib.lean
-- Dynamic proof accumulation — auto-managed by FormalizerAgent.
-- Foundational axioms are in Inventory.lean; proved conjectures are appended here.
import Mathlib
import Inventory


-- === C195_FaceCountP5Zero (proved) ===

private lemma C195_FaceCountP5Zero (maps : SimplyCon3ConnectedMap 0) (hM : IsMap maps) (h1 : maps.p_i 5 = 0) : (∑ k ∈ Finset.Ico 3 (maps.m + 1), maps.p_i k : ℤ) = maps.p_i 3 + maps.p_i 4 + maps.p_i 6 + ∑ k ∈ Finset.Ico 7 (maps.m + 1), maps.p_i k := by
  push_cast
  set N := max (maps.m + 1) 7 with hNdef
  have hN_ge_7 : 7 ≤ N := le_max_right _ _
  have hN_ge_m1 : maps.m + 1 ≤ N := le_max_left _ _
  have hL : (∑ k ∈ Finset.Ico 3 (maps.m + 1), (maps.p_i k : ℤ)) =
      ∑ k ∈ Finset.Ico 3 N, (maps.p_i k : ℤ) := by
    apply Finset.sum_subset (Finset.Ico_subset_Ico_right hN_ge_m1)
    intros k hk hnot
    simp [Finset.mem_Ico] at hk hnot
    have hkm : maps.m < k := by omega
    rw [p_range maps hM k hkm]
    simp
  have hR : (∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ)) =
      ∑ k ∈ Finset.Ico 7 N, (maps.p_i k : ℤ) := by
    apply Finset.sum_subset (Finset.Ico_subset_Ico_right hN_ge_m1)
    intros k hk hnot
    simp [Finset.mem_Ico] at hk hnot
    have hkm : maps.m < k := by omega
    rw [p_range maps hM k hkm]
    simp
  rw [hL, hR]
  rw [← Finset.sum_Ico_consecutive (fun k => (maps.p_i k : ℤ)) (by norm_num : 3 ≤ 7) hN_ge_7]
  have hSplit : ∑ k ∈ Finset.Ico 3 7, (maps.p_i k : ℤ) =
      (maps.p_i 3 : ℤ) + maps.p_i 4 + maps.p_i 5 + maps.p_i 6 := by
    rw [show (7 : ℕ) = 3 + 1 + 1 + 1 + 1 from rfl]
    repeat rw [Finset.sum_Ico_succ_top (by omega)]
    rw [Finset.Ico_self, Finset.sum_empty]
    ring
  rw [hSplit, h1]
  push_cast
  ring

-- === C195_WeightedSumBound (proved) ===

private lemma C195_WeightedSumBound (maps : SimplyCon3ConnectedMap 0) (hM : IsMap maps) : ∑ k ∈ Finset.Ico 7 (maps.m + 1), ((k : ℤ) - 6) * maps.p_i k ≥ ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) := by
  apply Finset.sum_le_sum
  intro k hk
  rw [Finset.mem_Ico] at hk
  have hk7 : (7 : ℤ) ≤ (k : ℤ) := by exact_mod_cast hk.1
  have hp : (0 : ℤ) ≤ (maps.p_i k : ℤ) := Int.natCast_nonneg _
  nlinarith [hk7, hp]
