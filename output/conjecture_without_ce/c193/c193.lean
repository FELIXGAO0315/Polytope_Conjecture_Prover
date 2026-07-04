-- Complete formalization: c193
-- Theorem: C193
-- Generated: 2026-07-03T11:05:49Z
-- Proved (4): C193_DehnSommervilleP3Zero, C193_WeightedSumBound, C193_CaseLargeS, C193_P6LowerBound
-- Failed (4): C193_FaceCountDecomp, C193_CaseZeroS, C193_CaseOneS, C193

-- Polib.lean
-- Dynamic proof accumulation — auto-managed by FormalizerAgent.
-- Foundational axioms are in Inventory.lean; proved conjectures are appended here.
import Mathlib
import Inventory


-- === C193_DehnSommervilleP3Zero (proved) ===

private lemma C193_DehnSommervilleP3Zero (maps : SimplyCon3ConnectedMap 0) (hM : IsMap maps) (h1 : maps.p_i 3 = 0) : (2 : ℤ) * maps.p_i 4 + maps.p_i 5 = 12 + ∑ k ∈ Finset.Ico 7 (maps.m + 1), (k - 6 : ℤ) * maps.p_i k := by
  have h := Juc_EulerFormula maps hM
  rw [h1] at h
  push_cast at h
  linarith [h]

-- === C193_WeightedSumBound (proved) ===

private lemma C193_WeightedSumBound (maps : SimplyCon3ConnectedMap 0) (hM : IsMap maps) : ∑ k ∈ Finset.Ico 7 (maps.m + 1), (k - 6 : ℤ) * maps.p_i k ≥ ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) := by
  apply Finset.sum_le_sum
  intro k hk
  rw [Finset.mem_Ico] at hk
  have hk7 : (7 : ℤ) ≤ k := by exact_mod_cast hk.1
  have hk6 : (1 : ℤ) ≤ (k : ℤ) - 6 := by linarith
  have hp : (0 : ℤ) ≤ (maps.p_i k : ℤ) := Int.ofNat_nonneg _
  calc (maps.p_i k : ℤ) = 1 * (maps.p_i k : ℤ) := by ring
    _ ≤ ((k : ℤ) - 6) * (maps.p_i k : ℤ) := by
        apply mul_le_mul_of_nonneg_right hk6 hp

-- === C193_CaseLargeS (proved) ===

private lemma C193_CaseLargeS (maps : SimplyCon3ConnectedMap 0) (hM : IsMap maps) (hS : ∑ k ∈ Finset.Ico 7 (maps.m + 1), maps.p_i k ≥ 2) : (maps.p_i 6 : ℤ) ≥ -2 * (∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ)) + 4 := by
  have hS' : (∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ)) ≥ 2 := by
    have h := hS
    have := (Nat.cast_le (α := ℤ)).mpr h
    push_cast at this
    exact this
  have hp6 : (maps.p_i 6 : ℤ) ≥ 0 := Int.natCast_nonneg _
  linarith

-- === C193_P6LowerBound (proved) ===

private lemma C193_P6LowerBound (maps : SimplyCon3ConnectedMap 0) (hM : IsMap maps) (h1 : maps.p_i 3 = 0) (h2 : ∑ k ∈ Finset.Ico 3 (maps.m + 1), maps.p_i k ≥ 17) : (maps.p_i 6 : ℤ) ≥ 5 + maps.p_i 4 - ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) - ∑ k ∈ Finset.Ico 7 (maps.m + 1), (k - 6 : ℤ) * maps.p_i k := by
  have hEuler := Juc_EulerFormula maps hM
  have h1z : (maps.p_i 3 : ℤ) = 0 := by exact_mod_cast h1
  have hDS : (2 : ℤ) * maps.p_i 4 + maps.p_i 5
           = 12 + ∑ k ∈ Finset.Ico 7 (maps.m + 1), (k - 6 : ℤ) * maps.p_i k := by
    linarith [hEuler]
  have h2' : ((∑ k ∈ Finset.Ico 3 (maps.m + 1), maps.p_i k : ℕ) : ℤ) ≥ 17 := by exact_mod_cast h2
  have hcast : ((∑ k ∈ Finset.Ico 3 (maps.m + 1), maps.p_i k : ℕ) : ℤ)
             = ∑ k ∈ Finset.Ico 3 (maps.m + 1), (maps.p_i k : ℤ) := by push_cast; rfl
  rw [hcast] at h2'
  have hm6 : maps.m ≥ 6 := by
    by_contra hm
    push_neg at hm
    interval_cases maps.m <;> simp_all [Finset.sum_Ico_succ_top] <;> omega
  have hsplit : ∑ k ∈ Finset.Ico 3 (maps.m + 1), (maps.p_i k : ℤ) =
                ∑ k ∈ Finset.Ico 3 7, (maps.p_i k : ℤ) +
                ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) := by
    rw [← Finset.sum_Ico_consecutive (fun k => (maps.p_i k : ℤ))
          (by norm_num : (3 : ℕ) ≤ 7) (by omega : (7 : ℕ) ≤ maps.m + 1)]
  have hsmall : ∑ k ∈ Finset.Ico 3 7, (maps.p_i k : ℤ) =
                (maps.p_i 3 : ℤ) + maps.p_i 4 + maps.p_i 5 + maps.p_i 6 := by
    rw [show (Finset.Ico 3 7 : Finset ℕ) = {3, 4, 5, 6} by decide]
    simp
    ring
  rw [hsmall] at hsplit
  linarith
