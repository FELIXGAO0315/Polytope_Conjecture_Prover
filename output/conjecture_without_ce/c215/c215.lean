-- Complete formalization: c215
-- Theorem: C215
-- Generated: 2026-07-05T16:50:45Z
-- Proved (7): C215_DSRelation, C215_FaceDecomp, C215_WeightedGeSum, C215_P3LowerBound, C215_ArithIdentity, C215_SumPkGeBound, C215

-- Polib.lean
-- Dynamic proof accumulation — auto-managed by FormalizerAgent.
-- Foundational axioms are in Inventory.lean; proved conjectures are appended here.
import Mathlib
import Inventory


-- === C215_DSRelation (proved) ===

private lemma C215_DSRelation (maps : SimplyCon3ConnectedMap 0) (hM : IsMap maps) (h1 : maps.p_i 4 = 0) (h2 : maps.p_i 5 = 0) : (3 : ℤ) * maps.p_i 3 = 12 + ∑ k ∈ Finset.Ico 7 (maps.m + 1), ((k : ℤ) - 6) * maps.p_i k := by
  have h := Juc_EulerFormula maps hM
  rw [h1, h2] at h
  simp at h
  linarith [h]

-- === C215_FaceDecomp (proved) ===

open Finset

private lemma C215_FaceDecomp (maps : SimplyCon3ConnectedMap 0) (hM : IsMap maps) (h1 : maps.p_i 4 = 0) (h2 : maps.p_i 5 = 0) : (∑ k ∈ Finset.Ico 3 (maps.m + 1), maps.p_i k : ℤ) = maps.p_i 3 + maps.p_i 6 + ∑ k ∈ Finset.Ico 7 (maps.m + 1), maps.p_i k := by
  have hpr : ∀ k : ℕ, maps.m < k → maps.p_i k = 0 := p_range maps hM
  by_cases hm7 : 7 ≤ maps.m + 1
  · rw [← Finset.sum_Ico_consecutive (fun k => (maps.p_i k : ℤ)) (by omega : 3 ≤ 7) hm7]
    have hI : Finset.Ico 3 7 = ({3, 4, 5, 6} : Finset ℕ) := by decide
    rw [hI]
    rw [show ({3, 4, 5, 6} : Finset ℕ) = insert 3 (insert 4 (insert 5 {6})) from rfl]
    rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
        Finset.sum_insert (by decide), Finset.sum_singleton]
    push_cast [h1, h2]
    ring
  · push_neg at hm7
    have hmle : maps.m ≤ 5 := by omega
    have h7empty : Finset.Ico 7 (maps.m + 1) = ∅ := Finset.Ico_eq_empty_of_le (by omega)
    have hp6 : maps.p_i 6 = 0 := hpr 6 (by omega)
    rw [h7empty]
    simp only [Finset.sum_empty, hp6]
    push_cast
    interval_cases maps.m
    · have h3 : maps.p_i 3 = 0 := hpr 3 (by omega)
      simp [Finset.Ico_eq_empty_of_le (show (0 : ℕ) + 1 ≤ 3 by omega), h3]
    · have h3 : maps.p_i 3 = 0 := hpr 3 (by omega)
      simp [Finset.Ico_eq_empty_of_le (show (1 : ℕ) + 1 ≤ 3 by omega), h3]
    · have h3 : maps.p_i 3 = 0 := hpr 3 (by omega)
      simp [Finset.Ico_eq_empty_of_le (show (2 : ℕ) + 1 ≤ 3 by omega), h3]
    · rw [show (3 : ℕ) + 1 = 4 from rfl]
      rw [show Finset.Ico 3 4 = ({3} : Finset ℕ) from rfl]
      simp
    · rw [show (4 : ℕ) + 1 = 5 from rfl]
      rw [show Finset.Ico 3 5 = ({3, 4} : Finset ℕ) from rfl]
      simp [h1]
    · rw [show (5 : ℕ) + 1 = 6 from rfl]
      rw [show Finset.Ico 3 6 = ({3, 4, 5} : Finset ℕ) from rfl]
      simp [h1, h2]


-- === C201_WeightedSumGeSumPk (proved) ===
-- quality_score: 1.000 | sorry_count: 0 | saved_at: 2026-07-04T07:08:16.833203+00:00
open Finset

private lemma C201_WeightedSumGeSumPk (maps : SimplyCon3ConnectedMap 0) (hM : IsMap maps) : ∑ k ∈ Finset.Ico 7 (maps.m + 1), ((k : ℤ) - 6) * maps.p_i k ≥ ∑ k ∈ Finset.Ico 7 (maps.m + 1), maps.p_i k := by
  push_cast
  apply Finset.sum_le_sum
  intro k hk
  rw [Finset.mem_Ico] at hk
  have hk7 : (7 : ℤ) ≤ k := by exact_mod_cast hk.1
  have hpk : (0 : ℤ) ≤ (maps.p_i k : ℤ) := Int.natCast_nonneg _
  nlinarith [hpk, hk7]

-- === C215_P3LowerBound (proved) ===

private lemma C215_P3LowerBound (maps : SimplyCon3ConnectedMap 0) (hM : IsMap maps) (h1 : maps.p_i 4 = 0) (h2 : maps.p_i 5 = 0) : (maps.p_i 3 : ℤ) ≥ 4 := by
  -- Derive the DS relation directly from Juc_EulerFormula
  have h := Juc_EulerFormula maps hM
  rw [h1, h2] at h
  simp at h
  -- h : 3 * (maps.p_i 3 : ℤ) = 12 + ∑ k ∈ Finset.Ico 7 (maps.m + 1), ((k : ℤ) - 6) * maps.p_i k
  have hsum_nn : (0 : ℤ) ≤ ∑ k ∈ Finset.Ico 7 (maps.m + 1), ((k : ℤ) - 6) * maps.p_i k := by
    apply Finset.sum_nonneg
    intro k hk
    rw [Finset.mem_Ico] at hk
    have hk7 : (7 : ℤ) ≤ (k : ℤ) := by exact_mod_cast hk.1
    have hk6 : (0 : ℤ) ≤ (k : ℤ) - 6 := by linarith
    have hpk : (0 : ℤ) ≤ (maps.p_i k : ℤ) := by exact_mod_cast Nat.zero_le _
    exact mul_nonneg hk6 hpk
  linarith

-- === C215_ArithIdentity (proved) ===

private lemma C215_ArithIdentity (maps : SimplyCon3ConnectedMap 0) (hM : IsMap maps) (h1 : maps.p_i 4 = 0) (h2 : maps.p_i 5 = 0) : (3 : ℤ) * maps.p_i 6 + 2 * ∑ k ∈ Finset.Ico 7 (maps.m + 1), maps.p_i k = 3 * (∑ k ∈ Finset.Ico 3 (maps.m + 1), maps.p_i k) - 12 - ∑ k ∈ Finset.Ico 7 (maps.m + 1), ((k : ℤ) - 6) * maps.p_i k - ∑ k ∈ Finset.Ico 7 (maps.m + 1), maps.p_i k := by
  have hDS : (3 : ℤ) * maps.p_i 3 = 12 + ∑ k ∈ Finset.Ico 7 (maps.m + 1), ((k : ℤ) - 6) * maps.p_i k := by
    have h := Juc_EulerFormula maps hM
    rw [h1, h2] at h
    simp at h
    linarith [h]
  have hFD : (∑ k ∈ Finset.Ico 3 (maps.m + 1), (maps.p_i k : ℤ)) = (maps.p_i 3 : ℤ) + maps.p_i 6 + ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) := by
    have hpr : ∀ k : ℕ, maps.m < k → maps.p_i k = 0 := p_range maps hM
    by_cases hm7 : 7 ≤ maps.m + 1
    · rw [← Finset.sum_Ico_consecutive (fun k => (maps.p_i k : ℤ)) (by omega : 3 ≤ 7) hm7]
      have hI : Finset.Ico 3 7 = ({3, 4, 5, 6} : Finset ℕ) := by decide
      rw [hI]
      rw [show ({3, 4, 5, 6} : Finset ℕ) = insert 3 (insert 4 (insert 5 {6})) from rfl]
      rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
          Finset.sum_insert (by decide), Finset.sum_singleton]
      push_cast [h1, h2]
      ring
    · push_neg at hm7
      have hmle : maps.m ≤ 5 := by omega
      have h7empty : Finset.Ico 7 (maps.m + 1) = ∅ := Finset.Ico_eq_empty_of_le (by omega)
      have hp6 : maps.p_i 6 = 0 := hpr 6 (by omega)
      rw [h7empty]
      simp only [Finset.sum_empty, hp6]
      push_cast
      interval_cases maps.m
      · have h3 : maps.p_i 3 = 0 := hpr 3 (by omega)
        simp [Finset.Ico_eq_empty_of_le (show (0 : ℕ) + 1 ≤ 3 by omega), h3]
      · have h3 : maps.p_i 3 = 0 := hpr 3 (by omega)
        simp [Finset.Ico_eq_empty_of_le (show (1 : ℕ) + 1 ≤ 3 by omega), h3]
      · have h3 : maps.p_i 3 = 0 := hpr 3 (by omega)
        simp [Finset.Ico_eq_empty_of_le (show (2 : ℕ) + 1 ≤ 3 by omega), h3]
      · rw [show (3 : ℕ) + 1 = 4 from rfl]
        rw [show Finset.Ico 3 4 = ({3} : Finset ℕ) from rfl]
        simp
      · rw [show (4 : ℕ) + 1 = 5 from rfl]
        rw [show Finset.Ico 3 5 = ({3, 4} : Finset ℕ) from rfl]
        simp [h1]
      · rw [show (5 : ℕ) + 1 = 6 from rfl]
        rw [show Finset.Ico 3 6 = ({3, 4, 5} : Finset ℕ) from rfl]
        simp [h1, h2]
  push_cast
  push_cast at hFD
  linarith [hDS, hFD]

-- === C215_SumPkGeBound (proved) ===

open Finset

private lemma C215_SumPkGeBound (maps : SimplyCon3ConnectedMap 0) (hM : IsMap maps) (h1 : maps.p_i 4 = 0) (h2 : maps.p_i 5 = 0) (h3 : ∑ k ∈ Finset.Ico 3 (maps.m + 1), maps.p_i k ≥ 7) : 3 * (maps.p_i 6 : ℤ) + 2 * ∑ k ∈ Finset.Ico 7 (maps.m + 1), maps.p_i k ≥ 12 := by
  have hpr := p_range maps hM
  have h3z : (∑ k ∈ Finset.Ico 3 (maps.m + 1), (maps.p_i k : ℤ)) ≥ 7 := by
    have hh : ((∑ k ∈ Finset.Ico 3 (maps.m + 1), maps.p_i k : ℕ) : ℤ) ≥ 7 := by exact_mod_cast h3
    push_cast at hh
    exact hh
  by_cases hm6 : maps.m ≥ 6
  · have hIP := Juc_InequalityPart maps hM hm6
    rw [h1, h2] at hIP
    simp only [Nat.cast_zero, mul_zero, sub_zero] at hIP
    have hkey : ∑ k ∈ Finset.Ico 7 (maps.m + 1), (((k : ℤ) + 1) / 2 - 4) * (maps.p_i k : ℤ) ≥ 0 := by
      apply Finset.sum_nonneg
      intro k hk
      rw [Finset.mem_Ico] at hk
      have hkz : (k : ℤ) ≥ 7 := by exact_mod_cast hk.1
      have hcoef : (((k : ℤ) + 1) / 2 - 4) ≥ 0 := by omega
      have hpk : (maps.p_i k : ℤ) ≥ 0 := Int.ofNat_nonneg _
      exact mul_nonneg hcoef hpk
    have hsplit : ∑ k ∈ Finset.Ico 7 (maps.m + 1), (((k : ℤ) + 1) / 2 - 4) * (maps.p_i k : ℤ)
                = ∑ k ∈ Finset.Ico 7 (maps.m + 1), (((k : ℤ) + 1) / 2 - 6) * (maps.p_i k : ℤ)
                  + 2 * ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intros
      ring
    push_cast
    linarith
  · push_neg at hm6
    exfalso
    have hm_le : maps.m + 1 ≤ 6 := by omega
    have h7empty : Finset.Ico 7 (maps.m + 1) = ∅ := Finset.Ico_eq_empty_of_le (by omega)
    have hEF := Juc_EulerFormula maps hM
    rw [h1, h2, h7empty] at hEF
    simp at hEF
    have hp3 : (maps.p_i 3 : ℤ) = 4 := by linarith
    have hsubset : Finset.Ico 3 (maps.m + 1) ⊆ Finset.Ico 3 6 :=
      Finset.Ico_subset_Ico_right hm_le
    have hT_le : (∑ k ∈ Finset.Ico 3 (maps.m + 1), (maps.p_i k : ℤ)) ≤
                 ∑ k ∈ Finset.Ico 3 6, (maps.p_i k : ℤ) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
      intros; exact Int.ofNat_nonneg _
    have hSum6 : (∑ k ∈ Finset.Ico 3 6, (maps.p_i k : ℤ)) = 4 := by
      rw [show Finset.Ico 3 6 = ({3, 4, 5} : Finset ℕ) from by decide]
      rw [show ({3, 4, 5} : Finset ℕ) = insert 3 (insert 4 {5}) from rfl]
      rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
      push_cast [h1, h2]
      linarith
    linarith

-- === C215 (proved) ===

theorem C215 (maps : SimplyCon3ConnectedMap 0) (hM : IsMap maps) (h1 : maps.p_i 4 = 0) (h2 : maps.p_i 5 = 0) (h3 : ∑ k ∈ Finset.Ico 3 (maps.m + 1), maps.p_i k ≥ 7) : 3 * maps.p_i 6 + 2 * ∑ k ∈ Finset.Ico 7 (maps.m + 1), maps.p_i k ≥ 12 := by
  have h1z : (maps.p_i 4 : ℤ) = 0 := by exact_mod_cast h1
  have h2z : (maps.p_i 5 : ℤ) = 0 := by exact_mod_cast h2
  by_cases hm : maps.m ≥ 6
  · -- main case m ≥ 6
    have hIneq := Juc_InequalityPart maps hM hm
    rw [h1z, h2z] at hIneq
    have hSum : (0 : ℤ) ≤ ∑ k ∈ Finset.Ico 7 (maps.m + 1), (((k : ℤ) + 1) / 2 - 4) * maps.p_i k := by
      apply Finset.sum_nonneg
      intro k hk
      rw [Finset.mem_Ico] at hk
      have hk7 : (k : ℤ) ≥ 7 := by exact_mod_cast hk.1
      have hcoef : (0 : ℤ) ≤ ((k : ℤ) + 1) / 2 - 4 := by omega
      have hpk : (0 : ℤ) ≤ (maps.p_i k : ℤ) := by exact_mod_cast Nat.zero_le _
      exact mul_nonneg hcoef hpk
    have hgoal_z : (3 : ℤ) * maps.p_i 6 + 2 * ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) ≥ 12 := by
      have h4 : ∑ k ∈ Finset.Ico 7 (maps.m + 1), (((k : ℤ) + 1) / 2 - 4) * maps.p_i k
              = ∑ k ∈ Finset.Ico 7 (maps.m + 1), (((k : ℤ) + 1) / 2 - 6) * maps.p_i k
                + 2 * ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) := by
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intros k _
        ring
      linarith [hSum, hIneq, h4]
    have : (3 * maps.p_i 6 + 2 * ∑ k ∈ Finset.Ico 7 (maps.m + 1), maps.p_i k : ℤ) ≥ 12 := by
      push_cast
      linarith [hgoal_z]
    exact_mod_cast this
  · -- degenerate case m < 6: derive contradiction
    push_neg at hm
    have hE := Juc_EulerFormula maps hM
    rw [h1z, h2z] at hE
    have hEmpty : Finset.Ico 7 (maps.m + 1) = ∅ := by
      apply Finset.Ico_eq_empty
      omega
    rw [hEmpty, Finset.sum_empty] at hE
    have hp3 : (maps.p_i 3 : ℤ) = 4 := by linarith
    have hSum_le : ∑ k ∈ Finset.Ico 3 (maps.m + 1), (maps.p_i k : ℤ) ≤ 4 := by
      have hSub : Finset.Ico 3 (maps.m + 1) ⊆ Finset.Ico 3 6 := by
        apply Finset.Ico_subset_Ico_right
        omega
      calc ∑ k ∈ Finset.Ico 3 (maps.m + 1), (maps.p_i k : ℤ)
          ≤ ∑ k ∈ Finset.Ico 3 6, (maps.p_i k : ℤ) := by
            apply Finset.sum_le_sum_of_subset_of_nonneg hSub
            intros
            exact_mod_cast Nat.zero_le _
        _ = (maps.p_i 3 : ℤ) + (maps.p_i 4 : ℤ) + (maps.p_i 5 : ℤ) := by
            have : Finset.Ico 3 6 = {3, 4, 5} := by decide
            rw [this]
            simp
            ring
        _ = 4 := by rw [hp3, h1z, h2z]; ring
    have h3z : (∑ k ∈ Finset.Ico 3 (maps.m + 1), (maps.p_i k : ℤ)) ≥ 7 := by
      exact_mod_cast h3
    linarith
