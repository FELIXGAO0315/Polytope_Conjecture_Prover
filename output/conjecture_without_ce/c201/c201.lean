-- Complete formalization: c201
-- Theorem: C201
-- Generated: 2026-07-04T07:09:08Z
-- Proved (7): C201_DSEquality, C201_WeightedSumGeSumPk, C201_FaceCountSplit, C201_CaseLargeS, C201_P3LowerBound, C201_CaseS1, C201

-- Polib.lean
-- Dynamic proof accumulation — auto-managed by FormalizerAgent.
-- Foundational axioms are in Inventory.lean; proved conjectures are appended here.
import Mathlib
import Inventory



-- === C201_DSEquality (proved) ===
-- quality_score: 1.000 | sorry_count: 0 | saved_at: 2026-07-04T06:15:38.940078+00:00
private lemma C201_DSEquality (maps : SimplyCon3ConnectedMap 0) (hM : IsMap maps) (h1 : maps.p_i 4 = 0) (h2 : maps.p_i 5 = 0) : (3 : ℤ) * maps.p_i 3 = 12 + ∑ k ∈ Finset.Ico 7 (maps.m + 1), ((k : ℤ) - 6) * maps.p_i k := by
  have h := Juc_EulerFormula maps hM
  have e1 : (maps.p_i 4 : ℤ) = 0 := by exact_mod_cast h1
  have e2 : (maps.p_i 5 : ℤ) = 0 := by exact_mod_cast h2
  rw [e1, e2] at h
  linarith

-- === C201_WeightedSumGeSumPk (proved) ===

open Finset

private lemma C201_WeightedSumGeSumPk (maps : SimplyCon3ConnectedMap 0) (hM : IsMap maps) : ∑ k ∈ Finset.Ico 7 (maps.m + 1), ((k : ℤ) - 6) * maps.p_i k ≥ ∑ k ∈ Finset.Ico 7 (maps.m + 1), maps.p_i k := by
  push_cast
  apply Finset.sum_le_sum
  intro k hk
  rw [Finset.mem_Ico] at hk
  have hk7 : (7 : ℤ) ≤ k := by exact_mod_cast hk.1
  have hpk : (0 : ℤ) ≤ (maps.p_i k : ℤ) := Int.natCast_nonneg _
  nlinarith [hpk, hk7]

-- === C201_FaceCountSplit (proved) ===

private lemma C201_FaceCountSplit (maps : SimplyCon3ConnectedMap 0) (hM : IsMap maps) (h1 : maps.p_i 4 = 0) (h2 : maps.p_i 5 = 0) : (∑ k ∈ Finset.Ico 3 (maps.m + 1), maps.p_i k : ℤ) = maps.p_i 3 + maps.p_i 6 + ∑ k ∈ Finset.Ico 7 (maps.m + 1), maps.p_i k := by
  suffices h : ∑ k ∈ Finset.Ico 3 (maps.m + 1), maps.p_i k
             = maps.p_i 3 + maps.p_i 6 + ∑ k ∈ Finset.Ico 7 (maps.m + 1), maps.p_i k by
    exact_mod_cast h
  set N := max (maps.m + 1) 7 with hNdef
  have hN1 : maps.m + 1 ≤ N := le_max_left _ _
  have hN2 : 7 ≤ N := le_max_right _ _
  have hpad : ∀ k, maps.m + 1 ≤ k → maps.p_i k = 0 := fun k hk =>
    p_range maps hM k (by omega)
  have hExtL : ∑ k ∈ Finset.Ico 3 (maps.m + 1), maps.p_i k
             = ∑ k ∈ Finset.Ico 3 N, maps.p_i k := by
    apply Finset.sum_subset (Finset.Ico_subset_Ico le_rfl hN1)
    intros k hk1 hk2
    rw [Finset.mem_Ico] at hk1 hk2
    exact hpad k (by omega)
  have hExtR : ∑ k ∈ Finset.Ico 7 (maps.m + 1), maps.p_i k
             = ∑ k ∈ Finset.Ico 7 N, maps.p_i k := by
    apply Finset.sum_subset (Finset.Ico_subset_Ico le_rfl hN1)
    intros k hk1 hk2
    rw [Finset.mem_Ico] at hk1 hk2
    exact hpad k (by omega)
  rw [hExtL, hExtR]
  rw [← Finset.sum_Ico_consecutive (fun k => maps.p_i k) (by norm_num : (3:ℕ) ≤ 7) hN2]
  have h37 : ∑ k ∈ Finset.Ico 3 7, maps.p_i k
           = maps.p_i 3 + maps.p_i 4 + maps.p_i 5 + maps.p_i 6 := by
    rw [show (Finset.Ico 3 7 : Finset ℕ) = {3, 4, 5, 6} from by decide]
    simp
    ring
  omega


-- === C193_CaseLargeS (proved) ===
-- quality_score: 1.000 | sorry_count: 0 | saved_at: 2026-07-03T09:55:30.841976+00:00
private lemma C193_CaseLargeS (maps : SimplyCon3ConnectedMap 0) (hM : IsMap maps) (hS : ∑ k ∈ Finset.Ico 7 (maps.m + 1), maps.p_i k ≥ 2) : (maps.p_i 6 : ℤ) ≥ -2 * (∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ)) + 4 := by
  have hS' : (∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ)) ≥ 2 := by
    have h := hS
    have := (Nat.cast_le (α := ℤ)).mpr h
    push_cast at this
    exact this
  have hp6 : (maps.p_i 6 : ℤ) ≥ 0 := Int.natCast_nonneg _
  linarith


-- === C201_P3LowerBound (proved) ===
-- quality_score: 1.000 | sorry_count: 0 | saved_at: 2026-07-04T06:18:47.786714+00:00
private lemma C201_P3LowerBound (maps : SimplyCon3ConnectedMap 0) (hM : IsMap maps) (h1 : maps.p_i 4 = 0) (h2 : maps.p_i 5 = 0) (h3 : ∑ k ∈ Finset.Ico 7 (maps.m + 1), maps.p_i k ≥ 1) : (3 : ℤ) * maps.p_i 3 ≥ 12 + ∑ k ∈ Finset.Ico 7 (maps.m + 1), maps.p_i k := by
  have hEuler := Juc_EulerFormula maps hM
  have hSum : ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) ≤
              ∑ k ∈ Finset.Ico 7 (maps.m + 1), ((k : ℤ) - 6) * maps.p_i k := by
    apply Finset.sum_le_sum
    intro k hk
    rw [Finset.mem_Ico] at hk
    have hk7 : (7 : ℤ) ≤ k := by exact_mod_cast hk.1
    have hp : (0 : ℤ) ≤ (maps.p_i k : ℤ) := Int.natCast_nonneg _
    nlinarith
  have h1' : (maps.p_i 4 : ℤ) = 0 := by exact_mod_cast h1
  have h2' : (maps.p_i 5 : ℤ) = 0 := by exact_mod_cast h2
  push_cast
  linarith


-- === C201_CaseS1 (proved) ===
-- quality_score: 1.000 | sorry_count: 0 | saved_at: 2026-07-04T06:19:40.955614+00:00
private lemma C201_CaseS1 (maps : SimplyCon3ConnectedMap 0) (hM : IsMap maps) (h1 : maps.p_i 4 = 0) (h2 : maps.p_i 5 = 0) (hS : ∑ k ∈ Finset.Ico 7 (maps.m + 1), maps.p_i k = 1) : (maps.p_i 6 : ℤ) ≥ 1 := by
  -- If m ≤ 6, the sum is empty and cannot be 1.
  have hm : maps.m ≥ 6 := by
    by_contra h
    push_neg at h
    have hempty : Finset.Ico 7 (maps.m + 1) = ∅ := by
      apply Finset.Ico_eq_empty
      omega
    rw [hempty, Finset.sum_empty] at hS
    exact absurd hS (by decide)
  have hIneq := P6InequalityPart maps hM hm
  have hS_int : (∑ k ∈ Finset.Ico 7 (maps.m + 1), ((maps.p_i k : ℤ))) = 1 := by
    exact_mod_cast hS
  have hp4 : (maps.p_i 4 : ℤ) = 0 := by exact_mod_cast h1
  have hp5 : (maps.p_i 5 : ℤ) = 0 := by exact_mod_cast h2
  -- Bound: ∑ ((k+1)/2 - 6) * p_k ≥ -2 * ∑ p_k = -2
  have hSum_bound :
      -2 * (∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ)) ≤
      ∑ k ∈ Finset.Ico 7 (maps.m + 1), (((k : ℤ) + 1) / 2 - 6) * (maps.p_i k : ℤ) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intros k hk
    rw [Finset.mem_Ico] at hk
    have hk7 : (7 : ℤ) ≤ (k : ℤ) := by exact_mod_cast hk.1
    have hcoef : ((k : ℤ) + 1) / 2 - 6 ≥ -2 := by omega
    have hpk : (0 : ℤ) ≤ (maps.p_i k : ℤ) := Int.ofNat_nonneg _
    nlinarith
  linarith


-- === C201 (proved) ===
-- quality_score: 1.000 | sorry_count: 0 | saved_at: 2026-07-04T06:29:26.277763+00:00
private lemma C201_CaseS1_helper (maps : SimplyCon3ConnectedMap 0) (hM : IsMap maps) (h1 : maps.p_i 4 = 0) (h2 : maps.p_i 5 = 0) (hS : ∑ k ∈ Finset.Ico 7 (maps.m + 1), maps.p_i k = 1) : (maps.p_i 6 : ℤ) ≥ 1 := by
  have hm : maps.m ≥ 6 := by
    by_contra h
    push_neg at h
    have hempty : Finset.Ico 7 (maps.m + 1) = ∅ := by
      apply Finset.Ico_eq_empty
      omega
    rw [hempty, Finset.sum_empty] at hS
    exact absurd hS (by decide)
  have hIneq := P6InequalityPart maps hM hm
  have hS_int : (∑ k ∈ Finset.Ico 7 (maps.m + 1), ((maps.p_i k : ℤ))) = 1 := by
    exact_mod_cast hS
  have hp4 : (maps.p_i 4 : ℤ) = 0 := by exact_mod_cast h1
  have hp5 : (maps.p_i 5 : ℤ) = 0 := by exact_mod_cast h2
  have hSum_bound :
      -2 * (∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ)) ≤
      ∑ k ∈ Finset.Ico 7 (maps.m + 1), (((k : ℤ) + 1) / 2 - 6) * (maps.p_i k : ℤ) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intros k hk
    rw [Finset.mem_Ico] at hk
    have hk7 : (7 : ℤ) ≤ (k : ℤ) := by exact_mod_cast hk.1
    have hcoef : ((k : ℤ) + 1) / 2 - 6 ≥ -2 := by omega
    have hpk : (0 : ℤ) ≤ (maps.p_i k : ℤ) := Int.ofNat_nonneg _
    nlinarith
  linarith

theorem C201 (maps : SimplyCon3ConnectedMap 0) (hM : IsMap maps) (h1 : maps.p_i 4 = 0) (h2 : maps.p_i 5 = 0) (h3 : ∑ k ∈ Finset.Ico 7 (maps.m + 1), maps.p_i k ≥ 1) : (maps.p_i 6 : ℤ) ≥ -1 * (∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ)) + 2 := by
  by_cases hS : (∑ k ∈ Finset.Ico 7 (maps.m + 1), maps.p_i k) ≥ 2
  · have h0 : (0 : ℤ) ≤ (maps.p_i 6 : ℤ) := Int.ofNat_nonneg _
    have hS' : (2 : ℤ) ≤ ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) := by
      exact_mod_cast hS
    linarith
  · push_neg at hS
    have hS1 : (∑ k ∈ Finset.Ico 7 (maps.m + 1), maps.p_i k) = 1 := by omega
    have hcase := C201_CaseS1_helper maps hM h1 h2 hS1
    have hSZ : ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) = 1 := by
      exact_mod_cast hS1
    linarith
