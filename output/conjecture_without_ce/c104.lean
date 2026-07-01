-- Complete formalization: c104
-- Theorem: C104
-- Generated: 2026-07-01T08:29:14Z
-- Proved (1): C104

-- Polib.lean
-- Dynamic proof accumulation — auto-managed by FormalizerAgent.
-- Foundational axioms are in Inventory.lean; proved conjectures are appended here.
import Mathlib
import Inventory


-- === C104 (proved) ===

open Finset

theorem C104 (maps : SimplyCon3ConnectedMap 0) (hM : IsMap maps) (h1 : maps.p_i 4 = 0) (h2 : maps.p_i 5 ≤ 2) (h3 : ∑ k ∈ Finset.Ico 3 (maps.m + 1), maps.p_i k ≥ 7) : 2 * maps.p_i 6 ≥ 4 - ∑ k ∈ Finset.Ico 7 (maps.m + 1), maps.p_i k := by
  set S := ∑ k ∈ Finset.Ico 7 (maps.m + 1), maps.p_i k with hSdef
  by_cases hS4 : 4 ≤ S
  · omega
  push_neg at hS4
  have hp_range := p_range maps hM
  have hm6 : maps.m ≥ 6 := by
    by_contra hm_lt
    push_neg at hm_lt
    have hp3_ge : maps.p_i 3 ≥ 5 := by
      have hle : ∑ k ∈ Finset.Ico 3 (maps.m + 1), maps.p_i k ≤
                 maps.p_i 3 + maps.p_i 4 + maps.p_i 5 := by
        have hsub : Finset.Ico 3 (maps.m + 1) ⊆ ({3, 4, 5} : Finset ℕ) := by
          intro x hx
          rw [Finset.mem_Ico] at hx
          simp
          omega
        have hset_sum : ∑ k ∈ ({3, 4, 5} : Finset ℕ), maps.p_i k = 
                        maps.p_i 3 + maps.p_i 4 + maps.p_i 5 := by
          rw [show ({3, 4, 5} : Finset ℕ) = insert 3 (insert 4 {5}) from rfl]
          rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
          ring
        calc ∑ k ∈ Finset.Ico 3 (maps.m + 1), maps.p_i k
            ≤ ∑ k ∈ ({3, 4, 5} : Finset ℕ), maps.p_i k := by
              apply Finset.sum_le_sum_of_subset hsub
          _ = maps.p_i 3 + maps.p_i 4 + maps.p_i 5 := hset_sum
      linarith
    have hjuc := Juc_EulerFormula maps hM
    have hsum_z : ∑ k ∈ Finset.Ico 7 (maps.m + 1), ((k : ℤ) - 6) * (maps.p_i k : ℤ) = 0 := by
      apply Finset.sum_eq_zero
      intro k hk
      rw [Finset.mem_Ico] at hk
      omega
    rw [hsum_z, add_zero, h1] at hjuc
    push_cast at hjuc
    omega
  have hjuc_ineq := Juc_InequalityPart maps hM hm6
  have hSint : (S : ℤ) = ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) := by
    rw [hSdef]; push_cast; rfl
  have hsum_ineq_bd : ∑ k ∈ Finset.Ico 7 (maps.m + 1), (((k : ℤ) + 1) / 2 - 6) * (maps.p_i k : ℤ) 
                     ≥ -2 * (S : ℤ) := by
    rw [hSint, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro k hk
    rw [Finset.mem_Ico] at hk
    have hk7 : (7 : ℤ) ≤ (k : ℤ) := by exact_mod_cast hk.1
    have hp_nn : (0 : ℤ) ≤ (maps.p_i k : ℤ) := by positivity
    have hcoef : ((k : ℤ) + 1) / 2 - 6 ≥ -2 := by omega
    nlinarith
  rw [h1] at hjuc_ineq
  push_cast at hjuc_ineq
  have hp5_z : (maps.p_i 5 : ℤ) ≤ 2 := by exact_mod_cast h2
  have h3p6 : 3 * (maps.p_i 6 : ℤ) ≥ 12 - 3 * (maps.p_i 5 : ℤ) - 2 * (S : ℤ) := by
    linarith
  by_cases hS3 : S = 3
  · have hSge3 : ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) ≥ 3 := by
      rw [← hSint]; exact_mod_cast (by omega : S ≥ 3)
    have hbarnette := Barnette_P6Bound maps hM hm6 hSge3
    have hjuc_euler := Juc_EulerFormula maps hM
    have hsum_euler_bd : ∑ k ∈ Finset.Ico 7 (maps.m + 1), ((k : ℤ) - 6) * (maps.p_i k : ℤ) 
                       ≥ ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) := by
      apply Finset.sum_le_sum
      intro k hk
      rw [Finset.mem_Ico] at hk
      have hk7 : (7 : ℤ) ≤ (k : ℤ) := by exact_mod_cast hk.1
      have hp_nn : (0 : ℤ) ≤ (maps.p_i k : ℤ) := by positivity
      nlinarith
    rw [h1] at hjuc_euler
    push_cast at hjuc_euler hbarnette
    have hSint3 : (S : ℤ) = 3 := by exact_mod_cast hS3
    have hsumeq : ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) = 3 := by linarith
    have h3p3 : 3 * (maps.p_i 3 : ℤ) ≥ 15 - (maps.p_i 5 : ℤ) := by linarith
    have hp3ge5 : (maps.p_i 3 : ℤ) ≥ 5 := by
      have : 3 * (maps.p_i 3 : ℤ) ≥ 13 := by linarith
      omega
    have h2p6_z : 2 * (maps.p_i 6 : ℤ) ≥ 1 := by linarith
    have h2p6 : 2 * maps.p_i 6 ≥ 1 := by exact_mod_cast h2p6_z
    omega
  · have hS2 : S ≤ 2 := by omega
    have hSnat_z : (S : ℤ) ≤ 2 := by exact_mod_cast hS2
    have h2p6_z : 2 * (maps.p_i 6 : ℤ) ≥ 4 - (S : ℤ) := by omega
    have h2p6 : 2 * maps.p_i 6 + S ≥ 4 := by
      have : ((2 * maps.p_i 6 + S : ℕ) : ℤ) ≥ 4 := by push_cast; linarith
      exact_mod_cast this
    omega
