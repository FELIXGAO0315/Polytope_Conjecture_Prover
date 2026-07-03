-- Complete formalization: c124
-- Theorem: C124
-- Generated: 2026-07-01T15:31:50Z
-- Proved (2): C124_SumSplit, C124

-- Polib.lean
-- Dynamic proof accumulation — auto-managed by FormalizerAgent.
-- Foundational axioms are in Inventory.lean; proved conjectures are appended here.
import Mathlib
import Inventory



-- === C124_SumSplit (proved) ===
-- quality_score: 1.000 | sorry_count: 0 | saved_at: 2026-07-01T14:12:46.521257+00:00
private lemma C124_SumSplit (maps : SimplyCon3ConnectedMap 0) (hM : IsMap maps) : (∑ k ∈ Finset.Ico 3 (maps.m + 1), maps.p_i k) = maps.p_i 3 + maps.p_i 4 + maps.p_i 5 + maps.p_i 6 + ∑ k ∈ Finset.Ico 7 (maps.m + 1), maps.p_i k := by
  set N := max 7 (maps.m + 1) with hN
  have hN7 : 7 ≤ N := le_max_left _ _
  have hNm : maps.m + 1 ≤ N := le_max_right _ _
  have hZero : ∀ k ∈ Finset.Ico (maps.m + 1) N, maps.p_i k = 0 := by
    intros k hk
    rw [Finset.mem_Ico] at hk
    exact p_range maps hM k (by omega)
  have hExt_L : ∑ k ∈ Finset.Ico 3 (maps.m + 1), maps.p_i k =
                ∑ k ∈ Finset.Ico 3 N, maps.p_i k := by
    by_cases hm3 : 3 ≤ maps.m + 1
    · rw [← Finset.sum_Ico_consecutive maps.p_i hm3 hNm, Finset.sum_eq_zero hZero, add_zero]
    · push_neg at hm3
      have hE : Finset.Ico 3 (maps.m + 1) = ∅ := Finset.Ico_eq_empty (by omega)
      rw [hE, Finset.sum_empty]
      symm
      apply Finset.sum_eq_zero
      intros k hk
      rw [Finset.mem_Ico] at hk
      exact p_range maps hM k (by omega)
  have hExt_R : ∑ k ∈ Finset.Ico 7 (maps.m + 1), maps.p_i k =
                ∑ k ∈ Finset.Ico 7 N, maps.p_i k := by
    by_cases h : 7 ≤ maps.m + 1
    · rw [← Finset.sum_Ico_consecutive maps.p_i h hNm,
          Finset.sum_eq_zero hZero, add_zero]
    · push_neg at h
      have hE1 : Finset.Ico 7 (maps.m + 1) = ∅ := Finset.Ico_eq_empty (by omega)
      have hE2 : ∀ k ∈ Finset.Ico 7 N, maps.p_i k = 0 := by
        intros k hk
        rw [Finset.mem_Ico] at hk
        exact p_range maps hM k (by omega)
      rw [hE1, Finset.sum_empty, Finset.sum_eq_zero hE2]
  have hLead : ∑ k ∈ Finset.Ico 3 7, maps.p_i k =
               maps.p_i 3 + maps.p_i 4 + maps.p_i 5 + maps.p_i 6 := by
    rw [Finset.sum_Ico_succ_top (show 3 ≤ 6 by omega),
        Finset.sum_Ico_succ_top (show 3 ≤ 5 by omega),
        Finset.sum_Ico_succ_top (show 3 ≤ 4 by omega),
        Finset.sum_Ico_succ_top (show 3 ≤ 3 by omega),
        Finset.Ico_self, Finset.sum_empty]
    ring
  rw [hExt_L, hExt_R, ← Finset.sum_Ico_consecutive maps.p_i (by norm_num : 3 ≤ 7) hN7, hLead]

-- === C124 (proved) ===

theorem C124 (maps : SimplyCon3ConnectedMap 0) (hM : IsMap maps) : 2 * maps.p_i 6 ≤ 2 * (∑ k ∈ Finset.Ico 3 (maps.m + 1), maps.p_i k) - 2 * maps.p_i 4 - 2 * maps.p_i 5 := by
  have h_ext : ∑ k ∈ Finset.Ico 3 (maps.m + 1), maps.p_i k =
               ∑ k ∈ Finset.Ico 3 (max (maps.m + 1) 7), maps.p_i k := by
    apply Finset.sum_subset
    · intro k hk
      simp [Finset.mem_Ico] at hk ⊢
      omega
    · intro k hk hnk
      simp [Finset.mem_Ico] at hk hnk
      exact p_range maps hM k (by omega)
  have hsub : ({4, 5, 6} : Finset ℕ) ⊆ Finset.Ico 3 (max (maps.m + 1) 7) := by
    intro x hx
    simp [Finset.mem_Ico]
    simp at hx
    rcases hx with rfl | rfl | rfl <;> omega
  have hA_sum : (∑ k ∈ ({4, 5, 6} : Finset ℕ), maps.p_i k) =
                maps.p_i 4 + maps.p_i 5 + maps.p_i 6 := by
    rw [show ({4, 5, 6} : Finset ℕ) = insert 4 (insert 5 ({6} : Finset ℕ)) from rfl]
    rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
    ring
  have hAB : maps.p_i 4 + maps.p_i 5 + maps.p_i 6 ≤
             ∑ k ∈ Finset.Ico 3 (maps.m + 1), maps.p_i k := by
    rw [h_ext, ← hA_sum]
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Nat.zero_le _)
  omega
