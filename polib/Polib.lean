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

-- === C104_DehnSommervilleLowerDegree (proved) ===
-- quality_score: 1.000 | sorry_count: 0 | saved_at: 2026-06-28T11:59:16.183036+00:00
/-- From the Dehn–Sommerville relation with p_4 = 0, derive the lower-degree face bound.
    When no quadrilateral faces are present, the edge-count equation specializes to:
    3·p₃ + p₅ = 12 + ∑_{k≥7} (k − 6)·p_k -/
lemma C104_DehnSommervilleLowerDegree
    (maps : SimplyCon3ConnectedMap 0)
    (hM : IsMap maps)
    (h_p4 : maps.p_i 4 = 0) :
    (3 : ℤ) * (maps.p_i 3 : ℤ) + (maps.p_i 5 : ℤ) =
    12 + ∑ k ∈ Finset.Ico 7 (maps.m + 1), ((k : ℤ) - 6) * (maps.p_i k : ℤ) := by
  have h := P6EdgeCountEquation maps hM
  push_cast at *
  omega

-- === C104_P3LowerBound (proved) ===
-- quality_score: 1.000 | sorry_count: 0 | saved_at: 2026-06-28T15:11:58.280076+00:00
lemma C104_P3LowerBound (maps : SimplyCon3ConnectedMap 0) (hM : IsMap maps)
    (h_p4 : maps.p_i 4 = 0) (h_p5 : maps.p_i 5 ≤ 2) : 
    3 * (maps.p_i 3 : ℤ) ≥ 10 + ∑ k ∈ Finset.Ico 7 (maps.m + 1), (((k : ℤ) - 6) * (maps.p_i k : ℤ)) := by
  have h := Juc_EulerFormula maps hM
  linarith [h_p4, h_p5]

-- === C104_CaseLargeSum (proved) ===
-- quality_score: 1.000 | sorry_count: 0 | saved_at: 2026-06-29T07:51:35.509620+00:00
lemma C104_CaseLargeSum (maps : SimplyCon3ConnectedMap 0) (hM : IsMap maps)
    (hS : ∑ k ∈ Finset.Ico 7 (maps.m + 1), maps.p_i k > 2) :
    (maps.p_i 6 : ℤ) + 2 * (∑ k ∈ Finset.Ico 7 (maps.m + 1), maps.p_i k : ℤ) > 4 := by
  have h_S : (∑ k ∈ Finset.Ico 7 (maps.m + 1), maps.p_i k : ℤ) > 2 := by exact_mod_cast hS
  have h_p6 : (maps.p_i 6 : ℤ) ≥ 0 := Nat.cast_nonneg _
  linarith

-- === C104_DehnSommerville_Application (proved) ===
-- quality_score: 1.000 | sorry_count: 0 | saved_at: 2026-06-29T14:22:47.993657+00:00
private lemma C104_DehnSommerville_Application (maps : SimplyCon3ConnectedMap 0) (hM : IsMap maps) (h_p4 : maps.p_i 4 = 0) (h_p5 : maps.p_i 5 ≤ 2) : (3 : ℤ) * maps.p_i 3 ≥ 10 + ∑ k ∈ Finset.Ico 7 (maps.m + 1), (((k : ℤ) - 6) * maps.p_i k) := by
  have h1 := P6EdgeCountEquation maps hM
  have he := euler_formula maps hM
  have hh := handshake maps hM
  push_cast
  linarith

-- === C104_CaseSmallSum (proved) ===
-- quality_score: 1.000 | sorry_count: 0 | saved_at: 2026-07-01T06:59:11.495297+00:00
private lemma C104_CaseSmallSum (maps : SimplyCon3ConnectedMap 0) (hM : IsMap maps) (h1 : maps.p_i 4 = 0) (h2 : maps.p_i 5 ≤ 2) (h3 : ∑ k ∈ Finset.Ico 3 (maps.m + 1), maps.p_i k ≥ 7) (hS : ∑ k ∈ Finset.Ico 7 (maps.m + 1), maps.p_i k ≤ 2) : 2 * maps.p_i 6 ≥ 4 - ∑ k ∈ Finset.Ico 7 (maps.m + 1), maps.p_i k := by
  set S := ∑ k ∈ Finset.Ico 7 (maps.m + 1), maps.p_i k with hSdef
  set SZ : ℤ := ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) with hSZdef
  have hCastS : (S : ℤ) = SZ := by
    rw [hSZdef, hSdef]; push_cast; rfl
  have hSZnn : SZ ≥ 0 := by
    apply Finset.sum_nonneg; intros; exact Int.ofNat_nonneg _
  -- Step 1: m ≥ 6
  have hm : maps.m ≥ 6 := by
    by_contra hlt
    push_neg at hlt
    have hIco_empty : Finset.Ico 7 (maps.m + 1) = ∅ :=
      Finset.Ico_eq_empty (by omega)
    have hEuler := Juc_EulerFormula maps hM
    rw [hIco_empty, Finset.sum_empty] at hEuler
    rw [h1] at hEuler
    have hp3_le : maps.p_i 3 ≤ 4 := by
      have h1' : (3 * maps.p_i 3 : ℤ) ≤ 12 := by
        have hp5nn : (maps.p_i 5 : ℤ) ≥ 0 := Int.ofNat_nonneg _
        push_cast at hEuler
        linarith
      have h2' : (maps.p_i 3 : ℤ) ≤ 4 := by linarith
      exact_mod_cast h2'
    have hSub : Finset.Ico 3 (maps.m + 1) ⊆ Finset.Ico 3 6 :=
      Finset.Ico_subset_Ico_right (by omega)
    have hSumBound : ∑ k ∈ Finset.Ico 3 (maps.m + 1), maps.p_i k ≤
                     ∑ k ∈ Finset.Ico 3 6, maps.p_i k :=
      Finset.sum_le_sum_of_subset hSub
    have hIco36 : (Finset.Ico 3 6 : Finset ℕ) = {3, 4, 5} := by decide
    rw [hIco36] at hSumBound
    simp at hSumBound
    omega
  -- Step 2: 3 * p_6 ≥ 6 - 2 * SZ
  have hIneq := Juc_InequalityPart maps hM hm
  rw [h1] at hIneq
  push_cast at hIneq
  have hSumLB : ∑ k ∈ Finset.Ico 7 (maps.m + 1), (((k : ℤ) + 1) / 2 - 6) * (maps.p_i k : ℤ) ≥
                -2 * SZ := by
    have hle : ∑ k ∈ Finset.Ico 7 (maps.m + 1), (-2 : ℤ) * (maps.p_i k : ℤ) ≤
           ∑ k ∈ Finset.Ico 7 (maps.m + 1), (((k : ℤ) + 1) / 2 - 6) * (maps.p_i k : ℤ) := by
      apply Finset.sum_le_sum
      intro k hk
      rw [Finset.mem_Ico] at hk
      have hk7 : k ≥ 7 := hk.1
      have hkZ : (k : ℤ) ≥ 7 := by exact_mod_cast hk7
      have hdiv : ((k : ℤ) + 1) / 2 ≥ 4 := by omega
      have hcoeff : ((k : ℤ) + 1) / 2 - 6 ≥ -2 := by linarith
      have hp : (maps.p_i k : ℤ) ≥ 0 := Int.ofNat_nonneg _
      nlinarith
    have hEq : ∑ k ∈ Finset.Ico 7 (maps.m + 1), (-2 : ℤ) * (maps.p_i k : ℤ) =
               (-2) * SZ := by
      rw [hSZdef, ← Finset.mul_sum]
    linarith
  have hp5 : (maps.p_i 5 : ℤ) ≤ 2 := by exact_mod_cast h2
  have hp6bound : 3 * (maps.p_i 6 : ℤ) ≥ 6 - 2 * SZ := by linarith
  have hSZle : SZ ≤ 2 := by rw [← hCastS]; exact_mod_cast hS
  have h2p6 : 2 * (maps.p_i 6 : ℤ) ≥ 4 - SZ := by
    by_contra hlt
    push_neg at hlt
    have hstep1 : 2 * (maps.p_i 6 : ℤ) ≤ 3 - SZ := by linarith
    have hstep2 : (6 : ℤ) * (maps.p_i 6 : ℤ) ≤ 9 - 3 * SZ := by linarith
    have hstep3 : (6 : ℤ) * (maps.p_i 6 : ℤ) ≥ 12 - 4 * SZ := by linarith
    linarith
  have h_int_conv : (2 * maps.p_i 6 : ℤ) + (S : ℤ) ≥ 4 := by
    rw [hCastS]; push_cast; linarith
  have hFinal : 2 * maps.p_i 6 + S ≥ 4 := by exact_mod_cast h_int_conv
  omega

-- === C104 (proved) ===
-- quality_score: 1.000 | sorry_count: 0 | saved_at: 2026-07-01T08:28:57.825075+00:00
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

-- === C123_RHSSimplification (proved) ===
-- quality_score: 1.000 | sorry_count: 0 | saved_at: 2026-07-01T09:20:54.487193+00:00
lemma C123_RHSSimplification (F p6 : ℕ) : (4 * F - 6 - 4 * p6) - 2 * (2 * F - 4) - 2 = 0 := by
  omega

-- === C123_GoalReducesToZero (proved) ===
-- quality_score: 1.000 | sorry_count: 0 | saved_at: 2026-07-01T09:25:31.383076+00:00
lemma C123_GoalReducesToZero (maps : SimplyCon3ConnectedMap 0) (hM : IsMap maps) : (4 * (∑ k ∈ Finset.Ico 3 (maps.m + 1), maps.p_i k) - 6 - 4 * maps.p_i 6) - 2 * (2 * (∑ k ∈ Finset.Ico 3 (maps.m + 1), maps.p_i k) - 4) - 2 = 0 := by
  exact C123_RHSSimplification (∑ k ∈ Finset.Ico 3 (maps.m + 1), maps.p_i k) (maps.p_i 6)

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
-- quality_score: 1.000 | sorry_count: 0 | saved_at: 2026-07-01T15:31:32.241411+00:00
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

-- === C193_DehnSommervilleP3Zero (proved) ===
-- quality_score: 1.000 | sorry_count: 0 | saved_at: 2026-07-03T09:54:14.764959+00:00
private lemma C193_DehnSommervilleP3Zero (maps : SimplyCon3ConnectedMap 0) (hM : IsMap maps) (h1 : maps.p_i 3 = 0) : (2 : ℤ) * maps.p_i 4 + maps.p_i 5 = 12 + ∑ k ∈ Finset.Ico 7 (maps.m + 1), (k - 6 : ℤ) * maps.p_i k := by
  have h := Juc_EulerFormula maps hM
  rw [h1] at h
  push_cast at h
  linarith [h]

-- === C193_WeightedSumBound (proved) ===
-- quality_score: 1.000 | sorry_count: 0 | saved_at: 2026-07-03T09:54:35.271020+00:00
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
-- quality_score: 1.000 | sorry_count: 0 | saved_at: 2026-07-03T09:55:30.841976+00:00
private lemma C193_CaseLargeS (maps : SimplyCon3ConnectedMap 0) (hM : IsMap maps) (hS : ∑ k ∈ Finset.Ico 7 (maps.m + 1), maps.p_i k ≥ 2) : (maps.p_i 6 : ℤ) ≥ -2 * (∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ)) + 4 := by
  have hS' : (∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ)) ≥ 2 := by
    have h := hS
    have := (Nat.cast_le (α := ℤ)).mpr h
    push_cast at this
    exact this
  have hp6 : (maps.p_i 6 : ℤ) ≥ 0 := Int.natCast_nonneg _
  linarith

-- === C193_P6LowerBound (proved) ===
-- quality_score: 1.000 | sorry_count: 0 | saved_at: 2026-07-03T10:00:37.059153+00:00
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

-- === C195_WeightedSumBound (proved) ===
-- quality_score: 1.000 | sorry_count: 0 | saved_at: 2026-07-03T15:36:37.404477+00:00
private lemma C195_WeightedSumBound (maps : SimplyCon3ConnectedMap 0) (hM : IsMap maps) : ∑ k ∈ Finset.Ico 7 (maps.m + 1), ((k : ℤ) - 6) * maps.p_i k ≥ ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) := by
  apply Finset.sum_le_sum
  intro k hk
  rw [Finset.mem_Ico] at hk
  have hk7 : (7 : ℤ) ≤ (k : ℤ) := by exact_mod_cast hk.1
  have hp : (0 : ℤ) ≤ (maps.p_i k : ℤ) := Int.natCast_nonneg _
  nlinarith [hk7, hp]

-- === C195_FaceCountP5Zero (proved) ===
-- quality_score: 1.000 | sorry_count: 0 | saved_at: 2026-07-03T15:37:52.343147+00:00
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

-- === C201_DSEquality (proved) ===
-- quality_score: 1.000 | sorry_count: 0 | saved_at: 2026-07-04T06:15:38.940078+00:00
private lemma C201_DSEquality (maps : SimplyCon3ConnectedMap 0) (hM : IsMap maps) (h1 : maps.p_i 4 = 0) (h2 : maps.p_i 5 = 0) : (3 : ℤ) * maps.p_i 3 = 12 + ∑ k ∈ Finset.Ico 7 (maps.m + 1), ((k : ℤ) - 6) * maps.p_i k := by
  have h := Juc_EulerFormula maps hM
  have e1 : (maps.p_i 4 : ℤ) = 0 := by exact_mod_cast h1
  have e2 : (maps.p_i 5 : ℤ) = 0 := by exact_mod_cast h2
  rw [e1, e2] at h
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

-- === C201_FaceCountSplit (proved) ===
-- quality_score: 1.000 | sorry_count: 0 | saved_at: 2026-07-04T07:07:52.404708+00:00
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
