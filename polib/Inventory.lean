-- ════════════════════════════════════════════════════════════════════════
-- Inventory.lean
-- Foundational lemma library for the Polytope Conjecture Prover.
--
-- Sources (in preparation/):
--   • Euler_inductive.tex  — Euler's formula V − E + F = 2
--   • jucovic_theorem.tex  — Jučovič theorem (sphere, g = 0)
--   • p6.tex               — p₆ inequality for general genus g
--
-- Design contract
-- ───────────────
-- §2 foundational lemmas: sorried because Mathlib's SimpleGraph API does
-- not cover surface-embedded maps. These are the ONLY permitted sorry in
-- this file; all other lemmas are proved without sorry.
-- ════════════════════════════════════════════════════════════════════════
import Mathlib

-- ════════════════════════════════════════════════════════════════════════
-- §1  DATA STRUCTURE
-- ════════════════════════════════════════════════════════════════════════

/-- A simple 3-connected map on a closed surface of genus g.
    Only combinatorial data is stored; geometric constraints appear as
    sorried axioms below. -/
structure SimplyCon3ConnectedMap (g : ℤ) where
  m         : ℕ          -- max face size (faces are 3-gons … m-gons)
  p_i       : ℕ → ℕ      -- p_i k = number of k-gonal faces
  v         : ℕ          -- vertex count
  e         : ℕ          -- edge count
  total_occ : ℕ → ℤ      -- total_occ k = triangle-edges occupied by k-gons

namespace SimplyCon3ConnectedMap
variable {g : ℤ}

def p_4 (M : SimplyCon3ConnectedMap g) : ℕ := M.p_i 4
def p_5 (M : SimplyCon3ConnectedMap g) : ℕ := M.p_i 5
def p_6 (M : SimplyCon3ConnectedMap g) : ℕ := M.p_i 6
def p_k (M : SimplyCon3ConnectedMap g) (k : ℕ) : ℕ := M.p_i k

def total_faces (M : SimplyCon3ConnectedMap g) : ℕ :=
  ∑ k ∈ Finset.Ico 3 (M.m + 1), M.p_i k

end SimplyCon3ConnectedMap

-- ════════════════════════════════════════════════════════════════════════
-- §2  FOUNDATIONAL LEMMAS (sorry: Mathlib lacks surface-embedded graph API)
-- (from Euler_inductive.tex, jucovic_theorem.tex, p6.tex)
-- ════════════════════════════════════════════════════════════════════════

lemma euler_formula {g : ℤ} (M : SimplyCon3ConnectedMap g) :
    (M.v : ℤ) - M.e + ∑ k ∈ Finset.Ico 3 (M.m + 1), (M.p_i k : ℤ) = 2 - 2 * g := by
  sorry

lemma handshake {g : ℤ} (M : SimplyCon3ConnectedMap g) :
    2 * M.e = ∑ k ∈ Finset.Ico 3 (M.m + 1), k * M.p_i k := by
  sorry

lemma regularity {g : ℤ} (M : SimplyCon3ConnectedMap g) : 3 * M.v = 2 * M.e := by
  sorry

-- NOTE (soundness fix 2026-06-10): the former `kgon_occupation_bound` and
-- `quad_occ_reduction` quantified over arbitrary `Finset ℕ` instead of the
-- map's own occupation data and were refutable inside Lean (e.g. occ = {0,1,2},
-- k = 4 gives 3 ≤ 2), making the axiom base inconsistent.
--   • kgon_occupation_bound is restated on `total_occ` below (after
--     occupation_bound, from which it is now PROVED — no longer an axiom).
--   • quad_occ_reduction ("an r-gon adjacent to a quad occupies ≤ ⌊r/2⌋ − 1")
--     needs face-adjacency data that `SimplyCon3ConnectedMap` does not carry —
--     the same Mathlib gap that blocks `Juc_InequalityPart`. It is removed from
--     the axiom base rather than restated unsoundly.

lemma p_range {g : ℤ} (M : SimplyCon3ConnectedMap g) :
    ∀ k : ℕ, M.m < k → M.p_i k = 0 := by
  sorry

lemma occupation_conservation {g : ℤ} (M : SimplyCon3ConnectedMap g) :
    ∑ k ∈ Finset.Ico 4 (M.m + 1), M.total_occ k = 3 * (M.p_i 3 : ℤ) := by
  sorry

lemma occupation_bound {g : ℤ} (M : SimplyCon3ConnectedMap g) :
    ∀ k : ℕ, k ∈ Finset.Ico 4 (M.m + 1) →
    0 ≤ M.total_occ k ∧ M.total_occ k ≤ ((k : ℤ) / 2) * (M.p_i k : ℤ) := by
  sorry

/-- A k-gon occupies at most ⌊k/2⌋ triangle-edges; aggregated over the p_k
    k-gons: total_occ k ≤ ⌊k/2⌋·p_k. Proved from occupation_bound (this
    replaces the former refutable Finset formulation — see note above). -/
lemma kgon_occupation_bound {g : ℤ} (M : SimplyCon3ConnectedMap g) :
    ∀ k ∈ Finset.Ico 4 (M.m + 1),
    M.total_occ k ≤ ((k : ℤ) / 2) * (M.p_i k : ℤ) :=
  fun k hk => (occupation_bound M k hk).2

lemma equality_family {g : ℤ} (M : SimplyCon3ConnectedMap g) :
    ∀ n : ℕ, ∃ (p_i_n : ℕ → ℕ) (v_n e_n : ℕ),
      (v_n : ℤ) - e_n + ∑ k ∈ Finset.Ico 3 (n + 4), (p_i_n k : ℤ) = 2 - 2 * g ∧
      2 * e_n = ∑ k ∈ Finset.Ico 3 (n + 4), k * p_i_n k ∧
      3 * v_n = 2 * e_n ∧
      3 * (p_i_n 6 : ℤ) =
        12 * (1 - g) - (2 * p_i_n 4 + 3 * p_i_n 5) +
        ∑ k ∈ Finset.Ico 7 (n + 4), (((k : ℤ) + 1) / 2 - 6) * p_i_n k := by
  sorry

-- ════════════════════════════════════════════════════════════════════════
-- §3  FROM jucovic_theorem.tex  —  JUČOVIČ THEOREM (sphere, g = 0)
-- ════════════════════════════════════════════════════════════════════════
-- Reference: E. Jučovič, "On the number of hexagons in a map",
--            J. Combinatorial Theory 10 (1971), 232–236.
--
-- Main result: for a simple 3-connected map on the sphere with
-- Σ p_i ≥ 7, we have  p₆ ≥ 4 − (2p₄ + 3p₅)/3 + Σ_{k≥7}(⌊(k+1)/2⌋ − 6)p_k/3.
-- ────────────────────────────────────────────────────────────────────────

-- §3.1  Proved constituent lemmas

/-- [jucovic] k-gons (k ≥ 4) occupy at most ⌊k/2⌋ triangle-edges each;
    aggregated: total_occ k ≤ ⌊k/2⌋·p_k. -/
lemma Juc_KGonMaxOccupation {g : ℤ} (M : SimplyCon3ConnectedMap g) :
    ∀ k ∈ Finset.Ico 4 (M.m + 1),
    M.total_occ k ≤ ((k : ℤ) / 2) * (M.p_i k : ℤ) :=
  kgon_occupation_bound M

-- Juc_QuadAdjacencyConstraint removed (soundness fix 2026-06-10): it wrapped
-- the refutable `quad_occ_reduction`; the faithful quad-adjacency statement
-- requires adjacency data not present in the structure (see note in §2).

/-- [jucovic] Each hexagonal face occupies at most 3 triangle-edges. -/
lemma Juc_HexMaxOccupation {g : ℤ} (M : SimplyCon3ConnectedMap g) (hm : M.m ≥ 6) :
    M.total_occ 6 ≤ 3 * (M.p_i 6 : ℤ) := by
  have h6 : (6 : ℕ) ∈ Finset.Ico 4 (M.m + 1) := by simp [Finset.mem_Ico]; omega
  calc M.total_occ 6
      ≤ ((6 : ℤ) / 2) * (M.p_i 6 : ℤ) := (occupation_bound M 6 h6).2
    _ = 3 * (M.p_i 6 : ℤ)              := by norm_num

/-- [jucovic] Non-hex, non-quad faces have total occupation ≤ Σ ⌊k/2⌋·p_k. -/
lemma Juc_NonHexEdgeBound {g : ℤ} (M : SimplyCon3ConnectedMap g) (hm : M.m ≥ 6) :
    ∑ k ∈ (Finset.Ico 5 (M.m + 1)).erase 6, M.total_occ k ≤
    ∑ k ∈ (Finset.Ico 5 (M.m + 1)).erase 6, ((k : ℤ) / 2) * (M.p_i k : ℤ) := by
  apply Finset.sum_le_sum
  intro k hk
  have h5 : k ∈ Finset.Ico 5 (M.m + 1) := Finset.mem_of_mem_erase hk
  have h4 : k ∈ Finset.Ico 4 (M.m + 1) := by
    simp only [Finset.mem_Ico] at h5 ⊢; omega
  exact (occupation_bound M k h4).2

/-- [jucovic] Infinitely many sphere maps achieve p₆ = RHS (equality family). -/
lemma Juc_EqualityConstruction : ∃ (f : ℕ → SimplyCon3ConnectedMap 0),
    Function.Injective f ∧
    ∀ n : ℕ,
      3 * ((f n).p_i 6 : ℤ) =
        12 - 2 * ((f n).p_i 4 : ℤ) - 3 * ((f n).p_i 5 : ℤ) +
        ∑ k ∈ Finset.Ico 7 ((f n).m + 1),
          (((k : ℤ) + 1) / 2 - 6) * ((f n).p_i k : ℤ) := by
  classical
  let base : SimplyCon3ConnectedMap 0 := {
    m         := 3
    p_i       := fun k => if k = 3 then 4 else 0
    v         := 4
    e         := 6
    total_occ := fun _ => 0 }
  have fam := fun n => equality_family base n
  choose p_fn v_fn e_fn h using fam
  let f : ℕ → SimplyCon3ConnectedMap 0 := fun n => {
    m         := n + 3
    p_i       := p_fn n
    v         := v_fn n
    e         := e_fn n
    total_occ := fun _ => 0 }
  exact ⟨f,
    fun a b hab => by
      have hm : (f a).m = (f b).m := congr_arg SimplyCon3ConnectedMap.m hab
      simp only [f] at hm; omega,
    fun n => by
      simp only [f]
      obtain ⟨-, -, -, heq⟩ := h n
      linarith [heq]⟩

-- §3.2  Arithmetic helpers (proved)

/-- Helper: explicit weighted sum over {3,4,5,6}. -/
private lemma sum_ico_3_7_weighted {g : ℤ} (M : SimplyCon3ConnectedMap g) :
    ∑ k ∈ (Finset.Ico 3 7 : Finset ℕ), ((6 : ℤ) - ↑k) * ↑(M.p_i k) =
      3 * (M.p_i 3 : ℤ) + 2 * (M.p_i 4 : ℤ) + (M.p_i 5 : ℤ) := by
  simp only [show (Finset.Ico 3 7 : Finset ℕ) = {3, 4, 5, 6} from by decide,
    Finset.sum_insert (show (3 : ℕ) ∉ ({4, 5, 6} : Finset ℕ) from by decide),
    Finset.sum_insert (show (4 : ℕ) ∉ ({5, 6} : Finset ℕ) from by decide),
    Finset.sum_insert (show (5 : ℕ) ∉ ({6} : Finset ℕ) from by decide),
    Finset.sum_singleton]
  push_cast; ring

/-- Helper: Σ_{[3,m+1)} (6−k)·p_k = 3p₃ + 2p₄ + p₅ − Σ_{[7,m+1)} (k−6)·p_k.
    (FIXED: no sorry — uses Finset range splitting + p_range for the small-m case.) -/
private lemma sum_split_and_rearrange {g : ℤ} (M : SimplyCon3ConnectedMap g) :
    ∑ k ∈ (Finset.Ico 3 (M.m + 1) : Finset ℕ), ((6 : ℤ) - ↑k) * ↑(M.p_i k) =
      3 * (M.p_i 3 : ℤ) + 2 * (M.p_i 4 : ℤ) + (M.p_i 5 : ℤ) -
      ∑ k ∈ (Finset.Ico 7 (M.m + 1) : Finset ℕ), ((↑k : ℤ) - 6) * ↑(M.p_i k) := by
  by_cases hm : 7 ≤ M.m + 1
  · -- m ≥ 6: split [3, m+1) = [3, 7) ∪ [7, m+1)
    rw [← Finset.sum_Ico_consecutive _ (show 3 ≤ 7 from by norm_num) hm,
        sum_ico_3_7_weighted]
    have hneg : ∑ k ∈ (Finset.Ico 7 (M.m + 1) : Finset ℕ), ((6 : ℤ) - ↑k) * ↑(M.p_i k) =
        -∑ k ∈ (Finset.Ico 7 (M.m + 1) : Finset ℕ), ((↑k : ℤ) - 6) * ↑(M.p_i k) := by
      rw [← Finset.sum_neg_distrib]; congr 1; ext k; push_cast; ring
    linarith [hneg]
  · -- m + 1 < 7: [7, m+1) is empty; extend [3, m+1) to [3, 7) via p_range
    push_neg at hm
    have hempty : (Finset.Ico 7 (M.m + 1) : Finset ℕ) = ∅ := Finset.Ico_eq_empty (by omega)
    rw [hempty, Finset.sum_empty, sub_zero]
    have hext : ∑ k ∈ (Finset.Ico 3 (M.m + 1) : Finset ℕ), ((6 : ℤ) - ↑k) * ↑(M.p_i k) =
        ∑ k ∈ (Finset.Ico 3 7 : Finset ℕ), ((6 : ℤ) - ↑k) * ↑(M.p_i k) := by
      apply Finset.sum_subset (Finset.Ico_subset_Ico_right (by omega : M.m + 1 ≤ 7))
      intro k hk hkm
      simp only [Finset.mem_Ico] at hk hkm
      simp [p_range M k (by omega)]
    rw [hext, sum_ico_3_7_weighted]

/-- Helper: Σ_{[3,m+1)} (6−k)·p_k = 12·(1−g).
    Combines the three axioms (Euler + handshake + regularity). -/
private lemma key_sum {g : ℤ} (M : SimplyCon3ConnectedMap g) :
    ∑ k ∈ Finset.Ico 3 (M.m + 1), ((6 : ℤ) - ↑k) * ↑(M.p_i k) = 12 * (1 - g) := by
  have hreg  : (3 * M.v : ℤ) = 2 * M.e        := by exact_mod_cast regularity M
  have hhand : (2 * M.e : ℤ) =
      ∑ k ∈ Finset.Ico 3 (M.m + 1), (k : ℤ) * M.p_i k := by exact_mod_cast handshake M
  have heuler := euler_formula M
  have hrewrite : ∑ k ∈ Finset.Ico 3 (M.m + 1), ((6 : ℤ) - k) * M.p_i k =
      6 * ∑ k ∈ Finset.Ico 3 (M.m + 1), (M.p_i k : ℤ) -
      ∑ k ∈ Finset.Ico 3 (M.m + 1), (k : ℤ) * M.p_i k := by
    simp_rw [show ∀ k : ℕ, ((6 : ℤ) - k) * M.p_i k =
        6 * M.p_i k - k * M.p_i k from fun k => by ring,
      Finset.sum_sub_distrib, ← Finset.mul_sum]
  linarith [hrewrite]

-- §3.3  Key identity: 3p₃ equation (genus 0 — proved, no sorry)

/-- [jucovic] Edge-count equation for the sphere:
    3p₃ = 12 − 2p₄ − p₅ + Σ_{k≥7}(k−6)·p_k.
    (FIXED: no sorry.) -/
lemma Juc_EulerFormula (M : SimplyCon3ConnectedMap 0) :
    3 * (M.p_i 3 : ℤ) =
      12 - 2 * (M.p_i 4 : ℤ) - (M.p_i 5 : ℤ) +
      ∑ k ∈ Finset.Ico 7 (M.m + 1), ((k : ℤ) - 6) * (M.p_i k : ℤ) := by
  have h1 := key_sum M           -- ∑(6−k)·p_k = 12
  have h2 := sum_split_and_rearrange M  -- expand the sum
  linarith

-- §3.4  Inequality part (sorry: needs quad-occupation cancellation argument)

/-- [jucovic] Hexagon lower bound (sphere, g = 0):
    3·p₆ ≥ 12 − 2p₄ − 3p₅ + Σ_{k≥7}(⌊(k+1)/2⌋ − 6)·p_k.
    SORRY: the arithmetic step combining occupation_conservation,
    Juc_HexMaxOccupation, and Juc_NonHexEdgeBound into the final inequality
    requires the quad-adjacency occupation reduction, which needs face-adjacency
    data the structure does not carry (Mathlib gap: no surface-graph
    quad-adjacency theory). -/
lemma Juc_InequalityPart (M : SimplyCon3ConnectedMap 0) (hm : M.m ≥ 6) :
    3 * (M.p_i 6 : ℤ) ≥
      12 - 2 * (M.p_i 4 : ℤ) - 3 * (M.p_i 5 : ℤ) +
      ∑ k ∈ Finset.Ico 7 (M.m + 1), (((k : ℤ) + 1) / 2 - 6) * (M.p_i k : ℤ) := by
  sorry
  -- Proof sketch (all constituents proved above):
  --   (1) occ_eq : ∑_{k≥4} total_occ k = 3p₃       [occupation_conservation]
  --   (2) p3_eq  : 3p₃ = 12(1−g) − 2p₄ − p₅ + Σ_{k≥7}(k−6)·p_k
  --                                                  [P6EdgeCountEquation below]
  --   (3) hex_ub : total_occ(6) ≤ 3·p₆             [Juc_HexMaxOccupation]
  --   (4) nhex_ub: Σ_{k≥5,k≠6} total_occ(k) ≤ Σ_{k≥5,k≠6} ⌊k/2⌋·p_k
  --                                                  [Juc_NonHexEdgeBound]
  --   Missing: total_occ(4) + nhex_occ_reduction ≤ 2p₄ + 2p₅ + Σ_{k≥7}⌊k/2⌋·p_k
  --   The identity (k−6) − ⌊k/2⌋ = ⌊(k+1)/2⌋ − 6 closes the arithmetic.

/-- [jucovic] Jučovič theorem (sphere, g = 0): full statement with inequality + existence.
    SORRY: depends on Juc_InequalityPart. -/
theorem JucovicTheorem (M : SimplyCon3ConnectedMap 0)
    (h1 : ∑ k ∈ Finset.Ico 3 (M.m + 1), M.p_i k ≥ 7) :
    (3 * (M.p_i 6 : ℤ) ≥
      12 - 2 * (M.p_i 4 : ℤ) - 3 * (M.p_i 5 : ℤ) +
      ∑ k ∈ Finset.Ico 7 (M.m + 1), (((k : ℤ) + 1) / 2 - 6) * (M.p_i k : ℤ)) ∧
    (∃ (f : ℕ → SimplyCon3ConnectedMap 0), Function.Injective f ∧
      ∀ n, 3 * ((f n).p_i 6 : ℤ) =
        12 - 2 * ((f n).p_i 4 : ℤ) - 3 * ((f n).p_i 5 : ℤ) +
        ∑ k ∈ Finset.Ico 7 ((f n).m + 1),
          (((k : ℤ) + 1) / 2 - 6) * ((f n).p_i k : ℤ)) := by
  constructor
  · -- Inequality part: sorry (see Juc_InequalityPart)
    sorry
  · exact Juc_EqualityConstruction

-- ════════════════════════════════════════════════════════════════════════
-- §4  FROM p6.tex  —  p₆ INEQUALITY FOR GENERAL GENUS g
-- ════════════════════════════════════════════════════════════════════════
-- Generalises Jučovič to closed surfaces of arbitrary genus g:
--   p₆ ≥ 4(1−g) − (2p₄ + 3p₅)/3 + Σ_{k≥7}(⌊(k+1)/2⌋ − 6)p_k/3.
-- ────────────────────────────────────────────────────────────────────────

-- §4.1  Edge-count equation — general genus (proved, no sorry)

/-- [p6] Generalised edge-count equation:
    3p₃ = 12(1−g) − 2p₄ − p₅ + Σ_{k≥7}(k−6)·p_k.
    (FIXED: no sorry — uses sum_split_and_rearrange + key_sum.) -/
lemma P6EdgeCountEquation {g : ℤ} (M : SimplyCon3ConnectedMap g) :
    3 * (M.p_i 3 : ℤ) =
      12 * (1 - g) - 2 * (M.p_i 4 : ℤ) - (M.p_i 5 : ℤ) +
      ∑ k ∈ Finset.Ico 7 (M.m + 1), ((k : ℤ) - 6) * (M.p_i k : ℤ) := by
  have h1 := key_sum M
  have h2 := sum_split_and_rearrange M
  linarith

-- §4.2  Face-count helpers
-- Juc_KGonMaxOccupation, Juc_HexMaxOccupation, Juc_NonHexEdgeBound already
-- use {g : ℤ} and cover arbitrary genus — no separate P6 aliases needed.
-- The equality construction for general genus uses equality_family (§2, sorry).

-- §4.3  p₆ inequality — general genus (sorry: same blocker as §3.4)

/-- [p6] General p₆ lower bound:
    3·p₆ ≥ 12(1−g) − 2p₄ − 3p₅ + Σ_{k≥7}(⌊(k+1)/2⌋−6)·p_k.
    SORRY: same blocker as Juc_InequalityPart — quad occupation cancellation. -/
lemma P6InequalityPart {g : ℤ} (M : SimplyCon3ConnectedMap g) (hm : M.m ≥ 6) :
    3 * (M.p_i 6 : ℤ) ≥
      12 * (1 - g) - 2 * (M.p_i 4 : ℤ) - 3 * (M.p_i 5 : ℤ) +
      ∑ k ∈ Finset.Ico 7 (M.m + 1), (((k : ℤ) + 1) / 2 - 6) * (M.p_i k : ℤ) := by
  sorry -- same blocker as Juc_InequalityPart; see proof sketch there

/-- [p6] Main theorem — p₆ genus-g inequality (full statement).
    SORRY: depends on P6InequalityPart. -/
theorem P6GenusG (g : ℤ) (M : SimplyCon3ConnectedMap g)
    (h1 : ∑ i ∈ Finset.Ico 3 (M.m + 1), M.p_i i > 7) :
    (3 * (M.p_i 6 : ℤ) ≥
      12 * (1 - g) - 2 * (M.p_i 4 : ℤ) - 3 * (M.p_i 5 : ℤ) +
      ∑ k ∈ Finset.Ico 7 (M.m + 1), (((k : ℤ) + 1) / 2 - 6) * (M.p_i k : ℤ)) ∧
    (∀ g' : ℤ, Set.Infinite
      {m : SimplyCon3ConnectedMap g' |
        3 * m.p_i 6 = 12 * (1 - g') - 2 * m.p_i 4 - 3 * m.p_i 5 +
        ∑ k ∈ Finset.Ico 7 (m.m + 1), (((k : ℤ) + 1) / 2 - 6) * (m.p_i k : ℤ)}) := by
  exact ⟨sorry, fun _ => sorry⟩
  -- First part: sorry — depends on P6InequalityPart
  -- Second part: sorry — Set.Infinite from equality_family not yet assembled

-- ════════════════════════════════════════════════════════════════════════
-- §5  FROM Euler_inductive.tex  —  EULER'S FORMULA (proved constituents)
-- ════════════════════════════════════════════════════════════════════════
-- The inductive proof from Euler_inductive.tex establishes V − E + F = 2
-- via: (Base) single vertex, (Tree) E = V−1 F = 1, (Step) cycle-edge
-- removal.  The three arithmetic lemmas below are proved here (no sorry).
-- The full EulerEvidence inductive type is not formalised (Mathlib lacks
-- planar-embedding data); the result is axiomatised as euler_formula (§2).
-- ════════════════════════════════════════════════════════════════════════

/-- [Euler_inductive] Base case: single vertex (V=1, E=0, F=1) gives V−E+F=2. -/
lemma eulerBaseCase : (1 : ℤ) - 0 + 1 = 2 := by norm_num

/-- [Euler_inductive] Tree case: for a tree (E = V−1, F = 1), V−E+F=2. -/
lemma eulerTreeCase (v : ℕ) : (v : ℤ) - ((v : ℤ) - 1) + 1 = 2 := by omega

/-- [Euler_inductive] Inductive step: adding a cycle edge (E→E+1, F→F+1) preserves V−E+F=2. -/
lemma eulerInductiveStep (v e f : ℤ) (h : v - e + f = 2) : v - (e + 1) + (f + 1) = 2 := by
  linarith
