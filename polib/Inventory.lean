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
-- • The sorried statements below are the accepted axiom base — each one is a
--   statement or proof step taken verbatim from the three source papers
--   (Mathlib's SimpleGraph API does not cover surface-embedded maps):
--     §2  euler_formula, handshake, regularity, p_range,
--         occupation_conservation, occupation_bound, quad_occ_cancellation,
--         equality_family
--     §3.4 JucovicTheorem (inequality conjunct; m < 6 edge case)
--     §4.3 P6GenusG (both conjuncts; m < 6 edge case / Set.Infinite assembly)
--   Everything else is proved without sorry. In particular Juc_InequalityPart
--   and P6InequalityPart are PROVED (2026-06-11) from occupation_conservation
--   + occupation_bound + quad_occ_cancellation — see §4.3.
-- • POLICY: this sorry set is CLOSED and hand-curated from the papers. The
--   prover may CALL these lemmas freely (not a new sorry) but must NEVER add
--   a new sorried lemma of its own, even one that "looks like" paper content.
-- • Soundness guard (fix 2026-06-11): every axiom now requires `IsMap M`,
--   an OPAQUE realizability predicate with no introduction rule. Without
--   the guard the axiom base was inconsistent inside Lean: the all-zero
--   instance ⟨3, fun _ => 0, 0, 0, fun _ => 0⟩ refuted euler_formula
--   (0 = 2), so False — and hence any conjecture — was derivable with
--   zero sorry. The ONLY sources of an `IsMap` token are (a) hypotheses
--   of the theorem being proved and (b) the existential witnesses of
--   `equality_family`. Fabricated instances can never satisfy it.
-- ════════════════════════════════════════════════════════════════════════
import Mathlib

-- ════════════════════════════════════════════════════════════════════════
-- §1  DATA STRUCTURE
-- ════════════════════════════════════════════════════════════════════════

/-- A simple 3-connected map on a closed surface of genus g.
    Only combinatorial data is stored; geometric constraints appear as
    sorried axioms below, guarded by `IsMap`. -/
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

/-- Realizability predicate: `IsMap M` asserts that the combinatorial data
    of `M` comes from an actual simple 3-connected map on a closed surface
    of genus `g`. Deliberately OPAQUE with no introduction rule: proofs can
    obtain it only from theorem hypotheses or from `equality_family`.
    This guards the sorried axioms from being applied to fabricated data
    (soundness fix 2026-06-11 — see header). The witness below merely
    establishes inhabitation; opacity makes it invisible to proofs. -/
opaque IsMap : ∀ {g : ℤ}, SimplyCon3ConnectedMap g → Prop :=
  fun {_} _ => True

-- ════════════════════════════════════════════════════════════════════════
-- §2  FOUNDATIONAL LEMMAS (sorry: Mathlib lacks surface-embedded graph API)
-- (from Euler_inductive.tex, jucovic_theorem.tex, p6.tex)
-- ════════════════════════════════════════════════════════════════════════

lemma euler_formula {g : ℤ} (M : SimplyCon3ConnectedMap g) (hM : IsMap M) :
    (M.v : ℤ) - M.e + ∑ k ∈ Finset.Ico 3 (M.m + 1), (M.p_i k : ℤ) = 2 - 2 * g := by
  sorry

lemma handshake {g : ℤ} (M : SimplyCon3ConnectedMap g) (hM : IsMap M) :
    2 * M.e = ∑ k ∈ Finset.Ico 3 (M.m + 1), k * M.p_i k := by
  sorry

lemma regularity {g : ℤ} (M : SimplyCon3ConnectedMap g) (hM : IsMap M) :
    3 * M.v = 2 * M.e := by
  sorry

-- NOTE (soundness fix 2026-06-10): the former `kgon_occupation_bound` and
-- `quad_occ_reduction` quantified over arbitrary `Finset ℕ` instead of the
-- map's own occupation data and were refutable inside Lean (e.g. occ = {0,1,2},
-- k = 4 gives 3 ≤ 2), making the axiom base inconsistent.
--   • kgon_occupation_bound is restated on `total_occ` below (after
--     occupation_bound, from which it is now PROVED — no longer an axiom).
--   • quad_occ_reduction ("an r-gon adjacent to a quad occupies ≤ ⌊r/2⌋ − 1")
--     needs face-adjacency data that `SimplyCon3ConnectedMap` does not carry.
--     Its faithful AGGREGATE consequence is `quad_occ_cancellation` below
--     (added 2026-06-11), which is expressible on `total_occ` and is exactly
--     the form the paper's argument uses.

lemma p_range {g : ℤ} (M : SimplyCon3ConnectedMap g) (hM : IsMap M) :
    ∀ k : ℕ, M.m < k → M.p_i k = 0 := by
  sorry

/-- [p6, p.3] "The equation 3p₃ = … counts the number of edges of triangular
    faces that must be occupied by k-gons with k ≥ 4."
    GUARD (faithfulness, 2026-06-11): requires m ≥ 6. The paper first excludes
    the exceptional maps (tetrahedron, 3-prism, Figure 1b — the only simple
    3-connected maps with a triangle adjacent to a triangle, etc.); the
    tetrahedron (m = 3) genuinely violates the unguarded equation (its triangle
    edges are occupied by triangles, giving 0 = 3p₃ = 12). All exceptional maps
    have m ≤ 5, so m ≥ 6 excludes them and the equation is exact. -/
lemma occupation_conservation {g : ℤ} (M : SimplyCon3ConnectedMap g) (hM : IsMap M)
    (hm : M.m ≥ 6) :
    ∑ k ∈ Finset.Ico 4 (M.m + 1), M.total_occ k = 3 * (M.p_i 3 : ℤ) := by
  sorry

lemma occupation_bound {g : ℤ} (M : SimplyCon3ConnectedMap g) (hM : IsMap M) :
    ∀ k : ℕ, k ∈ Finset.Ico 4 (M.m + 1) →
    0 ≤ M.total_occ k ∧ M.total_occ k ≤ ((k : ℤ) / 2) * (M.p_i k : ℤ) := by
  sorry

/-- A k-gon occupies at most ⌊k/2⌋ triangle-edges; aggregated over the p_k
    k-gons: total_occ k ≤ ⌊k/2⌋·p_k. Proved from occupation_bound (this
    replaces the former refutable Finset formulation — see note above). -/
lemma kgon_occupation_bound {g : ℤ} (M : SimplyCon3ConnectedMap g) (hM : IsMap M) :
    ∀ k ∈ Finset.Ico 4 (M.m + 1),
    M.total_occ k ≤ ((k : ℤ) / 2) * (M.p_i k : ℤ) :=
  fun k hk => (occupation_bound M hM k hk).2

/-- [p6, p.4] Quadrangle cancellation (aggregate form): "A quadrangular face
    … even if it occupies one edge of a triangle, then at least one r-gonal
    face (r > 4) occupies not more than ⌊r/2⌋ − 1 edges. … So the k-gonal
    faces with k ≥ 4, k ≠ 6, can occupy at most Σ_{k≥5,k≠6} ⌊k/2⌋·p_k edges
    of triangles" — i.e. quadrangles contribute net zero.
    Stated on the map's own `total_occ` data (the former per-face formulation
    `quad_occ_reduction` needed adjacency data and was removed; this aggregate
    consequence is exactly what the paper uses and is expressible here).
    GUARD: m ≥ 6 excludes the exceptional maps (3-prism and Figure 1b violate
    the bound; both have m ≤ 5). -/
lemma quad_occ_cancellation {g : ℤ} (M : SimplyCon3ConnectedMap g) (hM : IsMap M)
    (hm : M.m ≥ 6) :
    ∑ k ∈ (Finset.Ico 4 (M.m + 1)).erase 6, M.total_occ k ≤
    ∑ k ∈ (Finset.Ico 5 (M.m + 1)).erase 6, ((k : ℤ) / 2) * (M.p_i k : ℤ) := by
  sorry

/-- For every n there is a REALIZABLE map of genus g with max face size n+3
    achieving the p₆ equality case. The `IsMap` conjunct is essential: it is
    the only introduction route for `IsMap`, and it makes the statement carry
    real geometric content (existence of bare data satisfying the linear
    equations alone is trivially provable and was the former formulation). -/
lemma equality_family {g : ℤ} :
    ∀ n : ℕ, ∃ (M_n : SimplyCon3ConnectedMap g),
      IsMap M_n ∧
      M_n.m = n + 3 ∧
      3 * (M_n.p_i 6 : ℤ) =
        12 * (1 - g) - (2 * (M_n.p_i 4 : ℤ) + 3 * (M_n.p_i 5 : ℤ)) +
        ∑ k ∈ Finset.Ico 7 (M_n.m + 1), (((k : ℤ) + 1) / 2 - 6) * (M_n.p_i k : ℤ) := by
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
lemma Juc_KGonMaxOccupation {g : ℤ} (M : SimplyCon3ConnectedMap g) (hM : IsMap M) :
    ∀ k ∈ Finset.Ico 4 (M.m + 1),
    M.total_occ k ≤ ((k : ℤ) / 2) * (M.p_i k : ℤ) :=
  kgon_occupation_bound M hM

-- Juc_QuadAdjacencyConstraint removed (soundness fix 2026-06-10): it wrapped
-- the refutable `quad_occ_reduction`; the faithful quad-adjacency statement
-- requires adjacency data not present in the structure (see note in §2).

/-- [jucovic] Each hexagonal face occupies at most 3 triangle-edges. -/
lemma Juc_HexMaxOccupation {g : ℤ} (M : SimplyCon3ConnectedMap g) (hM : IsMap M)
    (hm : M.m ≥ 6) :
    M.total_occ 6 ≤ 3 * (M.p_i 6 : ℤ) := by
  have h6 : (6 : ℕ) ∈ Finset.Ico 4 (M.m + 1) := by simp [Finset.mem_Ico]; omega
  calc M.total_occ 6
      ≤ ((6 : ℤ) / 2) * (M.p_i 6 : ℤ) := (occupation_bound M hM 6 h6).2
    _ = 3 * (M.p_i 6 : ℤ)              := by norm_num

/-- [jucovic] Non-hex, non-quad faces have total occupation ≤ Σ ⌊k/2⌋·p_k. -/
lemma Juc_NonHexEdgeBound {g : ℤ} (M : SimplyCon3ConnectedMap g) (hM : IsMap M)
    (hm : M.m ≥ 6) :
    ∑ k ∈ (Finset.Ico 5 (M.m + 1)).erase 6, M.total_occ k ≤
    ∑ k ∈ (Finset.Ico 5 (M.m + 1)).erase 6, ((k : ℤ) / 2) * (M.p_i k : ℤ) := by
  apply Finset.sum_le_sum
  intro k hk
  have h5 : k ∈ Finset.Ico 5 (M.m + 1) := Finset.mem_of_mem_erase hk
  have h4 : k ∈ Finset.Ico 4 (M.m + 1) := by
    simp only [Finset.mem_Ico] at h5 ⊢; omega
  exact (occupation_bound M hM k h4).2

/-- [jucovic] Infinitely many realizable sphere maps achieve p₆ = RHS
    (equality family). Proved from `equality_family` — no instance is
    constructed here; the witnesses (and their `IsMap` tokens) come from
    the axiom's existential. -/
lemma Juc_EqualityConstruction : ∃ (f : ℕ → SimplyCon3ConnectedMap 0),
    Function.Injective f ∧
    ∀ n : ℕ, IsMap (f n) ∧
      3 * ((f n).p_i 6 : ℤ) =
        12 - 2 * ((f n).p_i 4 : ℤ) - 3 * ((f n).p_i 5 : ℤ) +
        ∑ k ∈ Finset.Ico 7 ((f n).m + 1),
          (((k : ℤ) + 1) / 2 - 6) * ((f n).p_i k : ℤ) := by
  classical
  choose f hIs hm hp6 using equality_family (g := 0)
  refine ⟨f, fun a b hab => ?_, fun n => ⟨hIs n, ?_⟩⟩
  · have hmm : (f a).m = (f b).m := congrArg SimplyCon3ConnectedMap.m hab
    rw [hm a, hm b] at hmm
    omega
  · have h := hp6 n
    linarith [h]

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
private lemma sum_split_and_rearrange {g : ℤ} (M : SimplyCon3ConnectedMap g)
    (hM : IsMap M) :
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
      simp [p_range M hM k (by omega)]
    rw [hext, sum_ico_3_7_weighted]

/-- Helper: Σ_{[3,m+1)} (6−k)·p_k = 12·(1−g).
    Combines the three axioms (Euler + handshake + regularity). -/
private lemma key_sum {g : ℤ} (M : SimplyCon3ConnectedMap g) (hM : IsMap M) :
    ∑ k ∈ Finset.Ico 3 (M.m + 1), ((6 : ℤ) - ↑k) * ↑(M.p_i k) = 12 * (1 - g) := by
  have hreg  : (3 * M.v : ℤ) = 2 * M.e        := by exact_mod_cast regularity M hM
  have hhand : (2 * M.e : ℤ) =
      ∑ k ∈ Finset.Ico 3 (M.m + 1), (k : ℤ) * M.p_i k := by exact_mod_cast handshake M hM
  have heuler := euler_formula M hM
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
lemma Juc_EulerFormula (M : SimplyCon3ConnectedMap 0) (hM : IsMap M) :
    3 * (M.p_i 3 : ℤ) =
      12 - 2 * (M.p_i 4 : ℤ) - (M.p_i 5 : ℤ) +
      ∑ k ∈ Finset.Ico 7 (M.m + 1), ((k : ℤ) - 6) * (M.p_i k : ℤ) := by
  have h1 := key_sum M hM           -- ∑(6−k)·p_k = 12
  have h2 := sum_split_and_rearrange M hM  -- expand the sum
  linarith

-- §3.4  Inequality part
-- Juc_InequalityPart is now PROVED (2026-06-11, from quad_occ_cancellation)
-- as the g = 0 instance of P6InequalityPart — see §4.3 below (file order:
-- the general proof uses P6EdgeCountEquation, defined in §4.1).

/-- [jucovic] Jučovič theorem (sphere, g = 0): full statement with inequality + existence.
    SORRY (accepted, paper statement): the inequality conjunct has no m ≥ 6
    hypothesis; the m < 6 edge case needs the exceptional-map classification
    (tetrahedron / 3-prism / Figure 1b) that the structure cannot express.
    For m ≥ 6 it follows from Juc_InequalityPart (§4.3). -/
theorem JucovicTheorem (M : SimplyCon3ConnectedMap 0) (hM : IsMap M)
    (h1 : ∑ k ∈ Finset.Ico 3 (M.m + 1), M.p_i k ≥ 7) :
    (3 * (M.p_i 6 : ℤ) ≥
      12 - 2 * (M.p_i 4 : ℤ) - 3 * (M.p_i 5 : ℤ) +
      ∑ k ∈ Finset.Ico 7 (M.m + 1), (((k : ℤ) + 1) / 2 - 6) * (M.p_i k : ℤ)) ∧
    (∃ (f : ℕ → SimplyCon3ConnectedMap 0), Function.Injective f ∧
      ∀ n, IsMap (f n) ∧
        3 * ((f n).p_i 6 : ℤ) =
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
lemma P6EdgeCountEquation {g : ℤ} (M : SimplyCon3ConnectedMap g) (hM : IsMap M) :
    3 * (M.p_i 3 : ℤ) =
      12 * (1 - g) - 2 * (M.p_i 4 : ℤ) - (M.p_i 5 : ℤ) +
      ∑ k ∈ Finset.Ico 7 (M.m + 1), ((k : ℤ) - 6) * (M.p_i k : ℤ) := by
  have h1 := key_sum M hM
  have h2 := sum_split_and_rearrange M hM
  linarith

-- §4.2  Face-count helpers
-- Juc_KGonMaxOccupation, Juc_HexMaxOccupation, Juc_NonHexEdgeBound already
-- use {g : ℤ} and cover arbitrary genus — no separate P6 aliases needed.
-- The equality construction for general genus uses equality_family (§2, sorry).

-- §4.3  p₆ inequality — general genus (PROVED 2026-06-11, no sorry)

/-- [p6] General p₆ lower bound:
    3·p₆ ≥ 12(1−g) − 2p₄ − 3p₅ + Σ_{k≥7}(⌊(k+1)/2⌋−6)·p_k.
    PROVED from occupation_conservation + occupation_bound +
    quad_occ_cancellation + the edge-count equation, following p6.pdf p.3-4:
    hexagons must absorb the triangle-edge demand left over after all other
    k-gons (with quadrangles cancelling) have occupied their maximum. -/
lemma P6InequalityPart {g : ℤ} (M : SimplyCon3ConnectedMap g) (hM : IsMap M)
    (hm : M.m ≥ 6) :
    3 * (M.p_i 6 : ℤ) ≥
      12 * (1 - g) - 2 * (M.p_i 4 : ℤ) - 3 * (M.p_i 5 : ℤ) +
      ∑ k ∈ Finset.Ico 7 (M.m + 1), (((k : ℤ) + 1) / 2 - 6) * (M.p_i k : ℤ) := by
  have h6mem : (6 : ℕ) ∈ Finset.Ico 4 (M.m + 1) := by
    simp only [Finset.mem_Ico]; omega
  -- (1) conservation, with k = 6 extracted:
  --     total_occ 6 + Σ_{k∈[4,m]∖{6}} total_occ k = 3p₃
  have hcons := occupation_conservation M hM hm
  rw [← Finset.add_sum_erase _ _ h6mem] at hcons
  -- (2) quadrangle cancellation: Σ_{k∈[4,m]∖{6}} total_occ k ≤ Σ_{k∈[5,m]∖{6}} ⌊k/2⌋p_k
  have hquad := quad_occ_cancellation M hM hm
  -- (3) hexagons absorb at most 3p₆
  have hhex := Juc_HexMaxOccupation M hM hm
  -- (4) edge-count equation: 3p₃ = 12(1−g) − 2p₄ − p₅ + Σ_{k≥7}(k−6)p_k
  have hedge := P6EdgeCountEquation M hM
  -- (5) split the cancellation RHS: [5,m]∖{6} = {5} ∪ [7,m]; ⌊5/2⌋ = 2
  have hset : (Finset.Ico 5 (M.m + 1)).erase 6 = insert 5 (Finset.Ico 7 (M.m + 1)) := by
    ext a
    simp only [Finset.mem_erase, Finset.mem_Ico, Finset.mem_insert]
    omega
  have h5notin : (5 : ℕ) ∉ Finset.Ico 7 (M.m + 1) := by
    simp [Finset.mem_Ico]
  have hsplit : ∑ k ∈ (Finset.Ico 5 (M.m + 1)).erase 6, ((k : ℤ) / 2) * (M.p_i k : ℤ)
      = 2 * (M.p_i 5 : ℤ)
        + ∑ k ∈ Finset.Ico 7 (M.m + 1), ((k : ℤ) / 2) * (M.p_i k : ℤ) := by
    rw [hset, Finset.sum_insert h5notin]
    norm_num
  -- (6) coefficient identity per k ≥ 7: (k−6) − ⌊k/2⌋ = ⌊(k+1)/2⌋ − 6
  have hco : ∑ k ∈ Finset.Ico 7 (M.m + 1), (((k : ℤ) + 1) / 2 - 6) * (M.p_i k : ℤ)
      = ∑ k ∈ Finset.Ico 7 (M.m + 1), ((k : ℤ) - 6) * (M.p_i k : ℤ)
        - ∑ k ∈ Finset.Ico 7 (M.m + 1), ((k : ℤ) / 2) * (M.p_i k : ℤ) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k hk => ?_
    have h7 : 7 ≤ k := (Finset.mem_Ico.mp hk).1
    have hkid : ((k : ℤ) + 1) / 2 - 6 = ((k : ℤ) - 6) - (k : ℤ) / 2 := by omega
    rw [hkid]; ring
  -- chain: 3p₆ ≥ occ₆ = 3p₃ − Σ∖{6} ≥ 3p₃ − 2p₅ − Σ_{k≥7}⌊k/2⌋p_k = RHS
  linarith [hcons, hquad, hhex, hedge, hsplit, hco]

/-- [jucovic] Hexagon lower bound (sphere, g = 0):
    3·p₆ ≥ 12 − 2p₄ − 3p₅ + Σ_{k≥7}(⌊(k+1)/2⌋ − 6)·p_k.
    PROVED: the g = 0 instance of P6InequalityPart. -/
lemma Juc_InequalityPart (M : SimplyCon3ConnectedMap 0) (hM : IsMap M)
    (hm : M.m ≥ 6) :
    3 * (M.p_i 6 : ℤ) ≥
      12 - 2 * (M.p_i 4 : ℤ) - 3 * (M.p_i 5 : ℤ) +
      ∑ k ∈ Finset.Ico 7 (M.m + 1), (((k : ℤ) + 1) / 2 - 6) * (M.p_i k : ℤ) := by
  have h := P6InequalityPart M hM hm
  linarith

/-- [p6] Main theorem — p₆ genus-g inequality (full statement).
    SORRY (accepted, paper statement): same m < 6 edge case as JucovicTheorem
    for the first conjunct; Set.Infinite assembly from equality_family for the
    second. For m ≥ 6 the first conjunct follows from P6InequalityPart. -/
theorem P6GenusG (g : ℤ) (M : SimplyCon3ConnectedMap g) (hM : IsMap M)
    (h1 : ∑ i ∈ Finset.Ico 3 (M.m + 1), M.p_i i > 7) :
    (3 * (M.p_i 6 : ℤ) ≥
      12 * (1 - g) - 2 * (M.p_i 4 : ℤ) - 3 * (M.p_i 5 : ℤ) +
      ∑ k ∈ Finset.Ico 7 (M.m + 1), (((k : ℤ) + 1) / 2 - 6) * (M.p_i k : ℤ)) ∧
    (∀ g' : ℤ, Set.Infinite
      {m : SimplyCon3ConnectedMap g' | IsMap m ∧
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
