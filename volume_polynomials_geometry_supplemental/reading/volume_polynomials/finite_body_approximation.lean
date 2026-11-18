module
public import VolumePolynomials.FinitePolytope
public import VolumePolynomials.RealizationContinuity
public import Mathlib.Topology.MetricSpace.Pseudo.Basic

@[expose] public section

set_option autoImplicit false
noncomputable section

/-!
# Approximation by actual finite convex hulls

Finite nets inside a compact convex body give inscribed polytopes at arbitrarily
small Hausdorff distance. The closed finite-dimensional evaluation range then
transfers polynomiality, including nonnegativity of every coefficient, from
all polytopes to all convex bodies. The polytope theorem remains an explicit
premise of the transfer lemma and must be proved separately.
-/

open Set Metric Topology
open scoped Topology BigOperators

namespace VolumePolynomials
open PolytopeGeometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def finiteHullBody (S : Set E) (hS : S.Finite) (hne : S.Nonempty) : ConvexBody E where
  carrier := convexHull ℝ S
  convex' := convex_convexHull ℝ S
  isCompact' := hS.isCompact_convexHull ℝ
  nonempty' := hne.mono (subset_convexHull ℝ S)

theorem finiteHullBody_isFiniteHull (S : Set E) (hS : S.Finite) (hne : S.Nonempty) :
    IsFiniteHull (finiteHullBody S hS hne : Set E) := ⟨S, hS, rfl⟩

/-- The approximating vertices lie in the original body. -/
theorem exists_inscribed_finiteHullBody (K : ConvexBody E) {ε : ℝ} (hε : 0 < ε) :
    ∃ P : ConvexBody E, IsFiniteHull (P : Set E) ∧ P ≤ K ∧ dist P K < ε := by
  first
  | obtain ⟨S, hSK, hS, hcover⟩ :=
      Metric.finite_approx_of_totallyBounded K.isCompact.totallyBounded (ε / 2) (half_pos hε)
    have hne : S.Nonempty := by
      obtain ⟨x, hx⟩ := K.nonempty
      obtain ⟨y, hy, _⟩ := Set.mem_iUnion₂.mp (hcover hx)
      exact ⟨y, hy⟩
    let P := finiteHullBody S hS hne
    have hPK : P ≤ K := convexHull_min hSK K.convex
    refine ⟨P, finiteHullBody_isFiniteHull S hS hne, hPK, ?_⟩
    have hdist : dist P K ≤ ε / 2 := by
      change hausdorffDist (P : Set E) (K : Set E) ≤ ε / 2
      apply hausdorffDist_le_of_mem_dist (half_pos hε).le
      · intro x hx
        exact ⟨x, hPK hx, by simpa using (half_pos hε).le⟩
      · intro x hx
        obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp (hcover hx)
        exact ⟨y, subset_convexHull ℝ S hy, (Metric.mem_ball.mp hxy).le⟩
    exact hdist.trans_lt (half_lt_self hε)

theorem dense_finiteHullBodies :
    Dense {K : ConvexBody E | IsFiniteHull (K : Set E)} := by
  first
  | rw [Metric.dense_iff]
    intro K ε hε
    obtain ⟨P, hp, _, hdist⟩ := exists_inscribed_finiteHullBody K hε
    exact ⟨P, hdist, hp⟩

theorem dense_finiteHullBodyTuples (n : ℕ) :
    Dense {K : Fin n → ConvexBody E | ∀ i, IsFiniteHull (K i : Set E)} := by
  first
  | simpa [Set.pi] using
      (dense_pi Set.univ (fun (_ : Fin n) _ => dense_finiteHullBodies (E := E)))

def NonnegativeCoefficients (n d : ℕ) : Set (Coefficients n d) :=
  {c | ∀ α, 0 ≤ c α}

theorem isClosed_nonnegativeCoefficients (n d : ℕ) :
    IsClosed (NonnegativeCoefficients n d) := by
  first
  | change IsClosed {c : Coefficients n d | ∀ α, c α ∈ Set.Ici (0 : ℝ)}
    simp only [ofPred_forall]
    exact isClosed_iInter fun α => isClosed_Ici.preimage (continuous_apply α)

theorem isClosed_tuples_with_nonnegative_volume_polynomial (n d : ℕ) :
    IsClosed {K : Fin n → Body d |
      ∃ c : Coefficients n d, (∀ α, 0 ≤ c α) ∧ Realizes K c} := by
  first
  | have hclosed := (isClosedEmbedding_evaluation n d).isClosedMap
      (NonnegativeCoefficients n d) (isClosed_nonnegativeCoefficients n d)
    have heq : {K : Fin n → Body d |
        ∃ c : Coefficients n d, (∀ α, 0 ≤ c α) ∧ Realizes K c} =
        volumeEvaluation ⁻¹' (evaluationEmbedding n d '' NonnegativeCoefficients n d) := by
      ext K
      simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_image,
        NonnegativeCoefficients, realizes_iff_evaluation_eq]
    rw [heq]
    exact hclosed.preimage (continuous_volumeEvaluation n d)

/-- The only premise is the full polytope theorem, with no vertex bound or
general-position restriction. The conclusion covers every compact convex body. -/
theorem exists_nonnegative_realizes_of_all_finiteHulls (n d : ℕ)
    (hpoly : ∀ K : Fin n → Body d, (∀ i, IsFiniteHull (K i : Set (Space d))) →
      ∃ c : Coefficients n d, (∀ α, 0 ≤ c α) ∧ Realizes K c)
    (K : Fin n → Body d) :
    ∃ c : Coefficients n d, (∀ α, 0 ≤ c α) ∧ Realizes K c := by
  first
  | have hsub : {L : Fin n → Body d | ∀ i, IsFiniteHull (L i : Set (Space d))} ⊆
        {L | ∃ c : Coefficients n d, (∀ α, 0 ≤ c α) ∧ Realizes L c} := hpoly
    exact closure_minimal hsub (isClosed_tuples_with_nonnegative_volume_polynomial n d)
      (dense_finiteHullBodyTuples (E := Space d) n K)

end VolumePolynomials
