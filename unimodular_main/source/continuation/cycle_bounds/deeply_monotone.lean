module

public import Continuation.CycleBounds.InvariantDegrees
public import Continuation.CycleBounds.DeeplyMonotoneIncidence

/-!
# Corollary 6.9 on all invariant curves of the supplied fan

The integral incidence construction is imported from its unique source owner.
The results below concern the actual curve degrees and the literal anticanonical polytope.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators Matroid
open Set

namespace PaperVerification.ToricGeometry.SmoothCompleteFan
open AlgebraicGeometry CategoryTheory PaperVerification.ToricSchemes
open Unimodular.CycleBounds
universe u
variable {n : ℕ} (F : SmoothCompleteFan n) (k : Type u) [Field k]

/-- Corollary 6.9 for the original toric fan and the actual reflected
anticanonical polytope. The conclusion retains every stratum and every
intrinsic invariant integral curve. Projectivity is not an additional input
needed by this stronger consequence. -/
theorem deeplyMonotone_anticanonical_invariantCurve_bound
    (P : Unimodular.SmoothReflexivePresentation n) (hP : P.DeeplyMonotone)
    (hcarrier : P.carrier = {x : Ambient n | ∀ u ∈ F.rays, Unimodular.pairing x u ≤ 1})
    (θ : Module.Dual ℝ (Ambient n))
    (C : InvariantIntegralCurve k n (F.fanSchemeOver k)) (d : ℤ)
    (hd : RationalCurveHasDegree k
      ((Scheme.Modules.pullback C.inclusion.left).obj
        (F.fanCartierData k F.isPure (F.thomsenCoefficients θ)).sheaf) d) :
    d ≤ (F.thomsenStratumDimension θ : ℤ) := by
  obtain ⟨G, hG, hK, δ, hinj, hδ⟩ := anticanonical_integral_incidence_no_K4 F P hP hcarrier
  exact F.thomsen_invariantCurve_every_degree_bound k G hG hK δ hinj (fun u => by
    rw [hδ u]
    ext a
    by_cases hs : a = G.source u <;> by_cases ht : a = G.target u <;>
      simp [Pi.single_apply, hs, ht]) θ C d hd

/-- The paper uses outward normals, hence the reflected unit-boundary
polytope of the ordinary toric divisor convention. -/
theorem reflected_anticanonical_polytope :
    Neg.neg '' F.fanPolytope (fun _ ↦ (1 : ℝ)) =
      {x : Ambient n | ∀ u ∈ F.rays, Unimodular.pairing x u ≤ 1} := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩ u hu
    have h := hy u hu
    change -1 ≤ (∑ i, (u i : ℝ) * y i) at h
    change (∑ i, (-y i) * (u i : ℝ)) ≤ 1
    have heq : (∑ i, (-y i) * (u i : ℝ)) = -(∑ i, (u i : ℝ) * y i) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [heq]
    linarith
  · intro hx
    refine ⟨-x, ?_, neg_neg x⟩
    intro u hu
    have h := hx u hu
    change (∑ i, x i * (u i : ℝ)) ≤ 1 at h
    change -1 ≤ (∑ i, (u i : ℝ) * (-x i))
    have heq : (∑ i, (u i : ℝ) * (-x i)) = -(∑ i, x i * (u i : ℝ)) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [heq]
    linarith

/-- The existential degree form of Corollary 6.9. No degree witness is required
as an additional hypothesis: every restricted Thomsen line bundle has the
ordinary rational-curve degree supplied by the theorem. -/
theorem corollary_6_9_degree
    (P : Unimodular.SmoothReflexivePresentation n) (hP : P.DeeplyMonotone)
    (hanti : P.carrier = Neg.neg '' F.fanPolytope (fun _ ↦ (1 : ℝ)))
    (θ : Module.Dual ℝ (Ambient n))
    (C : InvariantIntegralCurve k n (F.fanSchemeOver k)) :
    ∃ d : ℤ, RationalCurveHasDegree k
      ((Scheme.Modules.pullback C.inclusion.left).obj
        (F.fanCartierData k F.isPure (F.thomsenCoefficients θ)).sheaf) d ∧
      d ≤ (F.thomsenStratumDimension θ : ℤ) := by
  obtain ⟨G, hG, hK, δ, hinj, hδ⟩ := anticanonical_integral_incidence_no_K4 F P hP
    (hanti.trans F.reflected_anticanonical_polytope)
  exact F.thomsen_invariantCurve_degree_bound k G hG hK δ hinj (fun u => by
    rw [hδ u]
    ext a
    by_cases hs : a = G.source u <;> by_cases ht : a = G.target u <;>
      simp [Pi.single_apply, hs, ht]) θ C

/-- Corollary 6.9, with the exact reflected anticanonical polytope and the
ordinary degree of every restricted Thomsen line bundle. -/
theorem corollary_6_9
    (P : Unimodular.SmoothReflexivePresentation n) (hP : P.DeeplyMonotone)
    (hanti : P.carrier = Neg.neg '' F.fanPolytope (fun _ ↦ (1 : ℝ)))
    (θ : Module.Dual ℝ (Ambient n))
    (C : InvariantIntegralCurve k n (F.fanSchemeOver k)) (d : ℤ)
    (hd : RationalCurveHasDegree k
      ((Scheme.Modules.pullback C.inclusion.left).obj
        (F.fanCartierData k F.isPure (F.thomsenCoefficients θ)).sheaf) d) :
    d ≤ (F.thomsenStratumDimension θ : ℤ) :=
  F.deeplyMonotone_anticanonical_invariantCurve_bound k P hP
    (hanti.trans F.reflected_anticanonical_polytope) θ C d hd

#print axioms corollary_6_9
#print axioms corollary_6_9_degree
#print axioms deeplyMonotone_anticanonical_invariantCurve_bound
end PaperVerification.ToricGeometry.SmoothCompleteFan
