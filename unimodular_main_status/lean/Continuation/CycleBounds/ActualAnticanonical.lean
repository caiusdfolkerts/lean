module

public import Continuation.CycleBounds.DeeplyMonotone
public import Continuation.CycleBounds.TorusStrata
public import Continuation.Divisor.ReflectedPolytope

/-!
# Corollary 6.9 for the literal anticanonical section polytope

The toric dictionary uses inward inequalities. Reflecting its actual
anticanonical polytope gives the outward-normal presentation used in the
incidence proof. Reflection preserves deep monotonicity by a proved theorem;
the hypotheses below therefore concern the literal section polytope itself.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace PaperVerification.ToricGeometry.SmoothCompleteFan

open AlgebraicGeometry CategoryTheory PaperVerification.ToricSchemes
universe u
variable {n : ℕ} (F : SmoothCompleteFan n) (k : Type u) [Field k]

/-- Every positive Thomsen line bundle has the asserted ordinary curve
degree when the actual anticanonical section polytope is deeply monotone. -/
theorem corollary_6_9_anticanonical_degree
    (Q : Unimodular.SmoothReflexivePresentation n) (hQ : Q.DeeplyMonotone)
    (hanti : Q.carrier = F.fanPolytope (fun _ ↦ (1 : ℝ)))
    (θ : Module.Dual ℝ (Ambient n))
    (C : InvariantIntegralCurve k n (F.fanSchemeOver k)) :
    ∃ d : ℤ, RationalCurveHasDegree k
      ((Scheme.Modules.pullback C.inclusion.left).obj
        (F.fanCartierData k F.isPure (F.thomsenCoefficients θ)).sheaf) d ∧
      d ≤ (F.thomsenStratumDimension θ : ℤ) := by
  apply F.corollary_6_9_degree k Q.reflected
    (Q.deeplyMonotone_reflected_iff.mpr hQ) _ θ C
  rw [Q.reflected_carrier, hanti]

/-- The same conclusion for every ordinary degree witness, with no sign
convention hidden in the polytope hypothesis. -/
theorem corollary_6_9_anticanonical
    (Q : Unimodular.SmoothReflexivePresentation n) (hQ : Q.DeeplyMonotone)
    (hanti : Q.carrier = F.fanPolytope (fun _ ↦ (1 : ℝ)))
    (θ : Module.Dual ℝ (Ambient n))
    (C : InvariantIntegralCurve k n (F.fanSchemeOver k)) (d : ℤ)
    (hd : RationalCurveHasDegree k
      ((Scheme.Modules.pullback C.inclusion.left).obj
        (F.fanCartierData k F.isPure (F.thomsenCoefficients θ)).sheaf) d) :
    d ≤ (F.thomsenStratumDimension θ : ℤ) := by
  apply F.corollary_6_9 k Q.reflected
    (Q.deeplyMonotone_reflected_iff.mpr hQ) _ θ C d hd
  rw [Q.reflected_carrier, hanti]

/-- Corollary 6.9 quantified over the actual character-torus strata and
every lifted representative, for the original fan scheme and line bundle. -/
theorem corollary_6_9_anticanonical_torusStrata
    (Q : Unimodular.SmoothReflexivePresentation n) (hQ : Q.DeeplyMonotone)
    (hanti : Q.carrier = F.fanPolytope (fun _ ↦ (1 : ℝ)))
    (σ : F.TorusStratum) (θ : Module.Dual ℝ (Ambient n))
    (hθ : σ.val = F.torusStratum θ)
    (C : InvariantIntegralCurve k n (F.fanSchemeOver k)) :
    ∃ d : ℤ, RationalCurveHasDegree k
      ((Scheme.Modules.pullback C.inclusion.left).obj
        (F.fanCartierData k F.isPure (F.thomsenCoefficients θ)).sheaf) d ∧
      d ≤ (σ.dimension : ℤ) := by
  rw [σ.dimension_eq θ hθ]
  exact F.corollary_6_9_anticanonical_degree k Q hQ hanti θ C

#print axioms corollary_6_9_anticanonical_degree
#print axioms corollary_6_9_anticanonical
#print axioms corollary_6_9_anticanonical_torusStrata

end PaperVerification.ToricGeometry.SmoothCompleteFan
