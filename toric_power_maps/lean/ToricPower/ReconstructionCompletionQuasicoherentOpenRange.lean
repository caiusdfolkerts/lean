module

public import ToricPower.ReconstructionCompletionOpenRange
public import ToricPower.FiniteTotalEvaluationCriterion

/-! # The original top comparison on an affine image open

The finite-total map and both inherited sheaf-complex categories are
fixed before substituting a toric chart or a concrete coefficient functor.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace ToricPower

open FunctorTotal

variable {U X : Scheme.{0}} (j : U ⟶ X) [IsOpenImmersion j]
  [IsAffineHom j] [IsAffineHom j.opensRange.ι]
  [HasFiniteBiproducts (QCoh X)]
  (Φ : QCoh X ⥤ CochainComplex (QCoh X) ℕ) [Φ.Additive]
  (T : QCoh X ⥤ QCoh X) [T.Additive]
  (n width : ℕ) (retained : n < width)
  (τ : Φ ⟶ singleCoefficient T n)

/-- The same original finite-total augmentation is a quasi-isomorphism
on image-open direct images whenever it is so on the affine chart. -/
theorem reconstructionQuasicoherentOpenRange_topComparison_quasiIso
    (localQuasiIso : ∀ J : CochainComplex (QCoh U) ℤ,
      QuasiIso ((topComparison Φ T n width retained τ).app
        (((quasicoherentAffinePushforward j).mapHomologicalComplex (.up ℤ)).obj J)))
    (K : CochainComplex (QCoh j.opensRange.toScheme) ℤ) :
    QuasiIso ((topComparison Φ T n width retained τ).app
      (((quasicoherentAffinePushforward j.opensRange.ι).mapHomologicalComplex (.up ℤ)).obj K)) :=
  reconstructionOpenRange_quasiIso j _ _ (topComparison Φ T n width retained τ) localQuasiIso K

end ToricPower

end
