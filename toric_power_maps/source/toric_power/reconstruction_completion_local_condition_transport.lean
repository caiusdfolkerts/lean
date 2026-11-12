module

public import ToricPower.ReconstructionCompletionSchemeAffineDerivedBridge

/-! # The original affine condition before toric specialization

The top-comparison map and its finite-total presentation are the same
actual augmentation. Their exact affine predicates are identified while
the scheme, cover, and coefficient functors remain abstract.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace ToricPower

variable (X : Scheme) {J : Type} {I : Type*} [Category.{0} J]
  (V : I → X.Opens) [∀ i, IsAffineHom (V i).ι]
  (H : QCoh X ⥤ (J ⥤ @ModuleCat.{0} ℂ Complex.commRing.toRing)) [H.Additive]
  (Φ : (J ⥤ ModuleCat.{0} ℂ) ⥤ CochainComplex (QCoh X) ℕ) [Φ.Additive]
  (T : QCoh X ⥤ QCoh X) [T.Additive]
  (n width : ℕ) (retained : n < width)
  (τ : H ⋙ Φ ⟶ T ⋙ HomologicalComplex.single (QCoh X) (.up ℕ) n)

local instance reconstructionLocalConditionBiproducts : HasFiniteBiproducts (QCoh X) :=
  HasFiniteBiproducts.of_hasFiniteProducts

/-- The original top augmentation on every unbounded affine direct image. -/
def schemeAffineTopComparisonCondition : Prop :=
  ∀ (i : I) (K : CochainComplex (QCoh (V i).toScheme) ℤ),
    QuasiIso ((FunctorTotal.topComparison (H ⋙ Φ) T n width retained τ).app
      (((quasicoherentAffinePushforward (V i).ι).mapHomologicalComplex (.up ℤ)).obj K))

/-- The proved original affine top condition is the exact condition used
by the derived reconstruction through the finite affine coresolution. -/
theorem schemeAffineLocalCondition_of_topComparison
    (localQuasiIso : schemeAffineTopComparisonCondition X V H Φ T n width retained τ) :
    schemeAffineLocalReconstructionCondition X V H Φ T n width retained τ := by
  intro i K
  simpa only [FunctorTotal.reconstructionComplexTopComparison_app] using localQuasiIso i K

end ToricPower

end
