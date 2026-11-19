module

public import ToricPower.ReconstructionCompletionNativeCoefficientCondition

/-! # The original single-coefficient target in the affine condition

The target of the original augmentation is retained as the complete
single-coefficient functor while the scheme and coefficient functors
remain abstract. This seals its presentation before specialization.
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
  (τ : H ⋙ Φ ⟶ FunctorTotal.singleCoefficient T n)

local instance reconstructionNativeSingleConditionBiproducts :
    HasFiniteBiproducts (QCoh X) := HasFiniteBiproducts.of_hasFiniteProducts

/-- The original single-coefficient presentation gives the same native
local-family requirement and the same named all-open condition. -/
def reconstructionAffineTopCondition_of_nativeSingle :=
  reconstructionAffineTopCondition_of_nativeComposition
    X V H Φ T n width retained τ

end ToricPower

end
