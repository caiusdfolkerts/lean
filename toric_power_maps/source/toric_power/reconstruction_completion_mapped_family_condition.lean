module

public import ToricPower.ReconstructionCompletionMappedCondition
public import ToricPower.ReconstructionCompletionNativeSingleCondition

/-! # Named mapped comparisons give the original affine condition

The original named comparison is converted to the exact reconstruction
condition while the coefficient and target functors remain abstract.
The input retains its named predicate on every unbounded affine complex.
-/

@[expose] public noncomputable section

set_option maxRecDepth 4096
set_option maxHeartbeats 800000
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace ToricPower

variable (X : Scheme.{0}) {J : Type} {I : Type*} [Category.{0} J]
  (V : I → X.Opens) [∀ i, IsAffineHom (V i).ι]
  (H : QCoh X ⥤ (J ⥤ @ModuleCat.{0} ℂ Complex.commRing.toRing)) [H.Additive]
  (Φ : (J ⥤ ModuleCat.{0} ℂ) ⥤ CochainComplex (QCoh X) ℕ) [Φ.Additive]
  (T : QCoh X ⥤ QCoh X) [T.Additive]
  (n width : ℕ) (retained : n < width)
  (τ : H ⋙ Φ ⟶ FunctorTotal.singleCoefficient T n)

local instance reconstructionMappedFamilyConditionBiproducts :
    HasFiniteBiproducts (QCoh X) := HasFiniteBiproducts.of_hasFiniteProducts

/-- The original named mapped-input comparisons supply the exact named
all-affine reconstruction condition, with no change of coefficient maps. -/
def reconstructionAffineTopCondition_of_mappedFamily
    (localQuasiIso : ∀ i : I,
      reconstructionMappedTopComparisonCondition (V i).toScheme X
        (quasicoherentAffinePushforward (V i).ι)
        (reconstructionNativeCoefficientComposition X H Φ) T n width retained τ) :=
  reconstructionAffineTopCondition_of_nativeSingle X V H Φ T n width retained τ
    (fun i => (reconstructionMappedTopComparisonCondition_iff (V i).toScheme X
      (quasicoherentAffinePushforward (V i).ι)
      (reconstructionNativeCoefficientComposition X H Φ) T n width retained τ).mp
        (localQuasiIso i))

end ToricPower

end
