module

public import ToricPower.ReconstructionCompletionAugmentationWitness
public import ToricPower.ReconstructionCompletionLocalConditionTransport

/-! # Returning a checked augmentation witness to the original map

The witness supplies a proof of equality to the original augmentation.
Transport along this equality preserves the exact reconstruction condition.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace ToricPower

variable (X : Scheme.{0}) {C : Type} [Category.{0} C]
  {I : Type*} (U : I → Scheme.{0}) (j : ∀ i, U i ⟶ X)
  [∀ i, IsAffineHom (j i)]
  {A : Type*} (V : A → X.Opens) [∀ a, IsAffineHom (V a).ι]
  (H : QCoh X ⥤ (C ⥤ @ModuleCat.{0} ℂ Complex.commRing.toRing)) [H.Additive]
  (Φ : (C ⥤ ModuleCat.{0} ℂ) ⥤ CochainComplex (QCoh X) ℕ) [Φ.Additive]
  (T : QCoh X ⥤ QCoh X) [T.Additive]
  (n width : ℕ) (retained : n < width)
  (τ : H ⋙ Φ ⟶ T ⋙ HomologicalComplex.single (QCoh X) (.up ℕ) n)
  (unit : reconstructionAffineUnitFamilyCondition U X j τ)

local instance reconstructionWitnessConditionBiproducts :
    HasFiniteBiproducts (QCoh X) := HasFiniteBiproducts.of_hasFiniteProducts

/-- The proved equality of augmentations returns the witness's
all-open reconstruction condition to the literal original map. -/
theorem reconstructionAffineTopCondition_of_augmentationWitness
    (h : schemeAffineTopComparisonCondition X V H Φ T n width retained
      (reconstructionAugmentationWitnessMap X T n τ U j unit)) :
    schemeAffineTopComparisonCondition X V H Φ T n width retained τ := by
  rw [reconstructionAugmentationWitnessMap_eq] at h
  exact h

end ToricPower

end
