module

public import ToricPower.ReconstructionCompletionNativeCoefficientCondition
public import ToricPower.ReconstructionCompletionAffineUnitFamily

/-! # The coefficient functor in the original Hom scalar category

The cellular functor is presented in the exact scalar category produced
by the original Hom functor before forming their composition. The functor,
augmentation, and all comparison predicates retain their original maps.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace ToricPower

variable (X : Scheme.{0}) {C : Type} [Category.{0} C]
  (Φ : (C ⥤ ModuleCat.{0} ℂ) ⥤ CochainComplex (QCoh X) ℕ)

/-- The original coefficient functor, with the exact scalar domain of
the original Hom functor fixed while the coefficient functor is abstract. -/
abbrev reconstructionCoefficientNativeScalar :
    (C ⥤ @ModuleCat.{0} ℂ Complex.commRing.toRing) ⥤ CochainComplex (QCoh X) ℕ :=
  Φ

theorem reconstructionCoefficientNativeScalar_additive [Φ.Additive] :
    (reconstructionCoefficientNativeScalar X Φ).Additive := by
  infer_instance

theorem reconstructionCoefficientNativeScalar_preservesFiniteLimits
    [PreservesFiniteLimits Φ] :
    PreservesFiniteLimits (reconstructionCoefficientNativeScalar X Φ) := by
  infer_instance

theorem reconstructionCoefficientNativeScalar_preservesColimits
    [PreservesColimitsOfSize.{0, 0} Φ] :
    PreservesColimitsOfSize.{0, 0} (reconstructionCoefficientNativeScalar X Φ) := by
  infer_instance

variable (H : QCoh X ⥤ (C ⥤ @ModuleCat.{0} ℂ Complex.commRing.toRing))

/-- This composition has literally matching middle categories. -/
abbrev reconstructionNativeScalarComposition :
    QCoh X ⥤ CochainComplex (QCoh X) ℕ :=
  H ⋙ reconstructionCoefficientNativeScalar X Φ

theorem reconstructionNativeScalarComposition_additive [H.Additive] [Φ.Additive] :
    (reconstructionNativeScalarComposition X Φ H).Additive := by
  infer_instance

section Augmentation

variable (G : QCoh X ⥤ CochainComplex (QCoh X) ℕ) (τ : H ⋙ Φ ⟶ G)

/-- The identical augmentation with its source composition fixed before
the original Hom functor is specialized to a geometric diagram. -/
abbrev reconstructionAugmentationNativeScalar :
    reconstructionNativeScalarComposition X Φ H ⟶ G :=
  τ

/-- The genuine unit-family condition retains the same components
under the identity presentation of its coefficient functor. -/
theorem reconstructionAffineUnitFamily_nativeScalar_iff
    {I : Type*} (U : I → Scheme.{0}) (j : ∀ i, U i ⟶ X)
    [∀ i, IsAffineHom (j i)] :
    reconstructionAffineUnitFamilyCondition U X j τ ↔
      reconstructionAffineUnitFamilyCondition U X j
        (reconstructionAugmentationNativeScalar X Φ H G τ) :=
  Iff.rfl

end Augmentation

section Condition

variable [H.Additive] [Φ.Additive] {I : Type*}
  (V : I → X.Opens) [∀ i, IsAffineHom (V i).ι]
  (T : QCoh X ⥤ QCoh X) [T.Additive]
  (n width : ℕ) (retained : n < width)
  (τ : H ⋙ Φ ⟶ T ⋙ HomologicalComplex.single (QCoh X) (.up ℕ) n)

/-- The named all-open condition retains the original coefficient
functor and original augmentation after scalar-presentation transport. -/
theorem reconstructionAffineTopCondition_nativeScalar_iff :
    schemeAffineTopComparisonCondition X V H Φ T n width retained τ ↔
      schemeAffineTopComparisonCondition X V H
        (reconstructionCoefficientNativeScalar X Φ) T n width retained
        (reconstructionAugmentationNativeScalar X Φ H _ τ) :=
  Iff.rfl

end Condition

end ToricPower

end
