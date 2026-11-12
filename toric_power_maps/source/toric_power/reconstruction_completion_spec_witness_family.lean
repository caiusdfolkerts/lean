module

public import ToricPower.ReconstructionCompletionAugmentationWitness

/-! # The original unit family over spectra of a family of rings

The source scheme of each unit is written directly as a spectrum.
The family-function beta conversion is checked while both coefficient
functors are abstract, before any geometric Hom functor is substituted.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace ToricPower

variable {I : Type*} (R : I → Type) [∀ i, CommRing (R i)]
  (X : Scheme.{0})
  {F : QCoh X ⥤ CochainComplex (QCoh X) ℕ}
  (T : QCoh X ⥤ QCoh X) (n : ℕ)
  (τ : F ⟶ T ⋙ HomologicalComplex.single (QCoh X) (.up ℕ) n)
  (j : ∀ i, Spec (.of (R i)) ⟶ X) [∀ i, IsAffineHom (j i)]
  (unit : reconstructionAffineUnitFamilyCondition
    (fun i => Spec (.of (R i))) X j τ)

/-- The checked witness's unit comparisons with the exact spectrum
source presentation used by the affine extension theorem. -/
theorem reconstructionAugmentationWitnessMap_familySpec :
    ∀ i, QuasiIso ((reconstructionAugmentationWitnessMap
      (F := F) X T n τ (fun i => Spec (.of (R i))) j unit).app
      (@quasicoherentAffineUnitImage (Spec (.of (R i))) X (j i) inferInstance)) :=
  reconstructionAugmentationWitnessMap_family (F := F) X T n τ
    (fun i => Spec (.of (R i))) j unit

end ToricPower

end
