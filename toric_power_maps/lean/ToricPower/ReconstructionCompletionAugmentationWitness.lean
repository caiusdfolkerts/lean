module

public import ToricPower.ReconstructionCompletionAffineUnitFamily
public import ToricPower.FiniteFunctorTotalSingle

/-! # A checked presentation witness for the original augmentation

The witness contains the original map, its equality to that map, and
the proved affine-unit family. Its opacity controls reduction only;
the value and both proofs are supplied and checked by the kernel.
-/

public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace ToricPower

variable (X : Scheme.{0})
  {F : QCoh X ⥤ CochainComplex (QCoh X) ℕ}
  (T : QCoh X ⥤ QCoh X) (n : ℕ)
  (τ : F ⟶ T ⋙ HomologicalComplex.single (QCoh X) (.up ℕ) n)
  {I : Type*} (U : I → Scheme.{0}) (j : ∀ i, U i ⟶ X)
  [∀ i, IsAffineHom (j i)]
  (h : reconstructionAffineUnitFamilyCondition U X j τ)

/-- A kernel-checked witness whose presented augmentation is exactly
the original map and has the already-proved unit comparisons. -/
opaque reconstructionAugmentationWitness :
    {σ : F ⟶ FunctorTotal.singleCoefficient T n //
      σ = τ ∧ ∀ i, QuasiIso (σ.app (quasicoherentAffineUnitImage (j i)))} :=
  ⟨τ, rfl, h⟩

/-- The map carried by the checked presentation witness. -/
abbrev reconstructionAugmentationWitnessMap :
    F ⟶ FunctorTotal.singleCoefficient T n :=
  (reconstructionAugmentationWitness X T n τ U j h).val

/-- The presented map is propositionally equal to the original map. -/
theorem reconstructionAugmentationWitnessMap_eq :
    reconstructionAugmentationWitnessMap X T n τ U j h = τ :=
  (reconstructionAugmentationWitness X T n τ U j h).property.1

/-- The witness supplies the original unrestricted affine-unit family. -/
theorem reconstructionAugmentationWitnessMap_family :
    ∀ i, QuasiIso ((reconstructionAugmentationWitnessMap X T n τ U j h).app
      (quasicoherentAffineUnitImage (j i))) :=
  (reconstructionAugmentationWitness X T n τ U j h).property.2

end ToricPower

end
