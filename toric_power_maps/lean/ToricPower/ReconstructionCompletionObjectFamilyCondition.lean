module

public import ToricPower.ReconstructionCompletionAffineUnitFamily

/-! # A comparison on an abstract family of objects

The complete source, target, and complex shape are inferred from the
original natural transformation before its rank-one family is packaged.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace ToricPower

section Abstract

variable {I : Type*} {A : Type*} {B : Type*} {ι : Type*} [Category* A] [Category* B]
  [HasZeroMorphisms B] [CategoryWithHomology B]
  {c : ComplexShape ι} {F G : A ⥤ HomologicalComplex B c}
  (objects : I → A) (τ : F ⟶ G)

/-- The given natural transformation is a quasi-isomorphism on every
object in the specified family, in its original complex category. -/
def reconstructionObjectFamilyCondition : Prop :=
  ∀ i, QuasiIso (τ.app (objects i))

/-- Package the original family with all categories and the complex
shape abstract. -/
def reconstructionObjectFamilyCondition_of_quasiIso
    (localQuasiIso : ∀ i, QuasiIso (τ.app (objects i))) :
    reconstructionObjectFamilyCondition objects τ :=
  localQuasiIso

end Abstract

section Affine

variable {I : Type*} (U : I → Scheme.{0}) (X : Scheme.{0})
  (j : ∀ i, U i ⟶ X) [∀ i, IsAffineHom (j i)]
  {F G : QCoh X ⥤ CochainComplex (QCoh X) ℕ} (τ : F ⟶ G)

/-- The abstract object-family condition is exactly the original named
affine unit condition, before any toric data is substituted. -/
theorem reconstructionAffineUnitFamilyCondition_of_objectFamily
    (h : reconstructionObjectFamilyCondition
      (fun i => quasicoherentAffineUnitImage (j i)) τ) :
    reconstructionAffineUnitFamilyCondition U X j τ :=
  h

end Affine

end ToricPower

end
