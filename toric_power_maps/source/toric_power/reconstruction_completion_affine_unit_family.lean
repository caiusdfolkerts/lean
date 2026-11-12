module

public import ToricPower.AffineRankOneSections
public import Mathlib.Algebra.Homology.QuasiIso

/-! # The original affine unit comparison for a scheme family

The rank-one premise has one fixed name before source schemes, direct
images, or the original augmentation are specialized.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace ToricPower

variable {I : Type*} (U : I → Scheme.{0}) (X : Scheme.{0})
  (j : ∀ i, U i ⟶ X) [∀ i, IsAffineHom (j i)]
  {F G : QCoh X ⥤ CochainComplex (QCoh X) ℕ} (τ : F ⟶ G)

/-- The original augmentation is a quasi-isomorphism on the unit direct
image from every chart in the specified source family. -/
def reconstructionAffineUnitFamilyCondition : Prop :=
  ∀ i, QuasiIso (τ.app (quasicoherentAffineUnitImage (j i)))

end ToricPower

end
