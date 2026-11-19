module

public import ToricPower.ReconstructionCompletionTotalDerivedBridge
public import ToricPower.AffineConeCoresolution
public import Mathlib.Data.Complex.Basic

/-! # The derived reconstruction bridge for quasicoherent coefficient diagrams

The scheme and coefficient category are still abstract here. Their
inherited complex structures are fixed before a toric scheme, its Hom
diagram, and its recursive affine replacement are substituted.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace ToricPower

variable (X : Scheme) {J : Type} [Category.{0} J]
  [HasDerivedCategory.{1} (QCoh X)]
  [HasDerivedCategory.{1} (J ⥤ ModuleCat.{0} ℂ)]

local instance schemeReconstructionBridgeBiproducts : HasFiniteBiproducts (QCoh X) :=
  HasFiniteBiproducts.of_hasFiniteProducts

variable
  (H : QCoh X ⥤ (J ⥤ @ModuleCat.{0} ℂ Complex.commRing.toRing)) [H.Additive]
  (Φ : (J ⥤ ModuleCat.{0} ℂ) ⥤ CochainComplex (QCoh X) ℕ) [Φ.Additive]
  (T : QCoh X ⥤ QCoh X) [T.Additive]
  (n width : ℕ) (retained : n < width)
  (τ : H ⋙ Φ ⟶ FunctorTotal.singleCoefficient T n)
  (R : DerivedCategory (QCoh X) ⥤ DerivedCategory (J ⥤ ModuleCat.{0} ℂ))
  (L : DerivedCategory (J ⥤ ModuleCat.{0} ℂ) ⥤ DerivedCategory (QCoh X))
  (E : DerivedCategory (QCoh X) ⥤ DerivedCategory (QCoh X))
  (S : CochainComplex (QCoh X) ℤ ⥤ CochainComplex (QCoh X) ℤ)

/-- The exact original coefficient factors give the derived isomorphism
once the actual finite-total comparison is a quasi-isomorphism. -/
def schemeDerivedTotalReconstructionOfCoresolution
    (objects : ∀ K : CochainComplex (QCoh X) ℤ, _)
    (sourceFactors : DerivedCategory.Q ⋙ (R ⋙ L) ≅
      S ⋙ H.mapHomologicalComplex (.up ℤ) ⋙
        FunctorTotal.functor Φ width ⋙ DerivedCategory.Q)
    (targetFactors : DerivedCategory.Q ⋙ E ≅
      S ⋙ T.mapHomologicalComplex (.up ℤ) ⋙
        shiftFunctor (CochainComplex (QCoh X) ℤ) (-(n : ℤ)) ⋙ DerivedCategory.Q) :=
  derivedTotalReconstructionOfCoresolution H Φ T n width retained τ R L E S
    (fun K => objects K) sourceFactors targetFactors

end ToricPower

end
