module

public import ToricPower.ArrangementLocalMorse
public import ToricPower.ComplexHomDiagramPresentation
public import Mathlib.CategoryTheory.Abelian.FunctorCategory

/-! # Whole Morse predicates for the two intrinsic Hom presentations

This comparison retains the actual Morse functor and its actual scalar
presentation. The source category, label diagram and complex are abstract,
and the same additive witness is used at the affine-assembly boundary.
-/

@[expose] public noncomputable section

open CategoryTheory

attribute [local instance 2000] Abelian.toPreadditive
attribute [local instance 2000] Preadditive.preadditiveHasZeroMorphisms

namespace ToricPower.IntegralArrangement

variable {n s : ℕ} (A : Fin s → Fin n → ℤ)
  (c : UniversalIncidenceObject A) (region : Set (Fin n → ℝ))
  {C : Type*} [Category.{0} C] [Preadditive C] [Linear ℂ C]

theorem universalLocalMorse_complexHom_acyclic_iff
    (P : (UniversalIncidenceObject A)ᵒᵖ ⥤ C)
    [canonicalAdditive : (Cellular.complexHomDiagram P).Additive]
    (K : CochainComplex C ℤ) :
    ((universalLocalMorse A ℂ c region).obj
      (((Cellular.complexHomDiagram P).mapHomologicalComplex (.up ℤ)).obj K)).Acyclic ↔
    ((universalLocalMorse A ℂ c region).obj
      (((Cellular.homDiagram ℂ P).mapHomologicalComplex (.up ℤ)).obj K)).Acyclic :=
  Iff.rfl

end ToricPower.IntegralArrangement
end
