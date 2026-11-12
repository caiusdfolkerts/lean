module

public import ToricPower.ComplexHomDiagramPresentation
public import ToricPower.MorseCategoryPresentations

/-! # An opaque additive witness for the concrete complex Hom functor

The inherited and abelian target presentations are compared with the
source category and labels abstract. Keeping this proof as a named theorem
prevents a later geometric comparison from expanding a locally constructed
cast between those equal structures.
-/

@[expose] public noncomputable section

open CategoryTheory

attribute [local instance 2000] Abelian.toPreadditive
attribute [local instance 2000] Preadditive.preadditiveHasZeroMorphisms

namespace ToricPower.Cellular

universe v

variable {C : Type} [Category.{0} C]
  {A : Type v} [Category.{0} A] [Preadditive A] [Linear ℂ A]

theorem complexHomDiagram_abelian_additive (P : Cᵒᵖ ⥤ A) :
    (complexHomDiagram P).Additive := by
  simpa only [morseDiagramPreadditivePresentation] using
    (complexHomDiagram_additive P)

end ToricPower.Cellular
end
