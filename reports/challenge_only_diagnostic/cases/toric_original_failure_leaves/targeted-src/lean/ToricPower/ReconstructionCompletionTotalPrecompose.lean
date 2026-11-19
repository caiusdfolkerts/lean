module

public import ToricPower.FiniteFunctorTotalMap

/-! # Precomposition of the genuine finite total

The signed finite total of a composite coefficient functor is the same
complex as first mapping the input and then taking the finite total.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

namespace ToricPower.FunctorTotal

variable {A C B : Type*} [Category* A] [Preadditive A]
  [Category* C] [Preadditive C] [Category* B] [Preadditive B]
  [HasFiniteBiproducts B]
  (H : A ⥤ C) [H.Additive]
  (Φ : C ⥤ CochainComplex B ℕ) [Φ.Additive]

/-- This identity comparison retains every original horizontal and
vertical differential, including the finite-total signs. -/
def precomposeIso (width : ℕ) :
    H.mapHomologicalComplex (.up ℤ) ⋙ functor Φ width ≅
      functor (H ⋙ Φ) width := Iso.refl _

end ToricPower.FunctorTotal

end
