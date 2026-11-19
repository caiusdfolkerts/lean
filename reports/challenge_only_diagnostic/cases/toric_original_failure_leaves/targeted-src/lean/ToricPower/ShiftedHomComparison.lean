module

public import Mathlib.CategoryTheory.Shift.Adjunction
public import Mathlib.CategoryTheory.Adjunction.Additive

/-! # The additive Hom comparison for opposite source and target shifts -/

@[expose] public noncomputable section

open CategoryTheory

namespace ToricPower

variable {D : Type*} [Category* D] [Preadditive D] [HasShift D ℤ]
  [∀ q : ℤ, (shiftFunctor D q).Additive]

/-- The genuine shift adjunction, including its additive zero map. -/
def shiftedHomAddEquiv (X Y : D) (q : ℤ) :
    (X⟦-q⟧ ⟶ Y) ≃+ (X ⟶ Y⟦q⟧) := by
  letI : (shiftEquiv D q).symm.functor.Additive :=
    inferInstanceAs ((shiftFunctor D (-q)).Additive)
  letI : (shiftEquiv D q).symm.inverse.Additive :=
    inferInstanceAs ((shiftFunctor D q).Additive)
  exact (shiftEquiv D q).symm.toAdjunction.homAddEquiv X Y

end ToricPower

end
