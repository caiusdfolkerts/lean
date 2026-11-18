module

public import Mathlib.Algebra.Homology.HomotopyCategory

/-! # Descent of an actual comparison to the homotopy category

The quotient is full.  A natural comparison of the pullbacks of two
homotopy functors therefore descends with its original components.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace ToricPower

universe u v w z

variable {A : Type u} [Category.{v} A] [Preadditive A]
  {D : Type w} [Category.{z} D]
  (F G : HomotopyCategory A (.up ℤ) ⥤ D)
  (a : HomotopyCategory.quotient A (.up ℤ) ⋙ F ⟶
    HomotopyCategory.quotient A (.up ℤ) ⋙ G)

/-- The descended comparison, obtained from the actual natural map on
complexes using fullness of precomposition by the quotient. -/
def homotopyComparisonOfComplex : F ⟶ G :=
  ((Functor.whiskeringLeft _ _ D).obj
    (HomotopyCategory.quotient A (.up ℤ))).preimage a

@[simp]
theorem homotopyComparisonOfComplex_app (K : CochainComplex A ℤ) :
    (homotopyComparisonOfComplex F G a).app
      ((HomotopyCategory.quotient A (.up ℤ)).obj K) = a.app K := by
  exact NatTrans.congr_app
    (((Functor.whiskeringLeft _ _ D).obj
      (HomotopyCategory.quotient A (.up ℤ))).map_preimage a) K

end ToricPower

end
