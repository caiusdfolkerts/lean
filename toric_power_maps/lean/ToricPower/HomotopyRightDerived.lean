module

public import ToricPower.RightKanQuotientDescent
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Functor.Derived.RightDerivedCommShift
public import Mathlib.CategoryTheory.Functor.Derived.RightDerivedTriangulated

/-!
# The right-derived comparison on the homotopy category

For an additive functor, termwise application respects actual chain
homotopies. The comparison from complexes therefore descends through
the homotopy quotient. Its universal property descends as well, so the
derived functor receives its canonical shift comparison from the
triangulated homotopy category.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor

namespace ToricPower

universe u v u' v'

variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory A]
  {B : Type u'} [Category.{v'} B] [Abelian B] [HasDerivedCategory B]
  (H : A ⥤ B) [H.Additive]

/-- The actual factorization of termwise application through the
homotopy quotient and then the derived localization. -/
def homotopyDerivedFactors :
    HomotopyCategory.quotient A (.up ℤ) ⋙
      (H.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh) ≅
    H.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
  (Functor.associator _ _ _).symm ≪≫
    isoWhiskerRight (H.mapHomotopyCategoryFactors (.up ℤ)) DerivedCategory.Qh ≪≫
    Functor.associator _ _ _ ≪≫
    isoWhiskerLeft _ (DerivedCategory.quotientCompQhIso B)

variable (R : DerivedCategory A ⥤ DerivedCategory B)
  (β : H.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ R)

/-- The actual comparison on the homotopy category. -/
def homotopyRightDerivedComparison :
    H.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ R :=
  rightKanQuotientComparison (HomotopyCategory.quotient A (.up ℤ))
    (DerivedCategory.quotientCompQhIso A) (homotopyDerivedFactors H) R β

@[simp]
theorem homotopyRightDerivedComparison_app (K : CochainComplex A ℤ) :
    (homotopyRightDerivedComparison H R β).app
      ((HomotopyCategory.quotient A (.up ℤ)).obj K) =
    (homotopyDerivedFactors H).hom.app K ≫ β.app K ≫
      R.map ((DerivedCategory.quotientCompQhIso A).inv.app K) :=
  rightKanQuotientComparison_app _ _ _ _ _ K

/-- The descended comparison is an isomorphism on every input where
the original comparison was one. -/
theorem homotopyRightDerivedComparison_isIso (K : HomotopyCategory A (.up ℤ))
    [IsIso (β.app K.as)] :
    IsIso ((homotopyRightDerivedComparison H R β).app K) := by
  change IsIso ((homotopyRightDerivedComparison H R β).app
    ((HomotopyCategory.quotient A (.up ℤ)).obj K.as))
  rw [homotopyRightDerivedComparison_app]
  infer_instance

variable [R.IsRightDerivedFunctor β (HomologicalComplex.quasiIso A (.up ℤ))]

/-- Right derivation from complexes descends to right derivation from
the actual homotopy category. -/
theorem homotopyRightDerivedComparison_isRightDerivedFunctor :
    R.IsRightDerivedFunctor (homotopyRightDerivedComparison H R β)
      (HomotopyCategory.quasiIso A (.up ℤ)) := by
  letI := IsRightDerivedFunctor.isLeftKanExtension R β
    (HomologicalComplex.quasiIso A (.up ℤ))
  exact ⟨rightKanQuotientComparison_isLeftKanExtension _ _ _ _ _⟩

/-- The canonical comparison with every integral shift. -/
def homotopyRightDerivedCommShift : R.CommShift ℤ := by
  letI := homotopyRightDerivedComparison_isRightDerivedFunctor H R β
  exact IsRightDerivedFunctor.commShift R (homotopyRightDerivedComparison H R β)
    (HomotopyCategory.quasiIso A (.up ℤ)) ℤ

/-- The descended right-derived unit respects those same shifts. -/
theorem homotopyRightDerivedComparison_commShift :
    letI := homotopyRightDerivedCommShift H R β
    NatTrans.CommShift (homotopyRightDerivedComparison H R β) ℤ := by
  letI := homotopyRightDerivedComparison_isRightDerivedFunctor H R β
  exact IsRightDerivedFunctor.natTrans_commShift R
    (homotopyRightDerivedComparison H R β) (HomotopyCategory.quasiIso A (.up ℤ)) ℤ

end ToricPower

end
