module

public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory

/-!
# Actual finite-model comparison for the homotopy inverse-Nakayama functor

The comparison is ordinary additive functoriality of complexes followed
by actual localization. Its naturality follows from the unique lift in
the K-injective homotopy category. No right-derived comparison is assumed.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CochainComplex

namespace ToricPower

universe u v w u' v' w'
variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
  {B : Type u'} [Category.{v'} B] [Abelian B] [HasDerivedCategory.{w'} B]

/-- The natural comparison for an arbitrary actual additive functor. -/
def homotopyDerivedComplexIso (F : A ⥤ B) [F.Additive] :
    HomotopyCategory.quotient A (.up ℤ) ⋙ F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh ≅
      F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (F.mapHomotopyCategoryFactors (.up ℤ)) DerivedCategory.Qh ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (F.mapHomologicalComplex (.up ℤ))
      (DerivedCategory.quotientCompQhIso B)

end ToricPower

end
