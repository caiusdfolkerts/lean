module

public import ToricPower.HomotopyDerivedComplexComparison
public import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated
public import Mathlib.Algebra.Homology.DerivedCategory.Linear

/-!
# Applying an additive functor on homotopy classes and then localizing

This presentation retains the literal mapped complex as its object.
Its comparison with the standard homotopy functor proves exactness;
the quotient lift proves independence of every chain-map representative.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

namespace ToricPower

universe u v w u' v' w' r
variable {A : Type u} [Category.{v} A] [Abelian A]
  {B : Type u'} [Category.{v'} B] [Abelian B] [HasDerivedCategory.{w'} B]
  (F : A ⥤ B) [F.Additive]

/-- Actual quotient lift with the original mapped complex as its value. -/
def additiveHomotopyDerived : HomotopyCategory A (.up ℤ) ⥤ DerivedCategory B :=
  CategoryTheory.Quotient.lift (homotopic A (.up ℤ))
    (F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (fun _ _ f g ⟨h⟩ => DerivedCategory.Q_map_eq_of_homotopy B (F.mapHomotopy h))

def additiveHomotopyDerivedFactors :
    HomotopyCategory.quotient A (.up ℤ) ⋙ additiveHomotopyDerived F ≅
      F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
  CategoryTheory.Quotient.lift.isLift _ _ _

/-- The exactness comparison is made at the functor level. -/
def additiveHomotopyDerivedIso :
    F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh ≅ additiveHomotopyDerived F :=
  CategoryTheory.Quotient.natIsoLift (homotopic A (.up ℤ))
    (homotopyDerivedComplexIso F ≪≫ (additiveHomotopyDerivedFactors F).symm)

instance additiveHomotopyDerived_commShift : (additiveHomotopyDerived F).CommShift ℤ :=
  Functor.CommShift.ofIso (additiveHomotopyDerivedIso F) ℤ

instance additiveHomotopyDerivedIso_commShift :
    NatTrans.CommShift (additiveHomotopyDerivedIso F).hom ℤ :=
  Functor.CommShift.ofIso_compatibility _ _

instance additiveHomotopyDerived_isTriangulated : (additiveHomotopyDerived F).IsTriangulated :=
  Functor.isTriangulated_of_iso (additiveHomotopyDerivedIso F)

instance additiveHomotopyDerived_linear (k : Type r) [CommRing k]
    [Linear k A] [Linear k B] [F.Linear k] : (additiveHomotopyDerived F).Linear k :=
  Functor.linear_of_iso k (additiveHomotopyDerivedIso F)

@[simp]
theorem additiveHomotopyDerived_obj_quotient (K : CochainComplex A ℤ) :
    (additiveHomotopyDerived F).obj ((HomotopyCategory.quotient A (.up ℤ)).obj K) =
      DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj K) := rfl

@[simp]
theorem additiveHomotopyDerived_map_quotient {K L : CochainComplex A ℤ} (f : K ⟶ L) :
    (additiveHomotopyDerived F).map ((HomotopyCategory.quotient A (.up ℤ)).map f) =
      DerivedCategory.Q.map ((F.mapHomologicalComplex (.up ℤ)).map f) := rfl

end ToricPower
end
