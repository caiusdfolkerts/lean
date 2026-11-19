module

public import ToricPower.BaseRestrictionComparison

/-! # Composition of genuine restrictions on unbounded derived diagrams -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Functor

namespace ToricPower.ElementPushdown

variable {C D E X : Type} [SmallCategory C] [SmallCategory D]
  [SmallCategory E] [SmallCategory X] (R : Type) [CommRing R]

local instance restrictionDerivedC : HasDerivedCategory.{1} (C ⥤ ModuleCat.{0} R) :=
  HasDerivedCategory.standard _
local instance restrictionDerivedD : HasDerivedCategory.{1} (D ⥤ ModuleCat.{0} R) :=
  HasDerivedCategory.standard _
local instance restrictionDerivedE : HasDerivedCategory.{1} (E ⥤ ModuleCat.{0} R) :=
  HasDerivedCategory.standard _
local instance restrictionDerivedX : HasDerivedCategory.{1} (X ⥤ ModuleCat.{0} R) :=
  HasDerivedCategory.standard _

/-- The comparison descends the original identity on coefficients. -/
def derivedBaseRestrictionCompIso (F : C ⥤ D) (G : D ⥤ E) :
    (baseRestriction G (D := ModuleCat.{0} R)).mapDerivedCategory ⋙
        (baseRestriction F (D := ModuleCat.{0} R)).mapDerivedCategory ≅
      (baseRestriction (F ⋙ G) (D := ModuleCat.{0} R)).mapDerivedCategory :=
  Functor.mapDerivedCategoryCompIso _ _ ≪≫
    exactDerivedFunctorIso (baseRestrictionCompIso F G)

/-- Three original restrictions, without any objectwise choice. -/
def derivedBaseRestrictionTripleIso (F : C ⥤ D) (G : D ⥤ E) (H : E ⥤ X) :
    (baseRestriction H (D := ModuleCat.{0} R)).mapDerivedCategory ⋙
        (baseRestriction G (D := ModuleCat.{0} R)).mapDerivedCategory ⋙
        (baseRestriction F (D := ModuleCat.{0} R)).mapDerivedCategory ≅
      (baseRestriction (F ⋙ G ⋙ H) (D := ModuleCat.{0} R)).mapDerivedCategory :=
  Functor.isoWhiskerLeft (baseRestriction H (D := ModuleCat.{0} R)).mapDerivedCategory
      (derivedBaseRestrictionCompIso R F G) ≪≫
    derivedBaseRestrictionCompIso R (F ⋙ G) H

end ToricPower.ElementPushdown

end
