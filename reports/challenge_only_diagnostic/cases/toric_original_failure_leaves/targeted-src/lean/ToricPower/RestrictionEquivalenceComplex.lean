module

public import ToricPower.BaseRestrictionDerivedComparison

/-! # Exact restriction equivalences retain original complex representatives -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor

namespace ToricPower.ElementPushdown

variable {C D : Type} [SmallCategory C] [SmallCategory D]
  (R : Type) [CommRing R] (e : C ≌ D)

local instance restrictionEquivalenceDerivedC : HasDerivedCategory.{1} (C ⥤ ModuleCat.{0} R) :=
  HasDerivedCategory.standard _
local instance restrictionEquivalenceDerivedD : HasDerivedCategory.{1} (D ⥤ ModuleCat.{0} R) :=
  HasDerivedCategory.standard _

local instance restrictionEquivalenceForwardAdditive :
    ((e.congrLeft (E := ModuleCat.{0} R)).functor).Additive := by
  change ((whiskeringLeft D C (ModuleCat.{0} R)).obj e.inverse).Additive
  infer_instance

local instance restrictionEquivalenceInverseAdditive :
    ((e.congrLeft (E := ModuleCat.{0} R)).inverse).Additive := by
  change ((whiskeringLeft C D (ModuleCat.{0} R)).obj e.functor).Additive
  infer_instance

/-- Restriction along an actual equivalence is faithful after localization. -/
theorem restrictionEquivalenceDerived_faithful :
    (baseRestriction e.functor (D := ModuleCat.{0} R)).mapDerivedCategory.Faithful := by
  change ((e.congrLeft (E := ModuleCat.{0} R)).mapDerivedCategory).inverse.Faithful
  infer_instance

/-- Pulling back the genuine mapped representative returns the entire
original complex in the derived category. -/
def restrictionEquivalenceInverseComplexIso
    (K : CochainComplex (C ⥤ ModuleCat.{0} R) ℤ) :
    (baseRestriction e.functor (D := ModuleCat.{0} R)).mapDerivedCategory.obj
      (DerivedCategory.Q.obj
        (((baseRestriction e.inverse (D := ModuleCat.{0} R)).mapHomologicalComplex (.up ℤ)).obj K)) ≅
      DerivedCategory.Q.obj K :=
  (baseRestriction e.functor (D := ModuleCat.{0} R)).mapDerivedCategory.mapIso
      ((baseRestriction e.inverse (D := ModuleCat.{0} R)).mapDerivedCategoryFactors.app K).symm ≪≫
    ((e.congrLeft (E := ModuleCat.{0} R)).mapDerivedCategory.unitIso.app
      (DerivedCategory.Q.obj K)).symm

end ToricPower.ElementPushdown

end
