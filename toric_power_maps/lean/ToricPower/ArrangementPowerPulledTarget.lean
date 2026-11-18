module

public import ToricPower.ArrangementPowerCoverComponents
public import ToricPower.BaseRestrictionComparison
public import ToricPower.CoveringDetectionTransfer

/-! # The full target on the actual pulled-back universal covering -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor

namespace ToricPower.IntegralArrangement

variable {n s : ℕ} (A : Fin s → Fin n → ℤ) (ell : ℕ) (positive : 0 < ell)
  (R : Type) [CommRing R]

/-- Forgetting the residue retains exactly the original entire weighted
diagram, including its translated incidence arrows. -/
def powerPulledWeightedProjectionIso :
    ElementPushdown.pullbackElements (Elements.π (powerResidueFunctor A ell positive))
        (universalWeightFunctor A) ⋙ elementsToWeighted A ≅
      powerUniversalToWeighted A ell positive :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intros
    exact Subsingleton.elim _ _)

def powerPulledWeightedCoefficientIso :
    ElementPushdown.baseRestriction (elementsToWeighted A) (D := ModuleCat.{0} R) ⋙
      ElementPushdown.pullbackCoefficient (Elements.π (powerResidueFunctor A ell positive))
        (universalWeightFunctor A) (D := ModuleCat.{0} R) ≅
    ElementPushdown.baseRestriction (powerUniversalToWeighted A ell positive)
      (D := ModuleCat.{0} R) :=
  ElementPushdown.baseRestrictionCompIso
      (ElementPushdown.pullbackElements (Elements.π (powerResidueFunctor A ell positive))
        (universalWeightFunctor A)) (elementsToWeighted A) ≪≫
    ElementPushdown.baseRestrictionCongrIso (powerPulledWeightedProjectionIso A ell positive)

local instance powerTargetDerivedWeighted :
    HasDerivedCategory.{1} (WeightedIncidenceObject A ⥤ ModuleCat.{0} R) :=
  HasDerivedCategory.standard _
local instance powerTargetDerivedUniversal :
    HasDerivedCategory.{1} ((universalWeightFunctor A).Elements ⥤ ModuleCat.{0} R) :=
  HasDerivedCategory.standard _
local instance powerTargetDerivedPulled :
    HasDerivedCategory.{1} (PowerUniversalObject A ell positive ⥤ ModuleCat.{0} R) :=
  HasDerivedCategory.standard _

/-- The comparison is between the specified original complex and the
specified whole-cover pullback, before making any support truncation. -/
def powerPulledWeightedDerivedIso
    (K : CochainComplex (WeightedIncidenceObject A ⥤ ModuleCat.{0} R) ℤ) :
    (ElementPushdown.baseRestriction (powerUniversalToWeighted A ell positive)
      (D := ModuleCat.{0} R)).mapDerivedCategory.obj (DerivedCategory.Q.obj K) ≅
    DerivedCategory.Q.obj (pulledCoveringComplex (universalWeightFunctor A)
      (powerResidueFunctor A ell positive) R
      (((ElementPushdown.baseRestriction (elementsToWeighted A) (D := ModuleCat.{0} R)).mapHomologicalComplex (.up ℤ)).obj K)) :=
  (ElementPushdown.baseRestriction (powerUniversalToWeighted A ell positive)
      (D := ModuleCat.{0} R)).mapDerivedCategoryFactors.app K ≪≫
    DerivedCategory.Q.mapIso
      ((Functor.mapHomologicalComplexCompIso
        (powerPulledWeightedCoefficientIso A ell positive R) (.up ℤ)).app K).symm

end ToricPower.IntegralArrangement

end
