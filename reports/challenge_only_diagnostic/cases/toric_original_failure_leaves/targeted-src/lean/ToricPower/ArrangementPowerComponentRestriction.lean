module

public import ToricPower.ArrangementPowerComponentIdentification
public import ToricPower.BaseRestrictionDerivedComparison
public import ToricPower.EquivalenceComponentDetection

/-!
# The full selected covering component is the geometric inverse branch

The natural comparison includes the original carry characters. It is
proved first for the actual indexing functors and then descends through
their exact restrictions on unrestricted derived diagrams.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor

namespace ToricPower.IntegralArrangement

variable {n s : ℕ} (A : Fin s → Fin n → ℤ) (ell : ℕ) (positive : 0 < ell)

/-- Projection from the original weighted cells agrees with the genuine
universal-cell projection through the specified normalization equivalence. -/
def weightedUniversalProjectionIso :
    weightedIncidenceToCells A ⋙ universalCoverProjection A ≅
      weightedToElements A ⋙ Elements.π (universalWeightFunctor A) :=
  Functor.isoWhiskerRight (weightedExplicitCellEquivalence A).unitIso.symm
    (weightedToElements A ⋙ Elements.π (universalWeightFunctor A))

/-- The exact indexing identity connecting the full covering component
to the original geometric inverse branch. -/
def powerComponentGeometricProjectionIso (u : Fin n → ℤ) :
    powerUniversalIntegralLift A ell positive u ⋙
        Elements.π (Elements.π (powerResidueFunctor A ell positive) ⋙ universalWeightFunctor A) ⋙
        powerBranchFunctor A ell positive ≅
      weightedIncidenceToCells A ⋙ powerInverseBranchFunctor A ell positive u ⋙
        universalCoverProjection A :=
  powerUniversalIntegralLiftBranchIso A ell positive u ≪≫
    Functor.isoWhiskerLeft (weightedPowerBranchFunctor A ell positive u)
      (weightedUniversalProjectionIso A).symm ≪≫
    Functor.isoWhiskerRight (weightedPowerBranchGeometricIso A ell positive u)
      (universalCoverProjection A)

variable (R : Type) [CommRing R]

local instance componentRestrictionDerivedCells :
    HasDerivedCategory.{1} (IncidenceObject A ⥤ ModuleCat.{0} R) :=
  HasDerivedCategory.standard _
local instance componentRestrictionDerivedWeighted :
    HasDerivedCategory.{1} (WeightedIncidenceObject A ⥤ ModuleCat.{0} R) :=
  HasDerivedCategory.standard _
local instance componentRestrictionDerivedUniversal :
    HasDerivedCategory.{1} (UniversalIncidenceObject A ⥤ ModuleCat.{0} R) :=
  HasDerivedCategory.standard _
local instance componentRestrictionDerivedPower :
    HasDerivedCategory.{1} ((powerResidueFunctor A ell positive).Elements ⥤ ModuleCat.{0} R) :=
  HasDerivedCategory.standard _
local instance componentRestrictionDerivedPulled :
    HasDerivedCategory.{1} (PowerUniversalObject A ell positive ⥤ ModuleCat.{0} R) :=
  HasDerivedCategory.standard _

/-- The specified full component and the geometric inverse branch give
isomorphic source functors on all unbounded input diagrams. -/
def powerComponentGeometricRestrictionIso (u : Fin n → ℤ) :
    (ElementPushdown.baseRestriction (powerBranchFunctor A ell positive)
      (D := ModuleCat.{0} R)).mapDerivedCategory ⋙
      (ElementPushdown.restriction
        (Elements.π (powerResidueFunctor A ell positive) ⋙ universalWeightFunctor A)
        (D := ModuleCat.{0} R)).mapDerivedCategory ⋙
      (ElementPushdown.baseRestriction (powerUniversalIntegralLift A ell positive u)
        (D := ModuleCat.{0} R)).mapDerivedCategory ≅
    (ElementPushdown.baseRestriction (universalCoverProjection A)
      (D := ModuleCat.{0} R)).mapDerivedCategory ⋙
      (ElementPushdown.baseRestriction (powerInverseBranchFunctor A ell positive u)
        (D := ModuleCat.{0} R)).mapDerivedCategory ⋙
      (ElementPushdown.baseRestriction (weightedIncidenceToCells A)
        (D := ModuleCat.{0} R)).mapDerivedCategory :=
  ElementPushdown.derivedBaseRestrictionTripleIso R
      (powerUniversalIntegralLift A ell positive u)
      (Elements.π (Elements.π (powerResidueFunctor A ell positive) ⋙ universalWeightFunctor A))
      (powerBranchFunctor A ell positive) ≪≫
    exactDerivedFunctorIso (ElementPushdown.baseRestrictionCongrIso
      (powerComponentGeometricProjectionIso A ell positive u)) ≪≫
    (ElementPushdown.derivedBaseRestrictionTripleIso R (weightedIncidenceToCells A)
      (powerInverseBranchFunctor A ell positive u) (universalCoverProjection A)).symm

end ToricPower.IntegralArrangement

end
