module

public import ToricPower.ArrangementUniversalCover
public import ToricPower.ElementSumProductPullback
public import ToricPower.RestrictionEquivalenceComplex

/-!
# Base tests on the full geometric universal cover

The genuine sum-to-product comparison is followed by the actual right
covering adjunction and the explicit cell/element equivalence. Every
integer character and every incidence is retained.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor

namespace ToricPower.IntegralArrangement

variable {n s : ℕ} (A : Fin s → Fin n → ℤ) (R : Type) [CommRing R]

local instance coverTestDerivedBase :
    HasDerivedCategory.{1} (IncidenceObject A ⥤ ModuleCat.{0} R) := HasDerivedCategory.standard _
local instance coverTestDerivedWeighted :
    HasDerivedCategory.{1} (WeightedIncidenceObject A ⥤ ModuleCat.{0} R) := HasDerivedCategory.standard _
local instance coverTestDerivedElements :
    HasDerivedCategory.{1} ((universalWeightFunctor A).Elements ⥤ ModuleCat.{0} R) := HasDerivedCategory.standard _
local instance coverTestDerivedUniversal :
    HasDerivedCategory.{1} (UniversalIncidenceObject A ⥤ ModuleCat.{0} R) := HasDerivedCategory.standard _

def universalCoverWeightedProjectionIso :
    (universalCoverElementsEquivalence A).functor ⋙ elementsToWeighted A ≅ cellsToWeighted A :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by intros; exact Subsingleton.elim _ _)

def universalCoverWeightedCoefficientIso :
    ElementPushdown.baseRestriction (elementsToWeighted A) (D := ModuleCat.{0} R) ⋙
        ElementPushdown.baseRestriction (universalCoverElementsEquivalence A).functor ≅
      ElementPushdown.baseRestriction (cellsToWeighted A) :=
  ElementPushdown.baseRestrictionCompIso _ _ ≪≫
    ElementPushdown.baseRestrictionCongrIso (universalCoverWeightedProjectionIso A)

/-- The complete original target complex in both cover presentations. -/
def universalCoverWeightedDerivedIso
    (K : CochainComplex (WeightedIncidenceObject A ⥤ ModuleCat.{0} R) ℤ) :
    (ElementPushdown.baseRestriction (universalCoverElementsEquivalence A).functor
      (D := ModuleCat.{0} R)).mapDerivedCategory.obj
        (DerivedCategory.Q.obj (((ElementPushdown.baseRestriction (elementsToWeighted A)
          (D := ModuleCat.{0} R)).mapHomologicalComplex (.up ℤ)).obj K)) ≅
      DerivedCategory.Q.obj (((ElementPushdown.baseRestriction (cellsToWeighted A)
        (D := ModuleCat.{0} R)).mapHomologicalComplex (.up ℤ)).obj K) :=
  (ElementPushdown.baseRestriction (universalCoverElementsEquivalence A).functor
    (D := ModuleCat.{0} R)).mapDerivedCategoryFactors.app _ ≪≫
    DerivedCategory.Q.mapIso
      ((Functor.mapHomologicalComplexCompIso (universalCoverWeightedCoefficientIso A R) (.up ℤ)).app K)

/-- Nonzero maps into the entire pushdown give nonzero tests on the
entire geometric cover. The target condition is only cohomological. -/
theorem exists_nonzero_universal_pullback_of_sum
    (K : CochainComplex (WeightedIncidenceObject A ⥤ ModuleCat.{0} R) ℤ)
    (finite : ∀ (q : ℤ) (c : IncidenceObject A),
      {r : (universalWeightFunctor A).obj c | ¬ IsZero
        (((((ElementPushdown.baseRestriction (elementsToWeighted A)
          (D := ModuleCat.{0} R)).mapHomologicalComplex (.up ℤ)).obj K).homology q).obj
            ((universalWeightFunctor A).elementsMk c r))}.Finite)
    (E : DerivedCategory (IncidenceObject A ⥤ ModuleCat.{0} R)) (q : ℤ)
    (f : E ⟶ ((ElementPushdown.functor (universalWeightFunctor A)
      (D := ModuleCat.{0} R)).mapDerivedCategory.obj (DerivedCategory.Q.obj
        (((ElementPushdown.baseRestriction (elementsToWeighted A)
          (D := ModuleCat.{0} R)).mapHomologicalComplex (.up ℤ)).obj K)))⟦q⟧)
    (nonzero : f ≠ 0) :
    ∃ g : (ElementPushdown.baseRestriction (universalCoverProjection A)
      (D := ModuleCat.{0} R)).mapDerivedCategory.obj E ⟶
        (DerivedCategory.Q.obj (((ElementPushdown.baseRestriction (cellsToWeighted A)
          (D := ModuleCat.{0} R)).mapHomologicalComplex (.up ℤ)).obj K))⟦q⟧,
      g ≠ 0 := by
  obtain ⟨a,ha⟩ := ElementComparison.exists_nonzero_pullback_of_sum
    (universalWeightFunctor A) (fun f => universalWeightFunctor_map_bijective A f)
    R _ finite E q f nonzero
  let pull := (ElementPushdown.baseRestriction (universalCoverElementsEquivalence A).functor
    (D := ModuleCat.{0} R)).mapDerivedCategory
  letI : pull.Faithful := ElementPushdown.restrictionEquivalenceDerived_faithful R
    (universalCoverElementsEquivalence A)
  let source := (ElementPushdown.derivedBaseRestrictionCompIso R
    (universalCoverElementsEquivalence A).functor (Elements.π (universalWeightFunctor A))).app E
  let target := (pull.commShiftIso q).app _ ≪≫
    (shiftFunctor _ q).mapIso (universalCoverWeightedDerivedIso A R K)
  refine ⟨source.inv ≫ pull.map a ≫ target.hom,?_⟩
  intro zero
  apply ha
  apply pull.map_injective
  rw [pull.map_zero]
  rw [← cancel_epi source.inv,← cancel_mono target.hom,
    Category.assoc,comp_zero,zero_comp]
  exact zero

end ToricPower.IntegralArrangement

end
