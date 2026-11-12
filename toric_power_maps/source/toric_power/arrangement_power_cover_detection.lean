module

public import ToricPower.ArrangementPowerComponentRestriction
public import ToricPower.ArrangementPowerPulledTarget
public import ToricPower.RestrictionEquivalenceComplex
public import ToricPower.ComponentCoverDetection
public import ToricPower.ArrangementPowerPushdown

/-!
# The geometric inverse branch detects the actual power direct image

A nonzero map on the whole universal arrangement is transported through
the explicit weighted equivalence, the selected full residue component,
the full covering product decomposition, and both covering adjunctions.
The final source is the original power-diagram functor. All integral
characters and all finite covering sheets remain present throughout.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor

namespace ToricPower.IntegralArrangement

variable {n s : ℕ} (A : Fin s → Fin n → ℤ) (ell : ℕ) (positive : 0 < ell)
  (k : Type) [Field k]

local instance powerCoverDetectionDerivedCells :
    HasDerivedCategory.{1} (IncidenceObject A ⥤ ModuleCat.{0} k) :=
  HasDerivedCategory.standard _
local instance powerCoverDetectionDerivedWeighted :
    HasDerivedCategory.{1} (WeightedIncidenceObject A ⥤ ModuleCat.{0} k) :=
  HasDerivedCategory.standard _
local instance powerCoverDetectionDerivedUniversal :
    HasDerivedCategory.{1} (UniversalIncidenceObject A ⥤ ModuleCat.{0} k) :=
  HasDerivedCategory.standard _
local instance powerCoverDetectionDerivedElements :
    HasDerivedCategory.{1} ((universalWeightFunctor A).Elements ⥤ ModuleCat.{0} k) :=
  HasDerivedCategory.standard _
local instance powerCoverDetectionDerivedPower :
    HasDerivedCategory.{1} ((powerResidueFunctor A ell positive).Elements ⥤ ModuleCat.{0} k) :=
  HasDerivedCategory.standard _
local instance powerCoverDetectionDerivedPulled :
    HasDerivedCategory.{1} (PowerUniversalObject A ell positive ⥤ ModuleCat.{0} k) :=
  HasDerivedCategory.standard _

/-- Detection passes through the actual power map with its original
incidence carries. Neither the arbitrary source nor the target cochains
are bounded or truncated by this theorem. -/
theorem exists_nonzero_power_pushdown_of_geometric_branch
    (K : CochainComplex (WeightedIncidenceObject A ⥤ ModuleCat.{0} k) ℤ)
    (finite : ∀ (q : ℤ) (c : IncidenceObject A),
      {r : (universalWeightFunctor A).obj c | ¬ IsZero
        (((((ElementPushdown.baseRestriction (elementsToWeighted A)
          (D := ModuleCat.{0} k)).mapHomologicalComplex (.up ℤ)).obj K).homology q).obj
            ((universalWeightFunctor A).elementsMk c r))}.Finite)
    (E : DerivedCategory (IncidenceObject A ⥤ ModuleCat.{0} k))
    (u : Fin n → ℤ) (q : ℤ)
    (f : (ElementPushdown.baseRestriction (powerInverseBranchFunctor A ell positive u)
      (D := ModuleCat.{0} k)).mapDerivedCategory.obj
        ((ElementPushdown.baseRestriction (universalCoverProjection A)
          (D := ModuleCat.{0} k)).mapDerivedCategory.obj E) ⟶
      (DerivedCategory.Q.obj
        (((ElementPushdown.baseRestriction (cellsToWeighted A)
          (D := ModuleCat.{0} k)).mapHomologicalComplex (.up ℤ)).obj K))⟦q⟧)
    (nonzero : f ≠ 0) :
    ∃ g : (powerDerivedPushdown A ell positive k).obj E ⟶
      ((ElementPushdown.functor (universalWeightFunctor A) (D := ModuleCat.{0} k)).mapDerivedCategory.obj (DerivedCategory.Q.obj
          (((ElementPushdown.baseRestriction (elementsToWeighted A)
            (D := ModuleCat.{0} k)).mapHomologicalComplex (.up ℤ)).obj K)))⟦q⟧, g ≠ 0 := by
  let pull := (ElementPushdown.baseRestriction (weightedIncidenceToCells A)
    (D := ModuleCat.{0} k)).mapDerivedCategory
  letI : pull.Faithful := ElementPushdown.restrictionEquivalenceDerived_faithful k
    (weightedExplicitCellEquivalence A)
  let KU := ((ElementPushdown.baseRestriction (cellsToWeighted A)
    (D := ModuleCat.{0} k)).mapHomologicalComplex (.up ℤ)).obj K
  let target := (pull.commShiftIso q).app (DerivedCategory.Q.obj KU) ≪≫
    (shiftFunctor _ q).mapIso (ElementPushdown.restrictionEquivalenceInverseComplexIso k
      (weightedExplicitCellEquivalence A) K)
  let source := (powerComponentGeometricRestrictionIso A ell positive k u).app E
  have mappedNonzero : pull.map f ≠ 0 := by
    intro zero
    apply nonzero
    apply pull.map_injective
    exact zero.trans (pull.map_zero _ _).symm
  have componentNonzero : source.hom ≫ pull.map f ≫ target.hom ≠ 0 := by
    intro zero
    apply mappedNonzero
    rw [← cancel_epi source.hom,← cancel_mono target.hom,Category.assoc,comp_zero,zero_comp]
    exact zero
  let K₀ := ((ElementPushdown.baseRestriction (elementsToWeighted A)
    (D := ModuleCat.{0} k)).mapHomologicalComplex (.up ℤ)).obj K
  let powerSource := (ElementPushdown.baseRestriction (powerBranchFunctor A ell positive)
    (D := ModuleCat.{0} k)).mapDerivedCategory.obj E
  obtain ⟨a,ha⟩ := exists_nonzero_cover_from_component
    (universalWeightFunctor A) (powerResidueFunctor A ell positive) k
    (fun f => universalWeightFunctor_map_bijective A f)
    (powerUniversalComponentsEquivalence A ell positive)
    (powerUniversalToWeighted A ell positive)
    (powerAllComponentsCoefficientIso A ell positive) K₀ K finite
    (powerPulledWeightedDerivedIso A ell positive k K) powerSource
    (latticeResidueOf ell positive (-u)) q (source.hom ≫ pull.map f ≫ target.hom) componentNonzero
  let pushFrame := (Functor.mapDerivedCategoryCompIso
    (ElementPushdown.baseRestriction (powerBranchFunctor A ell positive) (D := ModuleCat.{0} k))
    (ElementPushdown.functor (powerResidueFunctor A ell positive) (D := ModuleCat.{0} k))).app E
  refine ⟨pushFrame.inv ≫ a,?_⟩
  intro zero
  apply ha
  rw [← cancel_epi pushFrame.inv,comp_zero]
  exact zero

end ToricPower.IntegralArrangement

end
