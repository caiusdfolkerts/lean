module

public import ToricPower.WeightedElementPushdownComparison
public import ToricPower.ComplexDiagramExtension

/-!
# The original complete weighted complex as a covering direct image

This comparison retains all integral weights, all incidence translations,
and all cochain degrees. Extension from natural to integer degrees is
performed by the actual extension-by-zero functor.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor

namespace ToricPower.IntegralArrangement

variable {n s : ℕ} (A : Fin s → Fin n → ℤ) (R : Type) [CommRing R]

local instance weightedDerivedCoverBase :
    HasDerivedCategory.{1} (IncidenceObject A ⥤ ModuleCat.{0} R) :=
  HasDerivedCategory.standard _
local instance weightedDerivedCoverWeighted :
    HasDerivedCategory.{1} (WeightedIncidenceObject A ⥤ ModuleCat.{0} R) :=
  HasDerivedCategory.standard _
local instance weightedDerivedCoverElements :
    HasDerivedCategory.{1} ((universalWeightFunctor A).Elements ⥤ ModuleCat.{0} R) :=
  HasDerivedCategory.standard _

/-- The full integer-indexed complex on the genuine universal cover. -/
def weightedCoverLiftComplex
    (F : WeightedIncidenceObject A ⥤ CochainComplex (ModuleCat.{0} R) ℕ) :
    CochainComplex ((universalWeightFunctor A).Elements ⥤ ModuleCat.{0} R) ℤ :=
  ((ElementPushdown.baseRestriction (elementsToWeighted A) (D := ModuleCat.{0} R)).mapHomologicalComplex (.up ℤ)).obj
      (complexDiagramTranspose (F ⋙ ComplexShape.embeddingUpNat.extendFunctor (ModuleCat.{0} R)))

/-- The genuine covering direct image is the original full weighted
Čech pushdown, including its original differential and incidence maps. -/
def weightedCoverPushdownIso
    (F : WeightedIncidenceObject A ⥤ CochainComplex (ModuleCat.{0} R) ℕ) :
    (ElementPushdown.functor (universalWeightFunctor A) (D := ModuleCat.{0} R)).mapDerivedCategory.obj (DerivedCategory.Q.obj (weightedCoverLiftComplex A R F)) ≅
      DerivedCategory.Q.obj (complexDiagramTranspose
        (weightedComplexPushdown A R F ⋙
          ComplexShape.embeddingUpNat.extendFunctor (ModuleCat.{0} R))) := by
  let K := complexDiagramTranspose
    (F ⋙ ComplexShape.embeddingUpNat.extendFunctor (ModuleCat.{0} R))
  let pull := ElementPushdown.baseRestriction (elementsToWeighted A) (D := ModuleCat.{0} R)
  let push := ElementPushdown.functor (universalWeightFunctor A) (D := ModuleCat.{0} R)
  exact push.mapDerivedCategory.mapIso (pull.mapDerivedCategoryFactors.app K).symm ≪≫
    (Functor.mapDerivedCategoryCompIso pull push).app (DerivedCategory.Q.obj K) ≪≫
    (exactDerivedFunctorIso (weightedElementPushdownIso A R).symm).app
      (DerivedCategory.Q.obj K) ≪≫
    (weightedPushdown A R).mapDerivedCategoryFactors.app K ≪≫
    DerivedCategory.Q.mapIso
      (complexDiagramMapExtensionIso F ComplexShape.embeddingUpNat (weightedPushdown A R))

end ToricPower.IntegralArrangement

end
