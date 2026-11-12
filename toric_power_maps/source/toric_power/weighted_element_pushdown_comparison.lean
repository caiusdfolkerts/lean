module

public import ToricPower.ArrangementUniversalCover
public import ToricPower.WeightedIncidenceComplexPushdown
public import ToricPower.BaseRestrictionComparison

/-!
# The literal weighted sum is the genuine covering direct image

The comparison uses the universal property of the full dependent
finitely-supported module. On every vector inclusion it is the original
coproduct inclusion, so all translated incidence maps are retained.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

namespace ToricPower.IntegralArrangement

variable {n s : ℕ} (A : Fin s → Fin n → ℤ) (R : Type) [CommRing R]

private theorem singleMap_decidable_independent {I : Type} (M : I → ModuleCat.{0} R)
    (d d' : DecidableEq I) (i : I) :
    (letI := d; ModuleCat.ofHom (DFinsupp.lsingle (R := R) (M := fun j => ↑(M j)) i)) =
    (letI := d'; ModuleCat.ofHom (DFinsupp.lsingle (R := R) (M := fun j => ↑(M j)) i)) := by
  cases Subsingleton.elim d d'
  rfl

/-- The original full direct-sum module and its categorical coproduct. -/
def weightedElementCellIso (F : WeightedIncidenceObject A ⥤ ModuleCat.{0} R)
    (c : IncidenceObject A) :
    weightedPushdownCell A R F c ≅
      ElementPushdown.cell (universalWeightFunctor A)
        ((ElementPushdown.baseRestriction (elementsToWeighted A)).obj F) c :=
  ModuleDirectSum.sumColimitIso R (Discrete.functor
    (fun m : (universalWeightFunctor A).obj c =>
      ((ElementPushdown.baseRestriction (elementsToWeighted A)).obj F).obj
        ((universalWeightFunctor A).elementsMk c m)))

@[reassoc]
theorem weightedElementCellIso_inclusion
    (F : WeightedIncidenceObject A ⥤ ModuleCat.{0} R)
    (c : IncidenceObject A) (m : Fin n → ℤ) :
    weightedPushdownInclusion A R F c m ≫ (weightedElementCellIso A R F c).hom =
      ElementPushdown.inclusion (universalWeightFunctor A)
        ((ElementPushdown.baseRestriction (elementsToWeighted A)).obj F) c m := by
  letI : DecidableEq (Fin n → ℤ) := fun a b => Classical.propDecidable (a = b)
  let H := Discrete.functor (fun m : (universalWeightFunctor A).obj c =>
    ((ElementPushdown.baseRestriction (elementsToWeighted A)).obj F).obj
      ((universalWeightFunctor A).elementsMk c m))
  have h := ModuleDirectSum.sumColimitIso_inclusion R H m
  have inclusion : weightedPushdownInclusion A R F c m =
      (ModuleCat.ofHom (DFinsupp.lsingle (R := R)
        (M := fun j : Fin n → ℤ => ↑(H.obj ⟨j⟩)) m)) :=
    singleMap_decidable_independent R (fun j => F.obj (c,j)) _ _ m
  rw [inclusion]
  exact h

/-- The scalar comparison retains every genuine quotient incidence. -/
def weightedElementObjectIso (F : WeightedIncidenceObject A ⥤ ModuleCat.{0} R) :
    (weightedPushdown A R).obj F ≅
      (ElementPushdown.functor (universalWeightFunctor A)).obj
        ((ElementPushdown.baseRestriction (elementsToWeighted A)).obj F) :=
  NatIso.ofComponents (weightedElementCellIso A R F) (by
    intro c d f
    apply weightedPushdown_hom_ext A R F c
    intro m
    change weightedPushdownInclusion A R F c m ≫ weightedPushdownMap A R F f ≫
        (weightedElementCellIso A R F d).hom =
      weightedPushdownInclusion A R F c m ≫ (weightedElementCellIso A R F c).hom ≫
        ElementPushdown.map (universalWeightFunctor A)
          ((ElementPushdown.baseRestriction (elementsToWeighted A)).obj F) f
    rw [weightedPushdownMap_inclusion_assoc,weightedElementCellIso_inclusion,
      weightedElementCellIso_inclusion_assoc,ElementPushdown.inclusion_map]
    rfl)

/-- A natural isomorphism of actual coefficient functors. -/
def weightedElementPushdownIso :
    weightedPushdown A R ≅
      ElementPushdown.baseRestriction (elementsToWeighted A) ⋙
        ElementPushdown.functor (universalWeightFunctor A) :=
  NatIso.ofComponents (weightedElementObjectIso A R) (by
    intro F G α
    apply NatTrans.ext
    funext c
    apply weightedPushdown_hom_ext A R F c
    intro m
    change weightedPushdownInclusion A R F c m ≫ weightedPushdownCellMap A R α c ≫
        (weightedElementCellIso A R G c).hom =
      weightedPushdownInclusion A R F c m ≫ (weightedElementCellIso A R F c).hom ≫
        ElementPushdown.cellMap (universalWeightFunctor A)
          ((ElementPushdown.baseRestriction (elementsToWeighted A)).map α) c
    rw [weightedPushdownCellMap_inclusion_assoc,weightedElementCellIso_inclusion,
      weightedElementCellIso_inclusion_assoc,ElementPushdown.inclusion_cellMap]
    rfl)

end ToricPower.IntegralArrangement

end
