module

public import ToricPower.WeightedIncidenceGeometry
public import ToricPower.ElementPushdownAdjunction

/-!
# The universal arrangement as the actual lattice covering category

Every quotient-cell incidence translates the full character lattice.
Its category of elements is explicitly equivalent to the weighted
incidence category and to the genuine universal face category. The
equivalences retain the specified negative-translation convention.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Set

namespace ToricPower.IntegralArrangement

variable {n s : ℕ} (A : Fin s → Fin n → ℤ)

local notation "C" => IncidenceObject A
local notation "W" => WeightedIncidenceObject A
local notation "U" => UniversalIncidenceObject A

/-- The complete lattice of sheets, with the actual incidence translation. -/
def universalWeightFunctor : C ⥤ Type where
  obj _ := Fin n → ℤ
  map f := ↾(fun m => m + f.val)
  map_id c := by
    apply ConcreteCategory.hom_ext
    intro m
    exact add_zero m
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    intro m
    exact (add_assoc m f.val g.val).symm

/-- The fiber maps are genuine permutations of the full lattice. -/
theorem universalWeightFunctor_map_bijective {c d : C} (f : c ⟶ d) :
    Function.Bijective ((universalWeightFunctor A).map f) := by
  change Function.Bijective (fun m : Fin n → ℤ => m + f.val)
  constructor
  · intro m m' h
    exact add_right_cancel h
  · intro m
    exact ⟨m - f.val,sub_add_cancel m f.val⟩

/-- The weighted presentation and the element presentation have exactly
the same objects and the same translated incidences. -/
def weightedToElements : W ⥤ (universalWeightFunctor A).Elements where
  obj c := (universalWeightFunctor A).elementsMk c.1 c.2
  map f := ⟨f.val,f.property.symm⟩
  map_id _ := rfl
  map_comp _ _ := rfl

def elementsToWeighted : (universalWeightFunctor A).Elements ⥤ W where
  obj c := (c.obj,c.val)
  map f := ⟨f.hom,f.map_val.symm⟩
  map_id _ := rfl
  map_comp _ _ := rfl

instance : (elementsToWeighted A).Faithful where
  map_injective h := by
    apply Elements.hom_ext
    exact congrArg Subtype.val h

def weightedElementsEquivalence : W ≌ (universalWeightFunctor A).Elements where
  functor := weightedToElements A
  inverse := elementsToWeighted A
  unitIso := NatIso.ofComponents (fun _ => Iso.refl _) (by
    intros
    exact Subsingleton.elim _ _)
  counitIso := NatIso.ofComponents (fun _ => Iso.refl _) (by
    intros
    apply (elementsToWeighted A).map_injective
    exact Subsingleton.elim _ _)
  functor_unitIso_comp _ := by simp

/-- The canonical inverse chooses the original normalized cell and its
literal integral translation, rather than a new representative. -/
def cellsToWeighted : U ⥤ W where
  obj := (weightedIncidenceCellEquiv A).symm
  map {c d} f := weightedIncidenceOfClosedCellSubset A (by
    change universalIncidenceClosedCell A
        ((weightedIncidenceCellEquiv A) ((weightedIncidenceCellEquiv A).symm c)) ⊆
      universalIncidenceClosedCell A
        ((weightedIncidenceCellEquiv A) ((weightedIncidenceCellEquiv A).symm d))
    have contained : universalIncidenceClosedCell A c ⊆
        universalIncidenceClosedCell A d := f.le
    simpa only [Equiv.apply_symm_apply] using contained)
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

/-- This explicit equivalence has the literal normalization inverse. -/
def weightedExplicitCellEquivalence : W ≌ U where
  functor := weightedIncidenceToCells A
  inverse := cellsToWeighted A
  unitIso := NatIso.ofComponents
    (fun c => eqToIso (by
      change c = (weightedIncidenceCellEquiv A).symm ((weightedIncidenceCellEquiv A) c)
      exact ((weightedIncidenceCellEquiv A).symm_apply_apply c).symm))
    (by intros; exact Subsingleton.elim _ _)
  counitIso := NatIso.ofComponents
    (fun c => eqToIso (by
      change (weightedIncidenceCellEquiv A) ((weightedIncidenceCellEquiv A).symm c) = c
      exact (weightedIncidenceCellEquiv A).apply_symm_apply c))
    (by intros; exact Subsingleton.elim _ _)
  functor_unitIso_comp _ := Subsingleton.elim _ _

/-- The genuine universal face category is the full lattice covering. -/
def universalCoverElementsEquivalence : U ≌ (universalWeightFunctor A).Elements :=
  (weightedExplicitCellEquivalence A).symm.trans (weightedElementsEquivalence A)

/-- The actual map to the quotient incidence category. -/
def universalCoverProjection : U ⥤ C :=
  (universalCoverElementsEquivalence A).functor ⋙ Elements.π (universalWeightFunctor A)

/-- The geometric carrier of the explicit inverse is exactly the
original universal cell, with no enlargement or change of dimension. -/
theorem cellsToWeighted_closedCell (c : U) :
    weightedIncidenceClosedCell A ((cellsToWeighted A).obj c) =
      universalIncidenceClosedCell A c := by
  dsimp only [cellsToWeighted,weightedIncidenceClosedCell]
  rw [Equiv.apply_symm_apply]

end ToricPower.IntegralArrangement

end
