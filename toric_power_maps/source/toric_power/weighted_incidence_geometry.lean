module

public import ToricPower.ArrangementWeightedIncidence
public import ToricPower.ArrangementUniversalCells
public import ToricPower.ArrangementCostalkCells
public import Mathlib.CategoryTheory.Category.Preorder

/-!
# Weighted incidences are the actual universal arrangement face category

The weight convention sends `(c,m)` to the actual cell `c-m`. A weighted
incidence is equivalent to containment of these closed polyhedra. The
resulting category equivalence retains every universal-cover cell and
its genuine face relation; it is not a finite support truncation.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Set
open scoped Classical

namespace ToricPower.IntegralArrangement

variable {n s : ℕ} (A : Fin s → Fin n → ℤ)

local notation "W" => WeightedIncidenceObject A

/-- The exact sign convention relating a character and its actual cell. -/
def weightedIncidenceCellEquiv : W ≃ UniversalIncidenceObject A where
  toFun c := ⟨c.1.1, translateCell A (-c.2) c.1.2.val⟩
  invFun d := (⟨d.1, normalizeCell A d.2⟩, -coordinateCeilings A d.2)
  left_inv c := by
    rcases c with ⟨⟨q,c⟩,m⟩
    apply Prod.ext
    · change (⟨q, normalizeCell A (translateCell A (-m) c.val)⟩ : IncidenceObject A) = ⟨q,c⟩
      apply congrArg (fun t : NormalizedCell A q => (⟨q,t⟩ : IncidenceObject A))
      rw [normalizeCell_translate]
      apply Subtype.ext
      change translateCell A (-coordinateCeilings A c.val) c.val = c.val
      rw [c.property, neg_zero, translateCell_zero]
    · change -coordinateCeilings A (translateCell A (-m) c.val) = m
      rw [coordinateCeilings_translateCell, c.property, zero_add, neg_neg]
  right_inv d := by
    rcases d with ⟨q,d⟩
    change (⟨q, translateCell A (-(-coordinateCeilings A d)) (normalizeCell A d).val⟩ :
      UniversalIncidenceObject A) = ⟨q,d⟩
    apply congrArg (fun t : Cell (augmentedForms A) q => (⟨q,t⟩ : UniversalIncidenceObject A))
    change translateCell A (-(-coordinateCeilings A d)) (normalizeCell A d).val = d
    rw [neg_neg, translate_normalizeCell]

/-- The literal closed universal cell, with its negative character translate. -/
def weightedIncidenceClosedCell (c : W) : Set (Fin n → ℝ) :=
  universalIncidenceClosedCell A (weightedIncidenceCellEquiv A c)

/-- Translating back gives the literal normalized-cell membership test. -/
theorem mem_weightedIncidenceClosedCell_iff (c : W) (x : Fin n → ℝ) :
    x ∈ weightedIncidenceClosedCell A c ↔
      x + latticeLift c.2 ∈ incidenceClosedCell A c.1 := by
  change x ∈ closedCell (augmentedForms A)
      (translateCell A (-c.2) c.1.2.val).val.1
      (translateCell A (-c.2) c.1.2.val).val.2 ↔
    x + latticeLift c.2 ∈ closedCell (augmentedForms A) c.1.2.val.val.1 c.1.2.val.val.2
  simpa only [latticeLift_neg, sub_neg_eq_add] using
    mem_translatedClosedCell_iff A c.1.2.val (-c.2) x

/-- Every weighted incidence is an actual geometric face inclusion. -/
theorem weightedIncidence_closedCell_subset {c d : W} (f : c ⟶ d) :
    weightedIncidenceClosedCell A c ⊆ weightedIncidenceClosedCell A d := by
  intro x hx
  apply (mem_weightedIncidenceClosedCell_iff A d x).mpr
  have h := f.val.property (x + latticeLift c.2)
    ((mem_weightedIncidenceClosedCell_iff A c x).mp hx)
  have weight : latticeLift d.2 = latticeLift c.2 + latticeLift f.val.val :=
    (congrArg latticeLift f.property).trans (latticeLift_add c.2 f.val.val)
  rw [weight, ← add_assoc]
  exact h

/-- Conversely, every face inclusion supplies its unique actual weighted incidence. -/
def weightedIncidenceOfClosedCellSubset {c d : W}
    (contained : weightedIncidenceClosedCell A c ⊆ weightedIncidenceClosedCell A d) :
    c ⟶ d :=
  ⟨⟨d.2-c.2, by
    intro x hx
    have h : x - latticeLift c.2 ∈ weightedIncidenceClosedCell A c :=
      (mem_weightedIncidenceClosedCell_iff A c _).mpr (by simpa using hx)
    have target := (mem_weightedIncidenceClosedCell_iff A d _).mp (contained h)
    have shift : latticeLift (d.2-c.2) = latticeLift d.2 - latticeLift c.2 := by
      rw [sub_eq_add_neg, latticeLift_add, latticeLift_neg]
      rfl
    rw [shift]
    convert target using 1 <;> abel⟩, by simp [sub_eq_add_neg, add_left_comm]⟩

instance weightedIncidenceHom_subsingleton (c d : W) : Subsingleton (c ⟶ d) := by
  constructor
  intro f g
  apply Subtype.ext
  apply Subtype.ext
  exact add_left_cancel (f.property.symm.trans g.property)

theorem weightedIncidence_nonempty_iff_closedCell_subset (c d : W) :
    Nonempty (c ⟶ d) ↔ weightedIncidenceClosedCell A c ⊆ weightedIncidenceClosedCell A d :=
  ⟨fun ⟨f⟩ => weightedIncidence_closedCell_subset A f,
    fun h => ⟨weightedIncidenceOfClosedCellSubset A h⟩⟩

/-- The genuine functor to the actual universal face category. -/
def weightedIncidenceToCells : W ⥤ UniversalIncidenceObject A where
  obj := weightedIncidenceCellEquiv A
  map f := homOfLE (weightedIncidence_closedCell_subset A f)

instance : (weightedIncidenceToCells A).Faithful where
  map_injective _ := Subsingleton.elim _ _

instance : (weightedIncidenceToCells A).Full where
  map_surjective f :=
    ⟨weightedIncidenceOfClosedCellSubset A f.le, Subsingleton.elim _ _⟩

instance : (weightedIncidenceToCells A).EssSurj where
  mem_essImage c :=
    ⟨(weightedIncidenceCellEquiv A).symm c,
      ⟨eqToIso ((weightedIncidenceCellEquiv A).apply_symm_apply c)⟩⟩

instance : (weightedIncidenceToCells A).IsEquivalence where

/-- No lifted cells or face maps are lost by the weighted presentation. -/
def weightedIncidenceCellCategoryEquivalence : W ≌ UniversalIncidenceObject A :=
  (weightedIncidenceToCells A).asEquivalence

end ToricPower.IntegralArrangement

end
