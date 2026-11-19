module
prelude
public import RawFacePlacement

@[expose] public section

namespace Papers.RationalityTen.RootedCellLookup

/-- A checked lookup preserves the complete cell, including its kind.
Only cells of an allowed kind compatible with the root need an image. -/
def check {s t : Nat} (source : Fin s → ConcreteGrowth.Cell)
    (root : ConcreteGrowth.Cell) (target : Fin t → ConcreteGrowth.Cell)
    (allowed : Nat → Bool) (witness : Fin s → Fin t) (i : Fin s) : Bool :=
  (!(allowed (source i).kind && RawFacePlacement.compatible (source i) root)) ||
    (decide ((target (witness i)).kind = (source i).kind) &&
      RawFacetEmbedding.sameGeometry (target (witness i)) (source i))

theorem check_sound {s t : Nat} (source : Fin s → ConcreteGrowth.Cell)
    (root : ConcreteGrowth.Cell) (target : Fin t → ConcreteGrowth.Cell)
    (allowed : Nat → Bool) (witness : Fin s → Fin t) (i : Fin s)
    (h : check source root target allowed witness i = true)
    (ha : allowed (source i).kind = true)
    (hc : RawFacePlacement.compatible (source i) root = true) :
    (target (witness i)).kind = (source i).kind ∧
      RawFacetEmbedding.sameGeometry (target (witness i)) (source i) = true := by
  simp only [check, ha, hc, Bool.true_and, Bool.not_true, Bool.false_or,
    Bool.and_eq_true, decide_eq_true_eq] at h
  exact h

end Papers.RationalityTen.RootedCellLookup
