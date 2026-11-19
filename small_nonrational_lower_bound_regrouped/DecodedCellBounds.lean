module

public import LiteralMaskGeometry

@[expose] public section

/-!
# Vertex containment from literal masks

Only the masks actually present in a cell need to be checked. These lemmas
derive the usual finite-set containment statements from those raw checks,
avoiding repeated enumeration of all subsets of the ten vertex labels.
-/

namespace Papers.RationalityTen.DecodedCellBounds

open LiteralMaskGeometry

theorem maskSet_subset_of_land_eq {a b : Nat} (h : Nat.land a b = a) :
    maskSet a ⊆ maskSet b := by
  apply Finset.inter_eq_left.mp
  rw [← maskSet_inter, h]

theorem decoded_edges_subset (C : ConcreteGrowth.Cell)
    (h : C.edges.all (fun e => decide (Nat.land e C.vertices = e)) = true) :
    ∀ e ∈ (decodeCell C).edges, e ⊆ (decodeCell C).vertices := by
  intro e he
  obtain ⟨mask, hm, rfl⟩ := Finset.mem_image.mp he
  have hmask := (List.all_eq_true.mp h) mask (List.mem_toFinset.mp hm)
  exact maskSet_subset_of_land_eq (of_decide_eq_true hmask)

theorem decoded_ridges_subset (C : ConcreteGrowth.Cell)
    (h : C.ridgeMasks.all (fun q => decide (Nat.land q C.vertices = q)) = true) :
    ∀ q ∈ (decodeCell C).ridges, q ⊆ (decodeCell C).vertices := by
  intro q hq
  obtain ⟨mask, hm, rfl⟩ := Finset.mem_image.mp hq
  have hmask := (List.all_eq_true.mp h) mask (List.mem_toFinset.mp hm)
  exact maskSet_subset_of_land_eq (of_decide_eq_true hmask)

#print axioms decoded_edges_subset
#print axioms decoded_ridges_subset

end Papers.RationalityTen.DecodedCellBounds
