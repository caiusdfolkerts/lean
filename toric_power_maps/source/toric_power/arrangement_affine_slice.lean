module

public import ToricPower.ArrangementClosedLinearSlice

/-!
# Integral affine slices in the original arrangement

The local detection argument uses translates of closed linear slices.
Every selected equation has an integral value on the translating
lattice point. Consequently an open cell meeting the affine slice has
its entire closure in it. No refinement of the arrangement is involved.
-/

@[expose] public noncomputable section

open Set

namespace ToricPower.IntegralArrangement

section General

variable {E J : Type*} [AddCommGroup E] [Module ℝ E]
  (forms : J → Module.Dual ℝ E) (selected : Set J) (z : E)

def arrangementAffineSlice : Set E :=
  {x | x - z ∈ arrangementZeroSlice forms selected}

theorem mem_arrangementAffineSlice (x : E) :
    x ∈ arrangementAffineSlice forms selected z ↔
      ∀ j ∈ selected, forms j x = forms j z := by
  simp only [arrangementAffineSlice,Set.mem_setOf_eq,mem_arrangementZeroSlice,
    map_sub,sub_eq_zero]

/-- Integer levels are unions of actual closed cells, just as the
zero level is. The proof includes cells on equality walls. -/
theorem closedCell_subset_affineSlice_of_meets
    (integral : ∀ j ∈ selected, ∃ r : ℤ, forms j z = (r : ℝ))
    (e : J → ℤ) (active : Set J) {x : E}
    (inCell : x ∈ cell forms e active)
    (inSlice : x ∈ arrangementAffineSlice forms selected z) :
    closedCell forms e active ⊆ arrangementAffineSlice forms selected z := by
  intro y hy
  rw [mem_arrangementAffineSlice]
  intro j selectedj
  obtain ⟨r,level⟩ := integral j selectedj
  have same := (mem_arrangementAffineSlice forms selected z x).mp inSlice j selectedj
  have atLevel : forms j x = (r : ℝ) := same.trans level
  have ceiling : e j = r := by
    rw [← ceil_eq_of_mem_cell forms e active inCell j,atLevel,Int.ceil_intCast]
  have activej : j ∈ active := by
    rw [← integralIndices_eq_of_mem_cell forms e active inCell]
    change forms j x = (⌈forms j x⌉ : ℝ)
    rw [atLevel,Int.ceil_intCast]
  have value := hy j
  rw [if_pos activej,ceiling] at value
  exact value.trans level.symm

end General

variable {n s : ℕ} (A : Fin s → Fin n → ℤ)
  (selected : Set (Fin s ⊕ Fin n)) (m : Fin n → ℤ)

local notation "U" => UniversalIncidenceObject A

def universalAffineSliceSupport (c : U) : Prop :=
  universalIncidenceClosedCell A c ⊆
    arrangementAffineSlice (augmentedForms A) selected (latticeLift m)

theorem universalAffineSliceSupport_downward :
    Antitone (universalAffineSliceSupport A selected m) := by
  intro c d below contained x hx
  exact contained (below hx)

theorem universalAffineSliceSupport_iff_center (c : U) :
    universalAffineSliceSupport A selected m c ↔
      cellCenter (augmentedForms A) c.2 ∈
        arrangementAffineSlice (augmentedForms A) selected (latticeLift m) := by
  constructor
  · intro contained
    exact contained (cell_subset_closedCell _ _ _ (cellCenter_mem _ c.2))
  · exact closedCell_subset_affineSlice_of_meets (augmentedForms A) selected (latticeLift m)
      (fun j _ => ⟨_,augmentedForms_latticeLift A m j⟩)
      c.2.val.1 c.2.val.2 (cellCenter_mem _ c.2)

/-- The full affine slice is the union of its contained closed cells,
with all lattice translates and all intrinsic dimensions retained. -/
theorem universalAffineSlice_union :
    (⋃ c : {c : U // universalAffineSliceSupport A selected m c},
      universalIncidenceClosedCell A c.val) =
        arrangementAffineSlice (augmentedForms A) selected (latticeLift m) := by
  apply Set.Subset.antisymm
  · intro x hx
    obtain ⟨c,hc⟩ := Set.mem_iUnion.mp hx
    exact c.property hc
  · intro x hx
    let c := universalIncidenceOfPoint A x
    have supported : universalAffineSliceSupport A selected m c :=
      closedCell_subset_affineSlice_of_meets (augmentedForms A) selected (latticeLift m)
        (fun j _ => ⟨_,augmentedForms_latticeLift A m j⟩)
        _ _ (mem_cell_self _ x) hx
    exact Set.mem_iUnion.mpr ⟨⟨c,supported⟩,cell_subset_closedCell _ _ _ (mem_cell_self _ x)⟩

end ToricPower.IntegralArrangement

end
