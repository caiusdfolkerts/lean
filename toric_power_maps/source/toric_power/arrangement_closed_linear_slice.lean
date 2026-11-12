module

public import ToricPower.ArrangementFaceIntersections

/-! # Closed linear slices already adapted to the integral arrangement

A subspace cut out by a selected family of zero arrangement equations
is a literal union of complete closed cells. Any open cell meeting it
has its whole closure inside it. Thus the constant object on this closed
slice has a genuine downward-closed cell support in the original face
category, without a proposed or implicit refinement.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Set

namespace ToricPower.IntegralArrangement

section General

variable {E J : Type*} [AddCommGroup E] [Module ℝ E]
  (forms : J → Module.Dual ℝ E) (selected : Set J)

def arrangementZeroSlice : Submodule ℝ E :=
  ⨅ j ∈ selected, LinearMap.ker (forms j)

theorem mem_arrangementZeroSlice (x : E) :
    x ∈ arrangementZeroSlice forms selected ↔ ∀ j ∈ selected, forms j x = 0 := by
  simp only [arrangementZeroSlice,Submodule.mem_iInf,LinearMap.mem_ker]

/-- An integer zero equation is either absent from an open cell or
holds on the entire closed cell. -/
theorem closedCell_subset_zeroSlice_of_meets (e : J → ℤ) (active : Set J)
    {x : E} (inCell : x ∈ cell forms e active)
    (inSlice : x ∈ arrangementZeroSlice forms selected) :
    closedCell forms e active ⊆ arrangementZeroSlice forms selected := by
  intro y hy
  change y ∈ arrangementZeroSlice forms selected
  rw [mem_arrangementZeroSlice]
  intro j selectedj
  have zero := (mem_arrangementZeroSlice forms selected x).mp inSlice j selectedj
  have ceiling : e j = 0 := by
    rw [← ceil_eq_of_mem_cell forms e active inCell j,zero,Int.ceil_zero]
  have activej : j ∈ active := by
    rw [← integralIndices_eq_of_mem_cell forms e active inCell]
    change forms j x = (⌈forms j x⌉ : ℝ)
    rw [zero,Int.ceil_zero,Int.cast_zero]
  have value := hy j
  rw [if_pos activej,ceiling,Int.cast_zero] at value
  exact value

end General

variable {n s : ℕ} (A : Fin s → Fin n → ℤ) (selected : Set (Fin s ⊕ Fin n))

local notation "U" => UniversalIncidenceObject A

def universalZeroSliceSupport (c : U) : Prop :=
  universalIncidenceClosedCell A c ⊆ arrangementZeroSlice (augmentedForms A) selected

theorem universalZeroSliceSupport_downward : Antitone (universalZeroSliceSupport A selected) := by
  intro c d below contained x hx
  exact contained (below hx)

theorem universalZeroSliceSupport_iff_center (c : U) :
    universalZeroSliceSupport A selected c ↔
      cellCenter (augmentedForms A) c.2 ∈ arrangementZeroSlice (augmentedForms A) selected := by
  constructor
  · intro contained
    exact contained (cell_subset_closedCell _ _ _ (cellCenter_mem _ c.2))
  · exact closedCell_subset_zeroSlice_of_meets (augmentedForms A) selected
      c.2.val.1 c.2.val.2 (cellCenter_mem _ c.2)

/-- The closed slice is covered by exactly its genuinely contained
arrangement cells, rather than by cells merely touching the slice. -/
theorem universalZeroSlice_union :
    (⋃ c : {c : U // universalZeroSliceSupport A selected c},
      universalIncidenceClosedCell A c.val) =
        (arrangementZeroSlice (augmentedForms A) selected : Set (Fin n → ℝ)) := by
  apply Set.Subset.antisymm
  · intro x hx
    obtain ⟨c,hc⟩ := Set.mem_iUnion.mp hx
    exact c.property hc
  · intro x hx
    let c := universalIncidenceOfPoint A x
    have supported : universalZeroSliceSupport A selected c :=
      closedCell_subset_zeroSlice_of_meets (augmentedForms A) selected _ _
        (mem_cell_self _ x) hx
    exact Set.mem_iUnion.mpr ⟨⟨c,supported⟩,cell_subset_closedCell _ _ _ (mem_cell_self _ x)⟩

end ToricPower.IntegralArrangement

end
