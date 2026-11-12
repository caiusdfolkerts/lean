module

public import ToricPower.LinearSliceOpenCoordinates
public import Mathlib.Logic.Equiv.Sum

/-! # All integral translates of the actual closed linear slice

Connected components are indexed by the image of the full integral row
map, rather than by an arbitrarily chosen finite lattice quotient. A
representative only chooses coordinates on each component. Translation
identifies its actual original cells with the zero slice and the
translated open chart support.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Topology Set

namespace ToricPower.IntegralArrangement

variable {n s : ℕ} (A : Fin s → Fin n → ℤ)
  (zeroRows : Set (Fin s ⊕ Fin n))

local notation "L" => arrangementZeroSlice (augmentedForms A) zeroRows

def integralSliceRowMap : (Fin n → ℤ) →+ (zeroRows → ℤ) where
  toFun a j := augmentedLatticePairing A a j.val
  map_zero' := by ext j; simp
  map_add' a b := by ext j; simp

abbrev IntegralSliceValue := (integralSliceRowMap A zeroRows).range

def sliceValueRepresentative (value : IntegralSliceValue A zeroRows) : Fin n → ℤ :=
  Classical.choose value.property

theorem sliceValueRepresentative_values (value : IntegralSliceValue A zeroRows)
    (j : zeroRows) :
    augmentedLatticePairing A (sliceValueRepresentative A zeroRows value) j.val = value.val j :=
  congrFun (Classical.choose_spec value.property) j

theorem cellCenter_mem_zeroSlice_iff {q : ℕ} (c : Cell (augmentedForms A) q) :
    cellCenter (augmentedForms A) c ∈ L ↔
      zeroRows ⊆ c.val.2 ∧ ∀ j : zeroRows, c.val.1 j.val = 0 := by
  constructor
  · intro member
    have zeros := (mem_arrangementZeroSlice (augmentedForms A) zeroRows _).mp member
    constructor
    · intro j hj
      rw [← integralIndices_eq_of_mem_cell (augmentedForms A) _ _ (cellCenter_mem _ c)]
      change augmentedForms A j (cellCenter (augmentedForms A) c) =
        (⌈augmentedForms A j (cellCenter (augmentedForms A) c)⌉ : ℝ)
      rw [zeros j hj,Int.ceil_zero,Int.cast_zero]
    · intro j
      rw [← ceil_eq_of_mem_cell (augmentedForms A) _ _ (cellCenter_mem _ c) j.val,
        zeros j.val j.property,Int.ceil_zero]
  · rintro ⟨active,zero⟩
    rw [mem_arrangementZeroSlice]
    intro j hj
    have point := cellCenter_mem (augmentedForms A) c j
    rw [if_pos (active hj),zero ⟨j,hj⟩,Int.cast_zero] at point
    exact point

/-- The open set `U-a`, with its genuine inherited cellwise property. -/
def shiftedOpenCellSupport (U : OpenCellSupport A) (a : Fin n → ℤ) : OpenCellSupport A :=
  ⟨⟨(fun x => x+latticeLift a) ⁻¹' (U.val : Set (Fin n → ℝ)),
    U.val.isOpen.preimage (by fun_prop)⟩,by
      intro e active x y hx hy
      exact U.property _ _
        ((add_mem_cell_iff _ _ _ _ _ (augmentedForms_latticeLift A a) x).mpr hx)
        ((add_mem_cell_iff _ _ _ _ _ (augmentedForms_latticeLift A a) y).mpr hy)⟩

theorem translateCell_support_iff (U : OpenCellSupport A) (a : Fin n → ℤ)
    {q : ℕ} (c : Cell (augmentedForms A) q) :
    cellCenter (augmentedForms A) (translateCell A a c) ∈ U.val ↔
      cellCenter (augmentedForms A) c ∈ (shiftedOpenCellSupport A U a).val := by
  exact U.property _ _ (cellCenter_mem _ _)
    ((add_mem_cell_iff _ _ _ _ _ (augmentedForms_latticeLift A a) _).mpr
      (cellCenter_mem _ c))

def SliceComponentCell (U : OpenCellSupport A) (value : IntegralSliceValue A zeroRows) (q : ℕ) :=
  {c : Cell (augmentedForms A) q //
    (zeroRows ⊆ c.val.2 ∧ ∀ j : zeroRows, c.val.1 j.val = value.val j) ∧
      cellCenter (augmentedForms A) c ∈ U.val}

/-- Every lattice component is reindexed by the original cells of the
zero slice, with the full translated chart support. -/
def sliceComponentCellEquiv (U : OpenCellSupport A) (value : IntegralSliceValue A zeroRows)
    (q : ℕ) :
    SliceComponentCell A zeroRows U value q ≃
      SliceSupportCell A zeroRows
        (shiftedOpenCellSupport A U (sliceValueRepresentative A zeroRows value)) q where
  toFun c := ⟨⟨translateCell A (-sliceValueRepresentative A zeroRows value) c.val,by
    rw [cellCenter_mem_zeroSlice_iff]
    refine ⟨c.property.1.1,?_⟩
    intro j
    change c.val.val.1 j.val +
      augmentedLatticePairing A (-sliceValueRepresentative A zeroRows value) j.val = 0
    rw [augmentedLatticePairing_neg,Pi.neg_apply,c.property.1.2 j,
      sliceValueRepresentative_values,add_neg_cancel]⟩,by
    apply (translateCell_support_iff A U (sliceValueRepresentative A zeroRows value) _).mp
    simpa only [translateCell_add,neg_add_cancel,translateCell_zero] using c.property.2⟩
  invFun c := ⟨translateCell A (sliceValueRepresentative A zeroRows value) c.val.val,by
    obtain ⟨active,zero⟩ := (cellCenter_mem_zeroSlice_iff A zeroRows c.val.val).mp c.val.property
    refine ⟨⟨active,?_⟩,(translateCell_support_iff A U _ c.val.val).mpr c.property⟩
    intro j
    change c.val.val.val.1 j.val +
      augmentedLatticePairing A (sliceValueRepresentative A zeroRows value) j.val = value.val j
    rw [zero j,zero_add,sliceValueRepresentative_values]⟩
  left_inv c := by
    apply Subtype.ext
    simp only [translateCell_add,neg_add_cancel,translateCell_zero]
  right_inv c := by
    apply Subtype.ext
    apply Subtype.ext
    simp only [translateCell_add,add_neg_cancel,translateCell_zero]

end ToricPower.IntegralArrangement

end
