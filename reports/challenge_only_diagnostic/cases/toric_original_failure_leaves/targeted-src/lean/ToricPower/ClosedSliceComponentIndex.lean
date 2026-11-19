module

public import ToricPower.LinearSliceLatticeComponents

/-! # The full closed-row support split into its integral components

The coverage premise concerns literal points in the real universal
cover. In the toric application it is supplied by the proved regular
cone lattice-extension theorem. The resulting equivalence retains
every component, every supported cell, and every lattice character.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Topology Set

namespace ToricPower.IntegralArrangement

variable {n s : ℕ} (A : Fin s → Fin n → ℤ)
  (zeroRows : Set (Fin s ⊕ Fin n))

local notation "L" => arrangementZeroSlice (augmentedForms A) zeroRows

theorem cellLevel_mem_integralSliceValues {q : ℕ} (c : Cell (augmentedForms A) q)
    (active : zeroRows ⊆ c.val.2)
    (covered : ∃ a : Fin n → ℤ, cellCenter (augmentedForms A) c-latticeLift a ∈ L) :
    (fun j : zeroRows => c.val.1 j.val) ∈ (integralSliceRowMap A zeroRows).range := by
  obtain ⟨a,ha⟩ := covered
  refine ⟨a,?_⟩
  funext j
  have zero := (mem_arrangementZeroSlice (augmentedForms A) zeroRows _).mp ha j.val j.property
  have value := cellCenter_mem (augmentedForms A) c j.val
  rw [if_pos (active j.property)] at value
  rw [map_sub,augmentedForms_latticeLift,value] at zero
  change augmentedLatticePairing A a j.val = c.val.1 j.val
  exact_mod_cast (sub_eq_zero.mp zero).symm

def ClosedRowsSupportCell (U : OpenCellSupport A) (q : ℕ) :=
  {c : Cell (augmentedForms A) q //
    zeroRows ⊆ c.val.2 ∧ cellCenter (augmentedForms A) c ∈ U.val}

variable (U : OpenCellSupport A)
  (covered : ∀ {q : ℕ} (c : Cell (augmentedForms A) q), zeroRows ⊆ c.val.2 →
    ∃ a : Fin n → ℤ, cellCenter (augmentedForms A) c-latticeLift a ∈
      arrangementZeroSlice (augmentedForms A) zeroRows)

def closedRowsCellValue {q : ℕ} (c : ClosedRowsSupportCell A zeroRows U q) :
    IntegralSliceValue A zeroRows :=
  ⟨fun j => c.val.val.1 j.val,
    cellLevel_mem_integralSliceValues A zeroRows c.val c.property.1
      (covered c.val c.property.1)⟩

def closedRowsCellValueFiberEquiv (value : IntegralSliceValue A zeroRows) (q : ℕ) :
    {c : ClosedRowsSupportCell A zeroRows U q //
      closedRowsCellValue A zeroRows U covered c = value} ≃
      SliceComponentCell A zeroRows U value q where
  toFun c := ⟨c.val.val,⟨c.val.property.1,fun j =>
    congrArg (fun v : IntegralSliceValue A zeroRows => v.val j) c.property⟩,c.val.property.2⟩
  invFun c := ⟨⟨c.val,c.property.1.1,c.property.2⟩,by
    apply Subtype.ext
    funext j
    exact c.property.1.2 j⟩
  left_inv _ := Subtype.ext (Subtype.ext rfl)
  right_inv _ := Subtype.ext rfl

/-- The unrestricted component decomposition, at the actual cell level. -/
def closedRowsCellComponentsEquiv (q : ℕ) :
    ClosedRowsSupportCell A zeroRows U q ≃
      Σ value : IntegralSliceValue A zeroRows,
        SliceSupportCell A zeroRows
          (shiftedOpenCellSupport A U (sliceValueRepresentative A zeroRows value)) q :=
  (Equiv.sigmaFiberEquiv (closedRowsCellValue A zeroRows U covered)).symm.trans
    (Equiv.sigmaCongrRight fun value =>
      (closedRowsCellValueFiberEquiv A zeroRows U covered value q).trans
        (sliceComponentCellEquiv A zeroRows U value q))

omit U covered in
/-- Original incidence cannot change the selected integral levels:
the whole characteristic boundary stays in the same affine component. -/
theorem closedRows_incidence_levels {p q : ℕ}
    (c : Cell (augmentedForms A) p) (d : Cell (augmentedForms A) q)
    (activeC : zeroRows ⊆ c.val.2) (activeD : zeroRows ⊆ d.val.2)
    (face : closedCell (augmentedForms A) c.val.1 c.val.2 ⊆
      closedCell (augmentedForms A) d.val.1 d.val.2) (j : zeroRows) :
    c.val.1 j.val = d.val.1 j.val := by
  have source := cellCenter_mem (augmentedForms A) c j.val
  have target := face (cell_subset_closedCell _ _ _ (cellCenter_mem _ c)) j.val
  rw [if_pos (activeC j.property)] at source
  rw [if_pos (activeD j.property)] at target
  exact_mod_cast source.symm.trans target

end ToricPower.IntegralArrangement

end
