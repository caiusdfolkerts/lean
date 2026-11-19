module

public import ToricPower.ClosedSliceCellularDifferential
public import ToricPower.ClosedSliceComponentIndex
public import ToricPower.LinearSliceCompactDifferential

/-! # The actual closed-slice differential preserves every integral component

The closed support has all integral row values. A nonzero original
cellular incidence preserves those values. On a fixed value, integral
translation gives the original differential on the zero slice; its
characteristic-disk orientation is unchanged.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Topology Set
open scoped Classical

namespace ToricPower.IntegralArrangement

variable {n s : ℕ} (A : Fin s → Fin n → ℤ)
  (selected : Set (Fin s ⊕ Fin n))

local instance closedComponentIncidenceCW : CWComplex (arrangementCarrier A) :=
  periodicArrangementCWComplex A

/-- The literal open chart support, with its proved open and cellwise properties. -/
def closedSliceChartSupport (S : Set (Fin s)) : OpenCellSupport A :=
  ⟨⟨openWeightRegion (augmentedForms A) (Sum.inl '' S) (augmentedLatticePairing A 0),
    openWeightRegion_isOpen (augmentedForms A) (Sum.inl '' S)
      (augmentedLatticePairing A 0)⟩,
    openWeightRegion_cellwise (augmentedForms A) (Sum.inl '' S)
      (augmentedLatticePairing A 0)⟩

variable (U : OpenCellSupport A)
  (covered : ∀ {q : ℕ} (c : Cell (augmentedForms A) q), selected ⊆ c.val.2 →
    ∃ a : Fin n → ℤ, cellCenter (augmentedForms A) c-latticeLift a ∈
      arrangementZeroSlice (augmentedForms A) selected)

/-- The coordinate inverse retains the actual translated original cell. -/
theorem closedRowsCellComponentsEquiv_symm_val (q : ℕ)
    (value : IntegralSliceValue A selected)
    (c : SliceSupportCell A selected
      (shiftedOpenCellSupport A U (sliceValueRepresentative A selected value)) q) :
    ((closedRowsCellComponentsEquiv A selected U covered q).symm ⟨value,c⟩).val =
      translateCell A (sliceValueRepresentative A selected value) c.val.val := rfl

theorem closedRowsCellComponentsEquiv_symm_value (q : ℕ)
    (value : IntegralSliceValue A selected)
    (c : SliceSupportCell A selected
      (shiftedOpenCellSupport A U (sliceValueRepresentative A selected value)) q) :
    closedRowsCellValue A selected U covered
      ((closedRowsCellComponentsEquiv A selected U covered q).symm ⟨value,c⟩) = value := by
  exact ((closedRowsCellValueFiberEquiv A selected U covered value q).symm
    ((sliceComponentCellEquiv A selected U value q).symm c)).property

variable (k : Type) [Field k]

/-- A literal nonzero incidence remains in the same integral component. -/
theorem closedRowsCellValue_eq_of_incidence_ne_zero (q : ℕ)
    (c : ClosedRowsSupportCell A selected U q)
    (d : ClosedRowsSupportCell A selected U (q+1))
    (nonzero : TauCeti.cellularIncidence (arrangementCarrier A) k q c.val d.val ≠ 0) :
    closedRowsCellValue A selected U covered c = closedRowsCellValue A selected U covered d := by
  apply Subtype.ext
  funext row
  have source := cellCenter_mem (augmentedForms A) c.val row.val
  have target := point_mem_closedCell_of_incidence_ne_zero A k c.val d.val nonzero
    (cellCenter_mem (augmentedForms A) c.val) row.val
  rw [if_pos (c.property.1 row.property)] at source
  rw [if_pos (d.property.1 row.property)] at target
  exact_mod_cast source.symm.trans target

/-- Different parallel components have zero actual incidence coefficient. -/
theorem closedRowsCellComponents_incidence_of_ne (q : ℕ)
    (value other : IntegralSliceValue A selected) (different : value ≠ other)
    (c : SliceSupportCell A selected
      (shiftedOpenCellSupport A U (sliceValueRepresentative A selected value)) q)
    (d : SliceSupportCell A selected
      (shiftedOpenCellSupport A U (sliceValueRepresentative A selected other)) (q+1)) :
    TauCeti.cellularIncidence (arrangementCarrier A) k q
      ((closedRowsCellComponentsEquiv A selected U covered q).symm ⟨value,c⟩).val
      ((closedRowsCellComponentsEquiv A selected U covered (q+1)).symm ⟨other,d⟩).val = 0 := by
  by_contra nonzero
  apply different
  have same := closedRowsCellValue_eq_of_incidence_ne_zero A selected U covered k q
    ((closedRowsCellComponentsEquiv A selected U covered q).symm ⟨value,c⟩)
    ((closedRowsCellComponentsEquiv A selected U covered (q+1)).symm ⟨other,d⟩) nonzero
  simpa only [closedRowsCellComponentsEquiv_symm_value] using same

/-- Within every component the genuine orientation and sign agree
with the compact-support cochain complex on the translated zero slice. -/
theorem closedRowsCellComponents_incidence_self (q : ℕ)
    (value : IntegralSliceValue A selected)
    (c : SliceSupportCell A selected
      (shiftedOpenCellSupport A U (sliceValueRepresentative A selected value)) q)
    (d : SliceSupportCell A selected
      (shiftedOpenCellSupport A U (sliceValueRepresentative A selected value)) (q+1)) :
    TauCeti.cellularIncidence (arrangementCarrier A) k q
      ((closedRowsCellComponentsEquiv A selected U covered q).symm ⟨value,c⟩).val
      ((closedRowsCellComponentsEquiv A selected U covered (q+1)).symm ⟨value,d⟩).val =
      TauCeti.cellularIncidence (arrangementCarrier A) k q c.val.val d.val.val := by
  rw [closedRowsCellComponentsEquiv_symm_val,closedRowsCellComponentsEquiv_symm_val]
  exact arrangement_cellularIncidence_translate A k (sliceValueRepresentative A selected value)
    q c.val.val d.val.val

omit U in
/-- All actual Laurent indices, regrouped into every parallel component. -/
def closedSliceLaurentComponentsEquiv (S : Set (Fin s)) (q : ℕ) :
    ClosedSliceLaurentIndex A selected S q ≃
      Σ value : IntegralSliceValue A selected,
        SliceSupportCell A selected
          (shiftedOpenCellSupport A (closedSliceChartSupport A S)
            (sliceValueRepresentative A selected value)) q :=
  (closedSliceLaurentCellEquiv A selected S q).trans
    (closedRowsCellComponentsEquiv A selected (closedSliceChartSupport A S) covered q)

end ToricPower.IntegralArrangement

end
