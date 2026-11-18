module

public import ToricPower.ClosedSliceComponentIncidence
public import ToricPower.ModuleSumComplexCoordinates

/-! # The actual closed-slice realization as the sum of all parallel components

The isomorphism compares the original cellular complex with the
unrestricted direct sum of the genuine compact-support complexes on
the zero slice. It uses all integral row values, all allowed Laurent
monomials, and the original signed cellular differential.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

open CategoryTheory CategoryTheory.Limits Topology Set
open scoped Classical

namespace ToricPower.IntegralArrangement

variable {n s : ℕ} (A : Fin s → Fin n → ℤ)
  (selected : Set (Fin s ⊕ Fin n)) (S : Set (Fin s))
  (covered : ∀ {q : ℕ} (c : Cell (augmentedForms A) q), selected ⊆ c.val.2 →
    ∃ a : Fin n → ℤ, cellCenter (augmentedForms A) c-latticeLift a ∈
      arrangementZeroSlice (augmentedForms A) selected)
  (k : Type) [Field k]

local instance closedComponentComplexCW : CWComplex (arrangementCarrier A) :=
  periodicArrangementCWComplex A

abbrev ClosedSliceComponentIndex (q : ℕ) :=
  Σ value : IntegralSliceValue A selected,
    SliceSupportCell A selected
      (shiftedOpenCellSupport A (closedSliceChartSupport A S)
        (sliceValueRepresentative A selected value)) q

def closedSliceComponentsCoordinates (q : ℕ) :
    (closedSliceCellularComplex A selected S k).X q ≃ₗ[k]
      (ClosedSliceComponentIndex A selected S q →₀ k) :=
  (closedSliceCellularCoordinates A selected S k q).trans
    (Finsupp.mapDomain.linearEquiv k k
      (closedSliceLaurentComponentsEquiv A selected covered S q))

theorem closedSliceComponentsCoordinates_apply (q : ℕ)
    (x : (closedSliceCellularComplex A selected S k).X q)
    (p : ClosedSliceComponentIndex A selected S q) :
    closedSliceComponentsCoordinates A selected S covered k q x p =
      closedSliceCellularCoordinates A selected S k q x
        ((closedSliceLaurentComponentsEquiv A selected covered S q).symm p) := by
  let e := closedSliceLaurentComponentsEquiv A selected covered S q
  change Finsupp.mapDomain e (closedSliceCellularCoordinates A selected S k q x) p = _
  have h := Finsupp.mapDomain_apply_of_injective e.injective
    (closedSliceCellularCoordinates A selected S k q x) (e.symm p)
  simpa only [Equiv.apply_symm_apply] using h

theorem closedSliceComponentsCoordinates_symm_single (q : ℕ)
    (p : ClosedSliceComponentIndex A selected S q) (r : k) :
    (closedSliceComponentsCoordinates A selected S covered k q).symm (Finsupp.single p r) =
      (closedSliceCellularCoordinates A selected S k q).symm
        (Finsupp.single ((closedSliceLaurentComponentsEquiv A selected covered S q).symm p) r) := by
  apply (closedSliceComponentsCoordinates A selected S covered k q).injective
  rw [LinearEquiv.apply_symm_apply]
  symm
  change Finsupp.mapDomain (closedSliceLaurentComponentsEquiv A selected covered S q)
    ((closedSliceCellularCoordinates A selected S k q)
      ((closedSliceCellularCoordinates A selected S k q).symm _)) = _
  rw [LinearEquiv.apply_symm_apply,Finsupp.mapDomain_single,Equiv.apply_symm_apply]

theorem closedSliceLaurentComponentsEquiv_symm_cell (q : ℕ)
    (p : ClosedSliceComponentIndex A selected S q) :
    closedSliceLaurentCellEquiv A selected S q
      ((closedSliceLaurentComponentsEquiv A selected covered S q).symm p) =
      (closedRowsCellComponentsEquiv A selected (closedSliceChartSupport A S) covered q).symm p :=
  (closedSliceLaurentCellEquiv A selected S q).apply_symm_apply _

theorem closedSliceComponentsCoordinates_d (q : ℕ)
    (p : ClosedSliceComponentIndex A selected S q)
    (t : ClosedSliceComponentIndex A selected S (q+1)) (r : k) :
    closedSliceComponentsCoordinates A selected S covered k (q+1)
      ((closedSliceCellularComplex A selected S k).d q (q+1)
        ((closedSliceComponentsCoordinates A selected S covered k q).symm
          (Finsupp.single p r))) t =
      TauCeti.cellularIncidence (arrangementCarrier A) k q
        ((closedRowsCellComponentsEquiv A selected (closedSliceChartSupport A S)
          covered q).symm p).val
        ((closedRowsCellComponentsEquiv A selected (closedSliceChartSupport A S)
          covered (q+1)).symm t).val * r := by
  rw [closedSliceComponentsCoordinates_symm_single,closedSliceComponentsCoordinates_apply,
    closedSliceCellularCoordinates_d_geometric,
    closedSliceLaurentComponentsEquiv_symm_cell,closedSliceLaurentComponentsEquiv_symm_cell]

omit S covered in
theorem sliceCompactCoordinates_differential_generator
    (U : OpenCellSupport A) (start q : ℕ)
    (c : SliceSupportCell A selected U q)
    (d : SliceSupportCell A selected U (q+1)) (r : k) :
    sliceCompactCoordinates A selected U k start (q+1)
      ((sliceCompactCochainComplex A selected k U start).d q (q+1)
        ((sliceCompactCoordinates A selected U k start q).symm (Finsupp.single c r))) d =
      TauCeti.cellularIncidence (arrangementCarrier A) k q c.val.val d.val.val * r := by
  have single : Finsupp.single c r = r • (Finsupp.single c 1 : _ →₀ k) := by
    rw [Finsupp.smul_single,smul_eq_mul,mul_one]
  rw [single,map_smul,map_smul,map_smul,Finsupp.smul_apply,
    sliceCompactCoordinates_differential_single,smul_eq_mul,mul_comm]

variable (start : IntegralSliceValue A selected → ℕ)

/-- No component is removed, including those with empty chart support. -/
def closedSliceComponentFamily (value : IntegralSliceValue A selected) :
    CochainComplex (ModuleCat.{0} k) ℕ :=
  sliceCompactCochainComplex A selected k
    (shiftedOpenCellSupport A (closedSliceChartSupport A S)
      (sliceValueRepresentative A selected value)) (start value)

def closedSliceComponentSum : CochainComplex (ModuleCat.{0} k) ℕ :=
  ModuleDirectSum.complex k (closedSliceComponentFamily A selected S k start)

abbrev ClosedSliceComponentCell (value : IntegralSliceValue A selected) (q : ℕ) :=
  SliceSupportCell A selected
    (shiftedOpenCellSupport A (closedSliceChartSupport A S)
      (sliceValueRepresentative A selected value)) q

def closedSliceComponentCoordinates (value : IntegralSliceValue A selected) (q : ℕ) :
    ((closedSliceComponentFamily A selected S k start) value).X q ≃ₗ[k]
      (ClosedSliceComponentCell A selected S value q →₀ k) :=
  sliceCompactCoordinates A selected
    (shiftedOpenCellSupport A (closedSliceChartSupport A S)
      (sliceValueRepresentative A selected value)) k (start value) q

def closedSliceComponentSumCoordinates (q : ℕ) :
    (closedSliceComponentSum A selected S k start).X q ≃ₗ[k]
      (ClosedSliceComponentIndex A selected S q →₀ k) :=
  ModuleDirectSum.complexCoordinates k (closedSliceComponentFamily A selected S k start)
    (ClosedSliceComponentCell A selected S)
    (closedSliceComponentCoordinates A selected S k start) q

/-- The genuine closed constant-diagram realization is the complete
sum of the actual compact-support complexes of all parallel slices. -/
def closedSliceCellularComponentIso :
    closedSliceCellularComplex A selected S k ≅ closedSliceComponentSum A selected S k start :=
  cochainIsoOfFreeCoordinates k _ _ (ClosedSliceComponentIndex A selected S)
    (closedSliceComponentsCoordinates A selected S covered k)
    (closedSliceComponentSumCoordinates A selected S k start) (by
      intro q p r
      rcases p with ⟨value,c⟩
      ext t
      rcases t with ⟨other,d⟩
      rw [closedSliceComponentsCoordinates_d]
      by_cases same : other = value
      · subst other
        rw [closedRowsCellComponents_incidence_self]
        exact ((ModuleDirectSum.complexCoordinates_d_single_self k
          (closedSliceComponentFamily A selected S k start)
          (ClosedSliceComponentCell A selected S)
          (closedSliceComponentCoordinates A selected S k start) q (q+1) value c d r).trans
          (sliceCompactCoordinates_differential_generator A selected k _ (start value) q c d r)).symm
      · rw [closedRowsCellComponents_incidence_of_ne A selected
          (closedSliceChartSupport A S) covered k q value other (Ne.symm same),zero_mul]
        exact (ModuleDirectSum.complexCoordinates_d_single_ne k
          (closedSliceComponentFamily A selected S k start)
          (ClosedSliceComponentCell A selected S)
          (closedSliceComponentCoordinates A selected S k start) q (q+1)
          value other same c d r).symm)

end ToricPower.IntegralArrangement

end
