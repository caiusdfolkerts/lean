module

public import ToricPower.ArrangementClosedLinearSlice
public import ToricPower.ArrangementCostalkCellular
public import ToricPower.CWNestedSubcomplex

/-! # The inherited periodic CW structure on an actual linear slice

The slice and its closed complement use the original periodic disks.
The relative pair therefore has exactly the original cells contained
in the slice and in the selected open region.
-/

@[expose] public noncomputable section

open Set Topology

namespace ToricPower.IntegralArrangement

variable {n s : ℕ} (A : Fin s → Fin n → ℤ)
  (zeroRows : Set (Fin s ⊕ Fin n))

local notation "E" => Fin n → ℝ
local notation "V" => arrangementZeroSlice (augmentedForms A) zeroRows

theorem arrangementZeroSlice_cellwise : Cellwise (augmentedForms A) (V : Set E) := by
  intro e active x y hx hy
  constructor
  · intro inside
    exact closedCell_subset_zeroSlice_of_meets (augmentedForms A) zeroRows e active hx inside
      (cell_subset_closedCell _ _ _ hy)
  · intro inside
    exact closedCell_subset_zeroSlice_of_meets (augmentedForms A) zeroRows e active hy inside
      (cell_subset_closedCell _ _ _ hx)

local instance linearSliceAmbientCW : CWComplex (arrangementCarrier A) :=
  periodicArrangementCWComplex A

def periodicLinearSliceSubcomplex : CWComplex.Subcomplex (arrangementCarrier A) :=
  periodicCellwiseSubcomplex A (V : Set E)
    (V).closed_of_finiteDimensional (arrangementZeroSlice_cellwise A zeroRows)

def periodicSliceClosedComplement (region : Set E) (openRegion : IsOpen region)
    (cellwise : Cellwise (augmentedForms A) region) :
    CWComplex.Subcomplex (arrangementCarrier A) :=
  periodicCellwiseSubcomplex A ((V : Set E) ∩ regionᶜ)
    ((V).closed_of_finiteDimensional.inter openRegion.isClosed_compl)
    ((arrangementZeroSlice_cellwise A zeroRows).inter cellwise.compl)

def periodicSliceComplementWithin (region : Set E) (openRegion : IsOpen region)
    (cellwise : Cellwise (augmentedForms A) region) :
    CWComplex.Subcomplex (periodicLinearSliceSubcomplex A zeroRows : Set E) :=
  subcomplexWithin (periodicSliceClosedComplement A zeroRows region openRegion cellwise)
    (periodicLinearSliceSubcomplex A zeroRows) Set.inter_subset_left

/-- The actual pair `(V,V ∖ region)`, with precisely the periodic
characteristic maps inherited from the original arrangement. -/
@[instance_reducible]
def periodicLinearSliceRelativeCW (region : Set E) (openRegion : IsOpen region)
    (cellwise : Cellwise (augmentedForms A) region) :
    RelCWComplex (V : Set E) ((V : Set E) ∩ regionᶜ) :=
  relativeToSubcomplex (periodicSliceComplementWithin A zeroRows region openRegion cellwise)

end ToricPower.IntegralArrangement

end
