module

public import ToricPower.ArrangementLinearSliceCW
public import ToricPower.DiagonalCellWeights
public import ToricPower.ContractibleCellularAugmentation

/-! # The genuine closed convex regions in the dual slice calculation

The dual Cartier coefficient has a weak monomial inequality. These
inequalities define closed unions of the original cells, even on walls.
Their intersection with the actual zero slice inherits the original
characteristic disks and their ordinary cellular boundary.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Topology Set

namespace ToricPower.IntegralArrangement

variable {n s : ℕ} (A : Fin s → Fin n → ℤ)
  (selected : Set (Fin s ⊕ Fin n)) (S : Set (Fin s)) (lower : Fin s → ℤ)

def closedLowerWeightRegion : Set (Fin n → ℝ) :=
  {x | ∀ r ∈ S, (lower r : ℝ) ≤ integralRowForm A r x}

theorem closedLowerWeightRegion_cellwise :
    Cellwise (augmentedForms A) (closedLowerWeightRegion A S lower) := by
  intro e active x y hx hy
  suffices transfer : ∀ ⦃x y : Fin n → ℝ⦄,
      x ∈ cell (augmentedForms A) e active → y ∈ cell (augmentedForms A) e active →
      x ∈ closedLowerWeightRegion A S lower → y ∈ closedLowerWeightRegion A S lower from
    ⟨transfer hx hy,transfer hy hx⟩
  intro x y hx hy inside r hr
  have same := (openWeightRegion_cellwise (augmentedForms A) {Sum.inl r}
    (fun _ => lower r-1) e active hx hy)
  have inequality : (integralRowForm A r x < (lower r : ℝ)) ↔
      integralRowForm A r y < (lower r : ℝ) := by
    change ((augmentedForms A (.inl r)) x < (lower r : ℝ)) ↔
      (augmentedForms A (.inl r)) y < (lower r : ℝ)
    simpa [openWeightRegion,Int.cast_sub] using same
  exact not_lt.mp (fun below => (not_lt.mpr (inside r hr)) (inequality.mpr below))

theorem closedLowerWeightRegion_isClosed : IsClosed (closedLowerWeightRegion A S lower) := by
  change IsClosed {x | ∀ r, ∀ _ : r ∈ S, (lower r : ℝ) ≤ integralRowForm A r x}
  simp only [setOf_forall]
  exact isClosed_iInter fun r => isClosed_iInter fun _ =>
    isClosed_le continuous_const (integralRowForm A r).continuous_of_finiteDimensional

theorem closedLowerWeightRegion_convex : Convex ℝ (closedLowerWeightRegion A S lower) := by
  intro x hx y hy a b ha hb hab r hr
  change (lower r : ℝ) ≤ integralRowForm A r (a • x+b • y)
  rw [map_add,map_smul,map_smul]
  calc
    (lower r : ℝ) = a*(lower r : ℝ)+b*(lower r : ℝ) := by rw [← add_mul,hab,one_mul]
    _ ≤ a*integralRowForm A r x+b*integralRowForm A r y :=
      add_le_add (mul_le_mul_of_nonneg_left (hx r hr) ha)
        (mul_le_mul_of_nonneg_left (hy r hr) hb)

/-- The actual weak Cartier inequality, including every equality wall. -/
theorem closedLowerWeightRegion_cell_iff {q : ℕ} (c : Cell (augmentedForms A) q)
    {x : Fin n → ℝ} (inside : x ∈ cell (augmentedForms A) c.val.1 c.val.2) :
    x ∈ closedLowerWeightRegion A S lower ↔
      ∀ r ∈ S, reflectedCeiling A c r ≤ -lower r := by
  change (∀ r ∈ S, (lower r : ℝ) ≤ integralRowForm A r x) ↔ _
  apply forall₂_congr
  intro r hr
  rw [reflectedCeiling_eq_ceil A c inside,Int.ceil_le,Int.cast_neg,neg_le_neg_iff]

def closedSliceDualRegion : Set (Fin n → ℝ) :=
  (arrangementZeroSlice (augmentedForms A) selected : Set (Fin n → ℝ)) ∩
    closedLowerWeightRegion A S lower

theorem closedSliceDualRegion_convex : Convex ℝ (closedSliceDualRegion A selected S lower) :=
  (arrangementZeroSlice (augmentedForms A) selected).convex.inter
    (closedLowerWeightRegion_convex A S lower)

local instance closedDualRegionAmbientCW : CWComplex (arrangementCarrier A) :=
  periodicArrangementCWComplex A

/-- This CW structure retains the ambient periodic disks and incidence signs. -/
def closedSliceDualSubcomplex : CWComplex.Subcomplex (arrangementCarrier A) :=
  periodicCellwiseSubcomplex A (closedSliceDualRegion A selected S lower)
    ((arrangementZeroSlice (augmentedForms A) selected).closed_of_finiteDimensional.inter
      (closedLowerWeightRegion_isClosed A S lower))
    ((arrangementZeroSlice_cellwise A selected).inter
      (closedLowerWeightRegion_cellwise A S lower))

local instance closedDualRegionCW : CWComplex (closedSliceDualRegion A selected S lower) :=
  inferInstanceAs (CWComplex (closedSliceDualSubcomplex A selected S lower : Set (Fin n → ℝ)))

variable {k : Type} [Ring k] (M : ModuleCat.{0} k)

def closedSliceDualCellComplex : ChainComplex (ModuleCat k) ℕ :=
  TauCeti.cellularChainComplex (closedSliceDualRegion A selected S lower) M

def closedSliceDualAugmentation
    (nonempty : (closedSliceDualRegion A selected S lower).Nonempty) :
    closedSliceDualCellComplex A selected S lower M ⟶
      (ChainComplex.single₀ (ModuleCat k)).obj M := by
  letI := (closedSliceDualRegion_convex A selected S lower).contractibleSpace nonempty
  exact contractibleCellularAugmentation M (closedSliceDualRegion A selected S lower)
    ⟨nonempty.choose,nonempty.choose_spec⟩

theorem closedSliceDualAugmentation_quasiIso
    (nonempty : (closedSliceDualRegion A selected S lower).Nonempty) :
    QuasiIso (closedSliceDualAugmentation A selected S lower M nonempty) := by
  letI := (closedSliceDualRegion_convex A selected S lower).contractibleSpace nonempty
  exact contractibleCellularAugmentation_quasiIso M (closedSliceDualRegion A selected S lower)
    ⟨nonempty.choose,nonempty.choose_spec⟩

end ToricPower.IntegralArrangement

end
