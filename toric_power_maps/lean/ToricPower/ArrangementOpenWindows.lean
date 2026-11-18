module

public import ToricPower.DualDiagonalStrip
public import ToricPower.ArrangementOpenSupport

/-! # Bounded cellwise windows exhausting an arbitrary open support

The original coordinate hyperplanes supply integer boxes. Intersecting
with them retains the original cells and exhausts the full support;
no boundedness of the support itself is required.
-/

@[expose] public noncomputable section

open CategoryTheory Topology Set

namespace ToricPower.IntegralArrangement

variable {n s : ℕ} (A : Fin s → Fin n → ℤ) (U : OpenCellSupport A)

def openCellWindow (r : ℕ) : OpenCellSupport A :=
  ⟨⟨(U.val : Set (Fin n → ℝ)) ∩ integerOpenBox r,
    U.val.isOpen.inter (integerOpenBox_isOpen r)⟩,
    U.property.inter (integerOpenBox_cellwise A r)⟩

theorem openCellWindow_mono : Monotone (openCellWindow A U) := by
  intro r t le x hx
  refine ⟨hx.1,fun j => ?_⟩
  have cast : (r : ℝ) ≤ (t : ℝ) := by exact_mod_cast le
  exact ⟨lt_of_le_of_lt (neg_le_neg cast) (hx.2 j).1,(hx.2 j).2.trans_le cast⟩

theorem openCellWindow_le (r : ℕ) : openCellWindow A U r ≤ U :=
  inter_subset_left

theorem openCellWindow_convex (convexU : Convex ℝ (U.val : Set (Fin n → ℝ))) (r : ℕ) :
    Convex ℝ ((openCellWindow A U r).val : Set (Fin n → ℝ)) :=
  convexU.inter (integerOpenBox_convex r)

theorem openCellWindow_bounded (r : ℕ) :
    Bornology.IsBounded ((openCellWindow A U r).val : Set (Fin n → ℝ)) :=
  (integerOpenBox_bounded r).subset inter_subset_right

theorem openCellWindow_exhausts :
    (⋃ r : ℕ, ((openCellWindow A U r).val : Set (Fin n → ℝ))) = U.val := by
  apply Subset.antisymm
  · exact iUnion_subset fun r => openCellWindow_le A U r
  · intro x hx
    obtain ⟨r,hr⟩ := exists_nat_gt ‖x‖
    refine mem_iUnion.mpr ⟨r,hx,fun j => ?_⟩
    have bound : |x j| < (r : ℝ) := by
      simpa only [Real.norm_eq_abs] using (norm_le_pi_norm x j).trans_lt hr
    exact abs_lt.mp bound

def openCellWindowSystem (r₀ : ℕ) : ℕ ⥤ OpenCellSupport A where
  obj r := openCellWindow A U (r₀+r)
  map f := homOfLE (openCellWindow_mono A U (Nat.add_le_add_left f.le r₀))

end ToricPower.IntegralArrangement

end
