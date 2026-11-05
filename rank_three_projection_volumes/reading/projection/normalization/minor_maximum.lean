module
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Data.NNReal.Basic
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.Fintype.EquivFin

/-!
# Finite maxima of actual matrix minors

The maximum ranges over all row and column selections, including repeated
indices. Repeated rows or columns have determinant zero; allowing them makes
replacement-column and bordered-minor bounds direct finite-maximum statements.
A positive maximizing minor is proved to have injective row and column maps.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open Finset
open scoped NNReal

namespace ProjectionVolumes

/-- Largest absolute determinant of an `r × r` submatrix. -/
def minorMaximum {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (r : ℕ) : ℝ :=
  ((Finset.univ : Finset ((Fin r → Fin n) × (Fin r → Fin n))).sup
    (fun maps => NNReal.mk |(M.submatrix maps.1 maps.2).det| (abs_nonneg _)) : ℝ≥0)

lemma minorMaximum_nonneg {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (r : ℕ) :
    0 ≤ minorMaximum M r := by
  exact NNReal.coe_nonneg _

lemma minorMaximum_zero {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) :
    minorMaximum M 0 = 1 := by
  simp [minorMaximum]
  exact Finset.sup_const ⟨(Fin.elim0, Fin.elim0), Finset.mem_univ _⟩ 1

lemma minor_le_maximum {n r : ℕ} (M : Matrix (Fin n) (Fin n) ℝ)
    (rows cols : Fin r → Fin n) :
    |(M.submatrix rows cols).det| ≤ minorMaximum M r := by
  have h := Finset.le_sup
    (f := fun maps : (Fin r → Fin n) × (Fin r → Fin n) =>
      NNReal.mk |(M.submatrix maps.1 maps.2).det| (abs_nonneg _))
    (Finset.mem_univ (rows, cols))
  simpa only [minorMaximum, NNReal.coe_mk] using (NNReal.coe_le_coe.mpr h)

/-- A positive maximum is attained by one row and column selection. -/
theorem exists_maximal_minor {n r : ℕ} (M : Matrix (Fin n) (Fin n) ℝ)
    (hpos : 0 < minorMaximum M r) :
    ∃ rows cols : Fin r → Fin n,
      |(M.submatrix rows cols).det| = minorMaximum M r := by
  let s : Finset ((Fin r → Fin n) × (Fin r → Fin n)) := Finset.univ
  let f : ((Fin r → Fin n) × (Fin r → Fin n)) → ℝ≥0 :=
    fun maps => NNReal.mk |(M.submatrix maps.1 maps.2).det| (abs_nonneg _)
  have hpos' : (0 : ℝ≥0) < s.sup f := hpos
  obtain ⟨maps, hm, hle⟩ := (Finset.le_sup_iff hpos').mp (le_refl (s.sup f))
  have heq : f maps = s.sup f := le_antisymm (Finset.le_sup hm) hle
  exact ⟨maps.1, maps.2, congrArg (fun x : ℝ≥0 => (x : ℝ)) heq⟩

/-- A nonzero minor has no repeated row. -/
lemma injective_rows_of_minor_ne_zero {n r : ℕ}
    (M : Matrix (Fin n) (Fin n) ℝ) (rows cols : Fin r → Fin n)
    (hdet : (M.submatrix rows cols).det ≠ 0) : Function.Injective rows := by
  intro i j hij
  by_contra hne
  apply hdet
  apply Matrix.det_zero_of_row_eq hne
  funext a
  simp only [Matrix.submatrix_apply, hij]

/-- A nonzero minor has no repeated column. -/
lemma injective_cols_of_minor_ne_zero {n r : ℕ}
    (M : Matrix (Fin n) (Fin n) ℝ) (rows cols : Fin r → Fin n)
    (hdet : (M.submatrix rows cols).det ≠ 0) : Function.Injective cols := by
  intro i j hij
  by_contra hne
  apply hdet
  apply Matrix.det_zero_of_column_eq hne
  intro a
  simp only [Matrix.submatrix_apply, hij]

/-- Replacing a pivot column by any original column stays within the maximum
of minors of the same order. -/
lemma replacement_column_minor_bound {n r : ℕ}
    (M : Matrix (Fin n) (Fin n) ℝ) (rows cols : Fin r → Fin n)
    (i : Fin r) (j : Fin n) :
    |((M.submatrix rows cols).updateCol i (fun a => M (rows a) j)).det| ≤
      minorMaximum M r := by
  have hmat : (M.submatrix rows cols).updateCol i (fun a => M (rows a) j) =
      M.submatrix rows (Function.update cols i j) := by
    ext a b
    by_cases h : b = i <;> simp [Matrix.updateCol_apply, h]
  rw [hmat]
  exact minor_le_maximum M rows _

/-- The analogous replacement-row bound. -/
lemma replacement_row_minor_bound {n r : ℕ}
    (M : Matrix (Fin n) (Fin n) ℝ) (rows cols : Fin r → Fin n)
    (i : Fin r) (j : Fin n) :
    |((M.submatrix rows cols).updateRow i (fun a => M j (cols a))).det| ≤
      minorMaximum M r := by
  have hmat : (M.submatrix rows cols).updateRow i (fun a => M j (cols a)) =
      M.submatrix (Function.update rows i j) cols := by
    ext a b
    by_cases h : a = i <;> simp [Matrix.updateRow_apply, h]
  rw [hmat]
  exact minor_le_maximum M _ cols

/-- Reindexing allows the same bound for a minor with any finite index type. -/
lemma minor_le_maximum_card {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix (Fin n) (Fin n) ℝ) (rows cols : ι → Fin n) :
    |(M.submatrix rows cols).det| ≤ minorMaximum M (Fintype.card ι) := by
  let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  calc
    |(M.submatrix rows cols).det| =
        |((M.submatrix rows cols).submatrix e e).det| :=
      congrArg abs (Matrix.det_submatrix_equiv_self e (M.submatrix rows cols)).symm
    _ ≤ minorMaximum M (Fintype.card ι) :=
      minor_le_maximum M (rows ∘ e) (cols ∘ e)

/-- A cofactor of a pivot is an actual minor of the preceding order. -/
lemma cofactor_minor_bound {n r : ℕ}
    (M : Matrix (Fin n) (Fin n) ℝ) (rows cols : Fin (r + 1) → Fin n)
    (i j : Fin (r + 1)) :
    |((M.submatrix rows cols).submatrix j.succAbove i.succAbove).det| ≤
      minorMaximum M r :=
  minor_le_maximum M (rows ∘ j.succAbove) (cols ∘ i.succAbove)

/-- A bordered pivot is an actual minor of the following order, including when
the appended row or column repeats an existing one. -/
lemma bordered_minor_bound {n r : ℕ}
    (M : Matrix (Fin n) (Fin n) ℝ) (rows cols : Fin r → Fin n)
    (i j : Fin n) :
    |(Matrix.fromBlocks (M.submatrix rows cols)
        (fun a (_ : Unit) => M (rows a) j)
        (fun (_ : Unit) b => M i (cols b))
        (fun (_ _ : Unit) => M i j)).det| ≤ minorMaximum M (r + 1) := by
  have h := minor_le_maximum_card M (Sum.elim rows (fun _ : Unit => i))
    (Sum.elim cols (fun _ : Unit => j))
  have hmat : M.submatrix (Sum.elim rows (fun _ : Unit => i))
      (Sum.elim cols (fun _ : Unit => j)) =
      Matrix.fromBlocks (M.submatrix rows cols)
        (fun a (_ : Unit) => M (rows a) j)
        (fun (_ : Unit) b => M i (cols b))
        (fun (_ _ : Unit) => M i j) := by
    ext a b
    cases a <;> cases b <;> rfl
  rw [hmat] at h
  simpa only [Fintype.card_sum, Fintype.card_fin, Fintype.card_unique] using h

end ProjectionVolumes
