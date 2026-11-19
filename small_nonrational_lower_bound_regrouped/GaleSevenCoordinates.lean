module

public import GaleSevenAlgebra
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# The seven-hyperplane obstruction in a coordinate frame

The frame is `B,D,R,S,O`. Vectors in its first four coordinates represent
the four-dimensional hyperplane; the other three outside points have last
coordinate one. Every displayed determinant below is expanded and checked
symbolically by Lean. The final contradiction is linear dependence of
`X,Z,S`, not a numerical test of any particular realization.
-/

noncomputable section
namespace Papers.RationalityTen.GaleSevenCoordinates

open Matrix
open scoped BigOperators

abbrev Vector := Fin 5 → ℝ

def unitPoint (i : Fin 5) : Vector := Pi.single i 1

def point (x : Fin 4 → ℝ) (w : ℝ) : Vector := ![x 0, x 1, x 2, x 3, w]

def detRows (a b c d e : Vector) : ℝ := Matrix.det (Matrix.of ![a, b, c, d, e])

set_option maxRecDepth 10000 in
theorem determinant_BDROX (x : Fin 4 → ℝ) :
    detRows (unitPoint 0) (unitPoint 1) (unitPoint 2) (unitPoint 4) (point x 1) = -x 3 := by
  rw [detRows, Matrix.det_succ_row_zero]
  simp only [unitPoint, point, Matrix.det_succ_row_zero, Matrix.det_fin_three,
    Matrix.submatrix_apply, Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ,
    Fin.val_eq_zero, Fin.zero_succAbove, Fin.succ_succAbove_zero,
    Fin.succ_succAbove_one, Fin.succ_zero_eq_one, Fin.succ_one_eq_two,
    Matrix.submatrix_submatrix, Function.comp_apply, Matrix.det_unique,
    Fin.default_eq_zero, Finset.univ_unique, Finset.sum_singleton]
  norm_num [Pi.single_apply, Fin.succAbove, Fin.succ, Fin.castSucc, Fin.lt_def]

set_option maxRecDepth 10000 in
theorem determinant_ABFOX (a f x : Fin 4 → ℝ) :
    detRows (point a 0) (unitPoint 0) (point f 0) (unitPoint 4) (point x 1) =
      (a 2 * f 3 - a 3 * f 2) * x 1 - (a 1 * f 3 - a 3 * f 1) * x 2 +
        (a 1 * f 2 - a 2 * f 1) * x 3 := by
  rw [detRows, Matrix.det_succ_row_zero]
  simp only [unitPoint, point, Matrix.det_succ_row_zero, Matrix.det_fin_three,
    Matrix.submatrix_apply, Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ,
    Fin.val_eq_zero, Fin.zero_succAbove, Fin.succ_succAbove_zero,
    Fin.succ_succAbove_one, Fin.succ_zero_eq_one, Fin.succ_one_eq_two,
    Matrix.submatrix_submatrix, Function.comp_apply, Matrix.det_unique,
    Fin.default_eq_zero, Finset.univ_unique, Finset.sum_singleton]
  norm_num [Pi.single_apply, Fin.succAbove, Fin.succ, Fin.castSucc, Fin.lt_def] <;> ring

set_option maxRecDepth 10000 in
theorem determinant_BDRYZ (y z : Fin 4 → ℝ) :
    detRows (unitPoint 0) (unitPoint 1) (unitPoint 2) (point y 1) (point z 1) =
      y 3 - z 3 := by
  rw [detRows, Matrix.det_succ_row_zero]
  simp only [unitPoint, point, Matrix.det_succ_row_zero, Matrix.det_fin_three,
    Matrix.submatrix_apply, Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ,
    Fin.val_eq_zero, Fin.zero_succAbove, Fin.succ_succAbove_zero,
    Fin.succ_succAbove_one, Fin.succ_zero_eq_one, Fin.succ_one_eq_two,
    Matrix.submatrix_submatrix, Function.comp_apply, Matrix.det_unique,
    Fin.default_eq_zero, Finset.univ_unique, Finset.sum_singleton]
  norm_num [Pi.single_apply, Fin.succAbove, Fin.succ, Fin.castSucc, Fin.lt_def] <;> ring

set_option maxRecDepth 10000 in
theorem determinant_ADFYZ (a f y z : Fin 4 → ℝ) :
    detRows (point a 0) (unitPoint 1) (point f 0) (point y 1) (point z 1) =
      (a 0 * f 3 - a 3 * f 0) * (z 2 - y 2) -
        (a 2 * f 3 - a 3 * f 2) * (z 0 - y 0) +
          (a 0 * f 2 - a 2 * f 0) * (y 3 - z 3) := by
  rw [detRows, Matrix.det_succ_row_zero]
  simp only [unitPoint, point, Matrix.det_succ_row_zero, Matrix.det_fin_three,
    Matrix.submatrix_apply, Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ,
    Fin.val_eq_zero, Fin.zero_succAbove, Fin.succ_succAbove_zero,
    Fin.succ_succAbove_one, Fin.succ_zero_eq_one, Fin.succ_one_eq_two,
    Matrix.submatrix_submatrix, Function.comp_apply, Matrix.det_unique,
    Fin.default_eq_zero, Finset.univ_unique, Finset.sum_singleton]
  norm_num [Pi.single_apply, Fin.succAbove, Fin.succ, Fin.castSucc, Fin.lt_def] <;> ring

set_option maxRecDepth 10000 in
theorem determinant_BSOXZ (x z : Fin 4 → ℝ) :
    detRows (unitPoint 0) (unitPoint 3) (unitPoint 4) (point x 1) (point z 1) =
      x 1 * z 2 - x 2 * z 1 := by
  rw [detRows, Matrix.det_succ_row_zero]
  simp only [unitPoint, point, Matrix.det_succ_row_zero, Matrix.det_fin_three,
    Matrix.submatrix_apply, Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ,
    Fin.val_eq_zero, Fin.zero_succAbove, Fin.succ_succAbove_zero,
    Fin.succ_succAbove_one, Fin.succ_zero_eq_one, Fin.succ_one_eq_two,
    Matrix.submatrix_submatrix, Function.comp_apply, Matrix.det_unique,
    Fin.default_eq_zero, Finset.univ_unique, Finset.sum_singleton]
  norm_num [Pi.single_apply, Fin.succAbove, Fin.succ, Fin.castSucc, Fin.lt_def] <;> ring

set_option maxRecDepth 10000 in
theorem determinant_DSXYZ (x y z : Fin 4 → ℝ) :
    detRows (unitPoint 1) (unitPoint 3) (point x 1) (point y 1) (point z 1) =
      (z 2 - x 2) * (z 0 - y 0) - (z 0 - x 0) * (z 2 - y 2) := by
  rw [detRows, Matrix.det_succ_row_zero]
  simp only [unitPoint, point, Matrix.det_succ_row_zero, Matrix.det_fin_three,
    Matrix.submatrix_apply, Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ,
    Fin.val_eq_zero, Fin.zero_succAbove, Fin.succ_succAbove_zero,
    Fin.succ_succAbove_one, Fin.succ_zero_eq_one, Fin.succ_one_eq_two,
    Matrix.submatrix_submatrix, Function.comp_apply, Matrix.det_unique,
    Fin.default_eq_zero, Finset.univ_unique, Finset.sum_singleton]
  norm_num [Pi.single_apply, Fin.succAbove, Fin.succ, Fin.castSucc, Fin.lt_def] <;> ring

set_option maxRecDepth 10000 in
theorem determinant_ARSXZ (a x z : Fin 4 → ℝ) :
    detRows (point a 0) (unitPoint 2) (unitPoint 3) (point x 1) (point z 1) =
      a 1 * (z 0 - x 0) - a 0 * (z 1 - x 1) := by
  rw [detRows, Matrix.det_succ_row_zero]
  simp only [unitPoint, point, Matrix.det_succ_row_zero, Matrix.det_fin_three,
    Matrix.submatrix_apply, Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ,
    Fin.val_eq_zero, Fin.zero_succAbove, Fin.succ_succAbove_zero,
    Fin.succ_succAbove_one, Fin.succ_zero_eq_one, Fin.succ_one_eq_two,
    Matrix.submatrix_submatrix, Function.comp_apply, Matrix.det_unique,
    Fin.default_eq_zero, Finset.univ_unique, Finset.sum_singleton]
  norm_num [Pi.single_apply, Fin.succAbove, Fin.succ, Fin.castSucc, Fin.lt_def] <;> ring

set_option maxRecDepth 10000 in
theorem determinant_ABDRO (a : Fin 4 → ℝ) :
    detRows (point a 0) (unitPoint 0) (unitPoint 1) (unitPoint 2) (unitPoint 4) = -a 3 := by
  rw [detRows, Matrix.det_succ_row_zero]
  simp only [unitPoint, point, Matrix.det_succ_row_zero, Matrix.det_fin_three,
    Matrix.submatrix_apply, Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ,
    Fin.val_eq_zero, Fin.zero_succAbove, Fin.succ_succAbove_zero,
    Fin.succ_succAbove_one, Fin.succ_zero_eq_one, Fin.succ_one_eq_two,
    Matrix.submatrix_submatrix, Function.comp_apply, Matrix.det_unique,
    Fin.default_eq_zero, Finset.univ_unique, Finset.sum_singleton]
  norm_num [Pi.single_apply, Fin.succAbove, Fin.succ, Fin.castSucc, Fin.lt_def]

set_option maxRecDepth 10000 in
theorem determinant_ABDFO (a f : Fin 4 → ℝ) :
    detRows (point a 0) (unitPoint 0) (unitPoint 1) (point f 0) (unitPoint 4) =
      a 2 * f 3 - a 3 * f 2 := by
  rw [detRows, Matrix.det_succ_row_zero]
  simp only [unitPoint, point, Matrix.det_succ_row_zero, Matrix.det_fin_three,
    Matrix.submatrix_apply, Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ,
    Fin.val_eq_zero, Fin.zero_succAbove, Fin.succ_succAbove_zero,
    Fin.succ_succAbove_one, Fin.succ_zero_eq_one, Fin.succ_one_eq_two,
    Matrix.submatrix_submatrix, Function.comp_apply, Matrix.det_unique,
    Fin.default_eq_zero, Finset.univ_unique, Finset.sum_singleton]
  norm_num [Pi.single_apply, Fin.succAbove, Fin.succ, Fin.castSucc, Fin.lt_def] <;> ring

set_option maxRecDepth 10000 in
theorem determinant_ARSFO (a f : Fin 4 → ℝ) :
    detRows (point a 0) (unitPoint 2) (unitPoint 3) (point f 0) (unitPoint 4) =
      a 0 * f 1 - a 1 * f 0 := by
  rw [detRows, Matrix.det_succ_row_zero]
  simp only [unitPoint, point, Matrix.det_succ_row_zero, Matrix.det_fin_three,
    Matrix.submatrix_apply, Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ,
    Fin.val_eq_zero, Fin.zero_succAbove, Fin.succ_succAbove_zero,
    Fin.succ_succAbove_one, Fin.succ_zero_eq_one, Fin.succ_one_eq_two,
    Matrix.submatrix_submatrix, Function.comp_apply, Matrix.det_unique,
    Fin.default_eq_zero, Finset.univ_unique, Finset.sum_singleton]
  norm_num [Pi.single_apply, Fin.succAbove, Fin.succ, Fin.castSucc, Fin.lt_def] <;> ring

theorem independent_triple_difference_not_smul (x z s : Vector)
    (h : LinearIndependent ℝ ![x, z, s]) (c : ℝ) : z - x ≠ c • s := by
  intro heq
  have hz : z = c • s + x := sub_eq_iff_eq_add.mp heq
  have hsum : (∑ i : Fin 3, (![-(1 : ℝ), 1, -c] i) • (![x, z, s] i)) = 0 := by
    simp only [Fin.sum_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_succ,
      Fin.sum_univ_zero, add_zero, neg_one_smul, one_smul, neg_smul]
    rw [hz]
    abel
  have hc := Fintype.linearIndependent_iff.mp h ![-(1 : ℝ), 1, -c] hsum 1
  norm_num at hc

/-- The normalized form of the common obstruction in Appendix B.8. -/
theorem normalized_obstruction (a f x y z : Fin 4 → ℝ)
    (ha : a 3 ≠ 0)
    (hδ : a 2 * f 3 - a 3 * f 2 ≠ 0)
    (hε : a 0 * f 1 - a 1 * f 0 ≠ 0)
    (hOXB : LinearIndependent ℝ ![unitPoint 4, point x 1, unitPoint 0])
    (hYZD : LinearIndependent ℝ ![point y 1, point z 1, unitPoint 1])
    (hXZS : LinearIndependent ℝ ![point x 1, point z 1, unitPoint 3])
    (h₁ : detRows (unitPoint 0) (unitPoint 1) (unitPoint 2) (unitPoint 4) (point x 1) = 0)
    (h₂ : detRows (point a 0) (unitPoint 0) (point f 0) (unitPoint 4) (point x 1) = 0)
    (h₃ : detRows (unitPoint 0) (unitPoint 1) (unitPoint 2) (point y 1) (point z 1) = 0)
    (h₄ : detRows (point a 0) (unitPoint 1) (point f 0) (point y 1) (point z 1) = 0)
    (h₅ : detRows (unitPoint 0) (unitPoint 3) (unitPoint 4) (point x 1) (point z 1) = 0)
    (h₆ : detRows (unitPoint 1) (unitPoint 3) (point x 1) (point y 1) (point z 1) = 0)
    (h₇ : detRows (point a 0) (unitPoint 2) (unitPoint 3) (point x 1) (point z 1) = 0) : False := by
  rw [determinant_BDROX, neg_eq_zero] at h₁
  rw [determinant_ABFOX, h₁, mul_zero, add_zero] at h₂
  rw [determinant_BDRYZ, sub_eq_zero] at h₃
  rw [determinant_ADFYZ, h₃, sub_self, mul_zero, add_zero] at h₄
  rw [determinant_BSOXZ, sub_eq_zero] at h₅
  rw [determinant_DSXYZ, sub_eq_zero] at h₆
  rw [determinant_ARSXZ, sub_eq_zero] at h₇
  have hxnon : x 1 ≠ 0 ∨ x 2 ≠ 0 := by
    by_contra h
    push Not at h
    apply independent_triple_difference_not_smul _ _ _ hOXB (x 0)
    ext i
    fin_cases i <;> simp [point, unitPoint, h.1, h.2, h₁]
  have hrnon : z 0 - y 0 ≠ 0 ∨ z 2 - y 2 ≠ 0 := by
    by_contra h
    push Not at h
    have hz₀ : z 0 = y 0 := sub_eq_zero.mp h.1
    have hz₂ : z 2 = y 2 := sub_eq_zero.mp h.2
    apply independent_triple_difference_not_smul _ _ _ hYZD (z 1 - y 1)
    ext i
    fin_cases i <;> simp [point, unitPoint, hz₀, hz₂, h₃]
  have htransverse : a 0 * (a 1 * f 3 - a 3 * f 1) -
      a 1 * (a 0 * f 3 - a 3 * f 0) ≠ 0 := by
    intro h
    apply mul_ne_zero ha hε
    linear_combination -h
  obtain ⟨hz₀, hz₁, hz₂⟩ := GaleSevenAlgebra.projected_difference_zero
    (a 0) (a 1) (a 0 * f 3 - a 3 * f 0) (a 1 * f 3 - a 3 * f 1)
    (a 2 * f 3 - a 3 * f 2) (x 0) (x 1) (x 2) (z 0) (z 1) (z 2)
    (z 0 - y 0) (z 2 - y 2) hδ htransverse (sub_eq_zero.mp h₂)
    (sub_eq_zero.mp h₄).symm hxnon hrnon h₅ h₆.symm h₇.symm
  apply independent_triple_difference_not_smul _ _ _ hXZS (z 3 - x 3)
  ext i
  fin_cases i <;> simp [point, unitPoint, hz₀, hz₁, hz₂]

end Papers.RationalityTen.GaleSevenCoordinates
