module
public import Mathlib.LinearAlgebra.Matrix.SchurComplement
public import Mathlib.Data.Real.Basic

/-!
# The block transformation in maximal-minor normalization

The statements in this file are matrix identities and quantitative consequences
of explicitly stated pivot-minor bounds. No geometric realization assertion is
assumed or encoded in these hypotheses.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators Matrix

namespace ProjectionVolumes

variable {m n p : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- The row transformation determined by an invertible pivot block. -/
def pivotNormalizer (g : ℝ) (B : Matrix m m ℝ) (C : Matrix n m ℝ) :
    Matrix (m ⊕ n) (m ⊕ n) ℝ :=
  Matrix.fromBlocks (g⁻¹ • B⁻¹) 0 (-(C * B⁻¹)) 1

/-- Applying the normalizer leaves an identity pivot block and a scaled Schur
complement. -/
theorem pivotNormalizer_mul (g : ℝ) (hg : g ≠ 0)
    (B : Matrix m m ℝ) (A : Matrix m p ℝ) (C : Matrix n m ℝ)
    (D : Matrix n p ℝ) (hB : B.det ≠ 0) :
    g • (pivotNormalizer g B C * Matrix.fromBlocks B A C D) =
      Matrix.fromBlocks 1 (B⁻¹ * A) 0 (g • (D - C * B⁻¹ * A)) := by
  have hinv : B⁻¹ * B = 1 := B.nonsing_inv_mul (isUnit_iff_ne_zero.mpr hB)
  simp [pivotNormalizer, Matrix.fromBlocks_multiply, Matrix.smul_mul,
    Matrix.mul_assoc, hinv, Matrix.fromBlocks_smul, smul_smul, hg,
    sub_eq_add_neg, add_comm]

/-- The exact determinant of the row transformation. -/
theorem pivotNormalizer_det (g : ℝ) (B : Matrix m m ℝ) (C : Matrix n m ℝ) :
    (pivotNormalizer g B C).det = (g⁻¹) ^ Fintype.card m * B.det⁻¹ := by
  simp [pivotNormalizer, Matrix.det_fromBlocks_zero₁₂, Matrix.det_smul,
    Matrix.det_nonsing_inv, Ring.inverse_eq_inv']

/-- The exact absolute determinant, in the positive-scale case. -/
theorem pivotNormalizer_abs_det (g : ℝ) (hg : 0 < g)
    (B : Matrix m m ℝ) (C : Matrix n m ℝ) :
    |(pivotNormalizer g B C).det| = (g⁻¹) ^ Fintype.card m * |B.det|⁻¹ := by
  rw [pivotNormalizer_det, abs_mul, abs_pow, abs_inv, abs_of_pos hg, abs_inv]

/-- The normalizer has the scaling factor required to preserve the marked
mixed-volume coefficients with `k` segment arguments. -/
theorem pivotNormalizer_scaling (g : ℝ) (hg : 0 < g)
    (B : Matrix m m ℝ) (C : Matrix n m ℝ) {k : ℕ}
    (hrk : Fintype.card m ≤ k) (hB : |B.det| = g ^ (k - Fintype.card m)) :
    g ^ k * |(pivotNormalizer g B C).det| = 1 := by
  rw [pivotNormalizer_abs_det g hg B C, hB, inv_pow, ← mul_inv, ← pow_add,
    Nat.add_sub_of_le hrk, mul_inv_cancel₀ (pow_ne_zero _ hg.ne')]

/-- Every vector with zero pivot coordinates is fixed exactly. -/
theorem pivotNormalizer_fixes (g : ℝ) (B : Matrix m m ℝ) (C : Matrix n m ℝ)
    (v : n → ℝ) :
    pivotNormalizer g B C *ᵥ Sum.elim (fun _ : m => 0) v =
      Sum.elim (fun _ : m => 0) v := by
  rw [pivotNormalizer, Matrix.fromBlocks_mulVec]
  change Sum.elim
      ((g⁻¹ • B⁻¹) *ᵥ (0 : m → ℝ) + (0 : Matrix m n ℝ) *ᵥ v)
      ((-(C * B⁻¹)) *ᵥ (0 : m → ℝ) + (1 : Matrix n n ℝ) *ᵥ v) =
    Sum.elim (0 : m → ℝ) v
  simp only [Matrix.mulVec_zero, Matrix.zero_mulVec, Matrix.one_mulVec,
    add_zero, zero_add]

/-- Cramer's rule turns maximality of replacement-column minors into the
entry bound for `B⁻¹ A`. -/
theorem inverse_mulVec_bound (B : Matrix m m ℝ) (v : m → ℝ)
    (hB : B.det ≠ 0)
    (hminor : ∀ i, |(B.updateCol i v).det| ≤ |B.det|) :
    ∀ i, |(B⁻¹ *ᵥ v) i| ≤ 1 := by
  intro i
  have h := congrFun (B.det_smul_inv_mulVec_eq_cramer v (isUnit_iff_ne_zero.mpr hB)) i
  simp only [Matrix.smul_mulVec, Pi.smul_apply, smul_eq_mul, Matrix.cramer_apply] at h
  have hbound : |B.det| * |(B⁻¹ *ᵥ v) i| ≤ |B.det| * 1 := by
    rw [← abs_mul, h, mul_one]
    exact hminor i
  exact (mul_le_mul_iff_of_pos_left (abs_pos.mpr hB)).mp hbound

/-- The row version of Cramer's bound. -/
theorem vecMul_inverse_bound (B : Matrix m m ℝ) (v : m → ℝ)
    (hB : B.det ≠ 0)
    (hminor : ∀ i, |(B.updateRow i v).det| ≤ |B.det|) :
    ∀ i, |(v ᵥ* B⁻¹) i| ≤ 1 := by
  intro i
  have h := congrFun (B.det_smul_inv_vecMul_eq_cramer_transpose v
    (isUnit_iff_ne_zero.mpr hB)) i
  simp only [Matrix.smul_vecMul, Pi.smul_apply, smul_eq_mul, Matrix.cramer_apply,
    Matrix.updateCol_transpose, Matrix.det_transpose] at h
  have hbound : |B.det| * |(v ᵥ* B⁻¹) i| ≤ |B.det| * 1 := by
    rw [← abs_mul, h, mul_one]
    exact hminor i
  exact (mul_le_mul_iff_of_pos_left (abs_pos.mpr hB)).mp hbound

/-- The inverse pivot entries are bounded by the previous-order minors divided
by the pivot determinant. -/
theorem inverse_entry_bound {r : ℕ}
    (B : Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ) (hB : B.det ≠ 0)
    (d : ℝ)
    (hminor : ∀ i j : Fin (r + 1), |(B.submatrix j.succAbove i.succAbove).det| ≤ d) :
    ∀ i j, |B⁻¹ i j| ≤ d / |B.det| := by
  intro i j
  rw [Matrix.inv_def]
  simp only [Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv',
    Matrix.adjugate_fin_succ_eq_det_submatrix, abs_mul, abs_inv, abs_pow,
    abs_neg, abs_one, one_pow, one_mul]
  rw [div_eq_mul_inv, mul_comm d]
  exact mul_le_mul_of_nonneg_left (hminor i j) (inv_nonneg.mpr (abs_nonneg B.det))

/-- The bordered determinant is the pivot determinant times the corresponding
Schur-complement entry. This is the exact identity used for the next-order
minor bound. -/
theorem bordered_pivot_det (B : Matrix m m ℝ) (A : Matrix m p ℝ)
    (C : Matrix n m ℝ) (D : Matrix n p ℝ) (hB : B.det ≠ 0)
    (i : n) (j : p) :
    (Matrix.fromBlocks B (fun a (_ : Unit) => A a j)
      (fun (_ : Unit) b => C i b) (fun (_ _ : Unit) => D i j)).det =
      B.det * (D - C * B⁻¹ * A) i j := by
  letI : Invertible B := B.invertibleOfIsUnitDet (isUnit_iff_ne_zero.mpr hB)
  have h := Matrix.det_fromBlocks₁₁ B
    (fun a (_ : Unit) => A a j) (fun (_ : Unit) b => C i b)
    (fun (_ _ : Unit) => D i j)
  rw [Matrix.invOf_eq_nonsing_inv, Matrix.det_unique (n := Unit)] at h
  convert h using 1 <;> rfl

end ProjectionVolumes
