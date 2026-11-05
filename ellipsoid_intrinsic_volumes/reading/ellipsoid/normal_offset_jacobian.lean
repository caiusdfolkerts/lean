module

public import Ellipsoid.NormalOffsetCalculus
public import Mathlib.LinearAlgebra.Matrix.SchurComplement
public import Mathlib.Algebra.Polynomial.BigOperators
public import tau_ceti.topology.algebra.polynomial.basic

@[expose] public section

noncomputable section

open Matrix Polynomial Set
open scoped BigOperators RealInnerProductSpace

namespace EllipsoidVerification

theorem det_diagonal_add_vecMulVec {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b v w : ι → ℝ) (hb : ∀ i, b i ≠ 0) :
    (Matrix.diagonal b + Matrix.vecMulVec v w).det =
      (∏ i, b i) * (1 + ∑ i, w i * (b i)⁻¹ * v i) := by
  have hfactor : Matrix.diagonal b + Matrix.vecMulVec v w =
      Matrix.diagonal b * (1 + Matrix.vecMulVec (fun i => (b i)⁻¹ * v i) w) := by
    ext i j
    simp only [Matrix.add_apply, Matrix.diagonal_mul, Matrix.diagonal_apply,
      Matrix.one_apply, Matrix.vecMulVec_apply]
    split_ifs <;> field_simp [hb i] <;> ring
  rw [hfactor, Matrix.det_mul, Matrix.det_diagonal, Matrix.vecMulVec_eq Unit,
    Matrix.det_one_add_replicateCol_mul_replicateRow]
  simp only [dotProduct]
  congr 2
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem det_diagonal_add_vecMulVec_expansion {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b v w : ι → ℝ) (hb : ∀ i, b i ≠ 0) :
    (Matrix.diagonal b + Matrix.vecMulVec v w).det =
      (∏ i, b i) + ∑ i, v i * w i * ∏ j ∈ Finset.univ.erase i, b j := by
  rw [det_diagonal_add_vecMulVec b v w hb, mul_add, mul_one, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [← Finset.mul_prod_erase Finset.univ b (Finset.mem_univ i)]
  field_simp [hb i]

def normalOffsetJacobianPolynomial {n : ℕ} (a : Fin n → ℝ) (x : Space n) : ℝ[X] :=
  (∏ i, (X + C (‖x‖ / axisSupport a x * a i ^ 2))) +
    ∑ i, C (supportPoint a x i *
      (‖x‖⁻¹ * x i - ‖x‖ / axisSupport a x * supportPoint a x i)) *
      ∏ j ∈ Finset.univ.erase i, (X + C (‖x‖ / axisSupport a x * a j ^ 2))

theorem normalOffsetJacobianPolynomial_eval {n : ℕ} {a : Fin n → ℝ}
    (ha : ∀ i, 0 < a i) {x : Space n} (hx : x ≠ 0) {t : ℝ} (ht : 0 ≤ t) :
    (normalOffsetJacobianPolynomial a x).eval t = (normalOffsetMatrix a t x).det := by
  rw [normalOffsetMatrix, det_diagonal_add_vecMulVec_expansion]
  · simp only [normalOffsetJacobianPolynomial, Polynomial.eval_add,
      Polynomial.eval_prod, Polynomial.eval_finsetSum, Polynomial.eval_mul,
      Polynomial.eval_X, Polynomial.eval_C, add_comm]
  · intro i
    exact (add_pos_of_pos_of_nonneg
      (mul_pos (div_pos (norm_pos_iff.mpr hx) (axisSupport_pos ha hx)) (sq_pos_of_pos (ha i))) ht).ne'

theorem normalOffsetJacobianPolynomial_natDegree {n : ℕ} (a : Fin n → ℝ) (x : Space n) :
    (normalOffsetJacobianPolynomial a x).natDegree ≤ n := by
  apply Polynomial.natDegree_add_le_of_degree_le
  · apply (Polynomial.natDegree_prod_le _ _).trans
    simp only [natDegree_X_add_C, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, smul_eq_mul, mul_one]
    exact le_rfl
  · apply Polynomial.natDegree_sum_le_of_forall_le
    intro i hi
    apply (Polynomial.natDegree_C_mul_le _ _).trans
    apply (Polynomial.natDegree_prod_le _ _).trans
    simp only [natDegree_X_add_C, Finset.sum_const, smul_eq_mul, mul_one]
    exact (Finset.card_le_card (Finset.erase_subset _ _)).trans_eq (by simp)

theorem normalOffsetMatrix_det_pos_unit {n : ℕ} {a : Fin n → ℝ}
    (ha : ∀ i, 0 < a i) {x : Space n} (hx : ‖x‖ = 1) {t : ℝ} (ht : 0 ≤ t) :
    0 < (normalOffsetMatrix a t x).det := by
  have hx0 : x ≠ 0 := by intro h; simpa [h] using hx
  let h := axisSupport a x
  have hh : 0 < h := axisSupport_pos ha hx0
  let b : Fin n → ℝ := fun i => a i ^ 2 / h + t
  have hb (i : Fin n) : 0 < b i := add_pos_of_pos_of_nonneg
    (div_pos (sq_pos_of_pos (ha i)) hh) ht
  have hv (i : Fin n) : supportPoint a x i = a i ^ 2 * x i / h := by
    simp only [supportPoint_eq, PiLp.smul_apply, axisMap, PiLp.toLp_apply, smul_eq_mul]
    dsimp [h]
    ring
  have hsum : ∑ i, a i ^ 2 * (x i) ^ 2 / h ^ 2 = 1 := by
    rw [← Finset.sum_div, ← axisSupport_sq]
    exact div_self (pow_ne_zero 2 hh.ne')
  have hbracket :
      1 + ∑ i, (x i - h⁻¹ * supportPoint a x i) * (b i)⁻¹ * supportPoint a x i =
        ((h + t) / h) * ∑ i, (a i ^ 2 / h / b i) * (x i) ^ 2 := by
    have heach (i : Fin n) :
        (x i - h⁻¹ * supportPoint a x i) * (b i)⁻¹ * supportPoint a x i =
          ((h + t) / h) * ((a i ^ 2 / h / b i) * (x i) ^ 2) -
            a i ^ 2 * (x i) ^ 2 / h ^ 2 := by
      rw [hv]
      have hden : a i ^ 2 + h * t ≠ 0 :=
        (add_pos_of_pos_of_nonneg (sq_pos_of_pos (ha i)) (mul_nonneg hh.le ht)).ne'
      dsimp [b]
      field_simp [hh.ne', hden] <;> ring
    simp_rw [heach]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hsum]
    ring
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
    by_contra h
    apply hx0
    ext i
    exact not_not.mp (not_exists.mp h i)
  have hS : 0 < ∑ i, (a i ^ 2 / h / b i) * (x i) ^ 2 := by
    apply Finset.sum_pos'
    · intro i hi
      positivity
    · exact ⟨i, Finset.mem_univ i, mul_pos
        (div_pos (div_pos (sq_pos_of_pos (ha i)) hh) (hb i)) (sq_pos_of_ne_zero hi)⟩
  rw [normalOffsetMatrix, det_diagonal_add_vecMulVec]
  · have hpos : 0 < (∏ i, b i) *
        (1 + ∑ i, (x i - h⁻¹ * supportPoint a x i) * (b i)⁻¹ * supportPoint a x i) := by
      rw [hbracket]
      exact mul_pos (Finset.prod_pos fun i _ => hb i)
        (mul_pos (div_pos (add_pos_of_pos_of_nonneg hh ht) hh) hS)
    simpa only [hx, one_div, inv_one, one_mul, mul_one, b, h, div_eq_mul_inv,
      mul_comm] using hpos
  · intro i
    simpa [hx, b, h, div_eq_mul_inv, mul_comm] using (hb i).ne'

theorem normalOffsetMatrix_det_pos {n : ℕ} {a : Fin n → ℝ}
    (ha : ∀ i, 0 < a i) {x : Space n} (hx : x ≠ 0) {t : ℝ} (ht : 0 ≤ t) :
    0 < (normalOffsetMatrix a t x).det := by
  have hunit := normalized_mem_unitSphere hx
  have h := normalOffsetMatrix_det_pos_unit ha (by simpa using hunit) ht
  simpa only [normalOffsetMatrix_smul_pos a t (inv_pos.mpr (norm_pos_iff.mpr hx))] using h

theorem normalOffsetJacobianPolynomial_smul_pos {n : ℕ} (a : Fin n → ℝ)
    {r : ℝ} (hr : 0 < r) (x : Space n) :
    normalOffsetJacobianPolynomial a (r • x) = normalOffsetJacobianPolynomial a x := by
  simp only [normalOffsetJacobianPolynomial, norm_smul, Real.norm_of_nonneg hr.le,
    axisSupport_smul, abs_of_pos hr, supportPoint_smul_pos a hr,
    PiLp.smul_apply, smul_eq_mul, mul_div_mul_left _ _ hr.ne', _root_.mul_inv_rev]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  congr 2
  field_simp [hr.ne']

end EllipsoidVerification
