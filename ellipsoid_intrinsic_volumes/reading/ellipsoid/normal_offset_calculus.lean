module

public import Ellipsoid.NormalOffsetSurjectivity
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.LinearAlgebra.Determinant

@[expose] public section

noncomputable section

open Set Matrix
open scoped BigOperators RealInnerProductSpace InnerProductSpace

namespace EllipsoidVerification

theorem axisMap_axisMap {n : ℕ} (a : Fin n → ℝ) (x : Space n) :
    axisMap a (axisMap a x) = axisMap (fun i => a i ^ 2) x := by
  ext i
  simp [axisMap]
  ring

theorem supportPoint_eq {n : ℕ} (a : Fin n → ℝ) (x : Space n) :
    supportPoint a x = (axisSupport a x)⁻¹ • axisMap (fun i => a i ^ 2) x := by
  rw [supportPoint, axisMap_smul, axisMap_axisMap]

theorem axisSupport_sq {n : ℕ} (a : Fin n → ℝ) (x : Space n) :
    axisSupport a x ^ 2 = ∑ i, a i ^ 2 * (x i) ^ 2 := by
  rw [axisSupport, ← real_inner_self_eq_norm_sq]
  simp only [PiLp.inner_apply, Real.inner_apply, axisMap, PiLp.toLp_apply]
  apply Finset.sum_congr rfl
  intro i hi
  ring

def supportDerivative {n : ℕ} (a : Fin n → ℝ) (x : Space n) : Space n →L[ℝ] Space n :=
  (axisSupport a x)⁻¹ • axisCLM (fun i => a i ^ 2) -
    ((axisSupport a x)⁻¹ • innerSL ℝ (supportPoint a x)).smulRight (supportPoint a x)

theorem hasFDerivAt_supportPoint {n : ℕ} {a : Fin n → ℝ} (ha : ∀ i, 0 < a i)
    {x : Space n} (hx : x ≠ 0) :
    HasFDerivAt (supportPoint a) (supportDerivative a x) x := by
  have hp := axisSupport_pos ha hx
  have hi := (hasDerivAt_inv hp.ne').comp_hasFDerivAt x (hasFDerivAt_axisSupport ha hx)
  have hd := hi.smul (axisCLM (fun i => a i ^ 2)).hasFDerivAt
  convert hd using 1
  · funext z
    exact supportPoint_eq a z
  · ext y i
    simp only [supportDerivative, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, axisCLM_apply,
      supportPoint_eq, PiLp.smul_apply, PiLp.sub_apply, PiLp.add_apply, smul_eq_mul,
      inner_smul_left, Function.comp_apply]
    field_simp [hp.ne'] <;> ring

def normalOffsetDerivative {n : ℕ} (a : Fin n → ℝ) (t : ℝ) (x : Space n) :
    Space n →L[ℝ] Space n :=
  ‖x‖ • supportDerivative a x +
    (‖x‖⁻¹ • innerSL ℝ x).smulRight (supportPoint a x) +
      t • ContinuousLinearMap.id ℝ (Space n)

theorem hasFDerivAt_normalOffset {n : ℕ} {a : Fin n → ℝ} (ha : ∀ i, 0 < a i)
    (t : ℝ) {x : Space n} (hx : x ≠ 0) :
    HasFDerivAt (normalOffset a t) (normalOffsetDerivative a t x) x := by
  exact ((hasFDerivAt_euclideanNorm hx).smul (hasFDerivAt_supportPoint ha hx)).add
    ((hasFDerivAt_id x).const_smul t)

def normalOffsetMatrix {n : ℕ} (a : Fin n → ℝ) (t : ℝ) (x : Space n) :
    Matrix (Fin n) (Fin n) ℝ :=
  Matrix.diagonal (fun i => ‖x‖ / axisSupport a x * a i ^ 2 + t) +
    Matrix.vecMulVec (fun i => supportPoint a x i)
      (fun j => ‖x‖⁻¹ * x j - ‖x‖ / axisSupport a x * supportPoint a x j)

theorem normalOffsetDerivative_eq_matrix {n : ℕ} (a : Fin n → ℝ) (t : ℝ) (x : Space n) :
    normalOffsetDerivative a t x = (normalOffsetMatrix a t x).toEuclideanLin.toContinuousLinearMap := by
  ext y i
  simp only [normalOffsetDerivative, supportDerivative, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.id_apply,
    innerSL_apply_apply, axisCLM_apply, PiLp.smul_apply, PiLp.sub_apply,
    PiLp.add_apply, axisMap, PiLp.toLp_apply, smul_eq_mul,
    LinearMap.coe_toContinuousLinearMap',
    Matrix.toEuclideanLin, Matrix.toLpLin_apply, normalOffsetMatrix,
    Matrix.add_mulVec, Matrix.mulVec_diagonal, Matrix.vecMulVec_mulVec,
    Pi.add_apply, Pi.smul_apply, op_smul_eq_smul, dotProduct, PiLp.inner_apply, Real.inner_apply,
    sub_mul, Finset.sum_sub_distrib, Finset.sum_mul, Finset.mul_sum]
  ring_nf
  simp only [Finset.mul_sum]
  simp only [← mul_assoc]
  have hsum :
      (∑ j, ‖x‖ * (axisSupport a x)⁻¹ * supportPoint a x j * y j *
        supportPoint a x i) =
      ∑ j, ‖x‖ * (axisSupport a x)⁻¹ * supportPoint a x i *
        supportPoint a x j * y j := by
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [hsum]
  ring

theorem det_normalOffsetDerivative {n : ℕ} (a : Fin n → ℝ) (t : ℝ) (x : Space n) :
    LinearMap.det (normalOffsetDerivative a t x).toLinearMap = (normalOffsetMatrix a t x).det := by
  rw [normalOffsetDerivative_eq_matrix]
  exact LinearMap.det_toLin (EuclideanSpace.basisFun (Fin n) ℝ).toBasis _

theorem normalOffsetMatrix_smul_pos {n : ℕ} (a : Fin n → ℝ) (t : ℝ)
    {r : ℝ} (hr : 0 < r) (x : Space n) :
    normalOffsetMatrix a t (r • x) = normalOffsetMatrix a t x := by
  ext i j
  simp only [normalOffsetMatrix, norm_smul, Real.norm_of_nonneg hr.le,
    axisSupport_smul, abs_of_pos hr, supportPoint_smul_pos a hr,
    Matrix.add_apply, Matrix.diagonal_apply, Matrix.vecMulVec_apply, PiLp.smul_apply,
    smul_eq_mul]
  rw [mul_div_mul_left _ _ hr.ne', _root_.mul_inv_rev]
  split_ifs <;> field_simp [hr.ne'] <;> ring

end EllipsoidVerification
