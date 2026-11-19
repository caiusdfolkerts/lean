module

public import PaperVerification.AlternatingFormsOrbitGenericity
public import Mathlib.Data.Matrix.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Tactic.Ring.Basic

/-!
# Polynomial coordinates of simultaneous congruence

The variables are all entries of a change-of-basis matrix. Each polynomial below is
a literal entry of Xᵀ A X. The Jacobian at the identity is computed using dual-number
evaluation, with no appeal to an orbit classification theorem.
-/

@[expose] public section
noncomputable section

open scoped BigOperators

namespace PaperVerification.AlternatingForms

open MvPolynomial Matrix

variable {K ν ι : Type*} [CommRing K] [Fintype ν] [DecidableEq ν]

/-- Independent variables arranged as a square matrix. -/
def orbitUniversalMatrix : Matrix ν ν (MvPolynomial (ν × ν) K) :=
  Matrix.of fun i j ↦ X (i, j)

/-- The coefficient point corresponding to the identity matrix. -/
def orbitIdentityPoint : (ν × ν) → K :=
  fun z ↦ (1 : Matrix ν ν K) z.1 z.2

/-- A literal entry of the simultaneous congruence action. -/
def orbitCongruenceCoordinate (A : Matrix ν ν K) (u v : ν) :
    MvPolynomial (ν × ν) K :=
  ∑ i, ∑ j, C (A i j) * X (i, u) * X (j, v)

/-- A selected family of entries of one or more congruence transforms.
The matrix and selected row and column may depend on the output coordinate. -/
def orbitCongruenceFamily (A : ι → Matrix ν ν K) (row col : ι → ν) :
    ι → MvPolynomial (ν × ν) K :=
  fun i ↦ orbitCongruenceCoordinate (A i) (row i) (col i)

theorem orbitCongruenceCoordinate_eval (A : Matrix ν ν K) (u v : ν)
    (x : (ν × ν) → K) :
    eval x (orbitCongruenceCoordinate A u v) =
      ((Matrix.of fun i j ↦ x (i, j)).transpose * A *
        (Matrix.of fun i j ↦ x (i, j))) u v := by
  simp only [orbitCongruenceCoordinate, map_sum, map_mul, eval_C, eval_X,
    Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  ring

@[simp]
theorem orbitCongruenceCoordinate_identity (A : Matrix ν ν K) (u v : ν) :
    eval (orbitIdentityPoint (K := K) (ν := ν))
      (orbitCongruenceCoordinate A u v) = A u v := by
  rw [orbitCongruenceCoordinate_eval]
  have h : (Matrix.of fun i j ↦ orbitIdentityPoint (K := K) (ν := ν) (i, j)) =
      (1 : Matrix ν ν K) := rfl
  rw [h, Matrix.transpose_one, one_mul, mul_one]

/-- The differential of simultaneous congruence at the identity, in selected entries. -/
def orbitCongruenceDifferential (A : ι → Matrix ν ν K) (row col : ι → ν) :
    ((ν × ν) → K) →ₗ[K] (ι → K) where
  toFun H := fun i ↦
    ((Matrix.of fun r c ↦ H (r, c)).transpose * A i +
      A i * (Matrix.of fun r c ↦ H (r, c))) (row i) (col i)
  map_add' H G := by
    funext i
    simp only [Pi.add_apply, Matrix.of_apply, Matrix.add_apply, Matrix.mul_apply,
      Matrix.transpose_apply, add_mul, mul_add, Finset.sum_add_distrib]
    ring
  map_smul' a H := by
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, Matrix.of_apply, Matrix.add_apply,
      Matrix.mul_apply, Matrix.transpose_apply, RingHom.id_apply]
    rw [mul_add, Finset.mul_sum, Finset.mul_sum]
    congr 1
    · apply Finset.sum_congr rfl
      intro j _
      ring
    · apply Finset.sum_congr rfl
      intro j _
      ring

/-- The Jacobian of the actual polynomial congruence family at the identity equals
the usual differential H ↦ Hᵀ A + A H. -/
theorem orbitCongruenceFamily_jacobian (A : ι → Matrix ν ν K) (row col : ι → ν)
    (H : (ν × ν) → K) :
    TauCeti.jacobiMatrixAt (orbitCongruenceFamily A row col)
        (orbitIdentityPoint (K := K) (ν := ν)) *ᵥ H =
      orbitCongruenceDifferential A row col H := by
  funext z
  rw [TauCeti.jacobiMatrixAt_mulVec_apply_eq_snd_aeval]
  simp only [orbitCongruenceFamily, orbitCongruenceCoordinate, map_sum, map_mul,
    aeval_C, aeval_X, TrivSqZeroExt.algebraMap_eq_inl,
    TrivSqZeroExt.snd_sum, DualNumber.snd_mul, TrivSqZeroExt.fst_mul,
    TrivSqZeroExt.fst_add, TrivSqZeroExt.snd_add, TrivSqZeroExt.fst_inl,
    TrivSqZeroExt.snd_inl, TrivSqZeroExt.fst_inr, TrivSqZeroExt.snd_inr,
    add_zero, zero_add, zero_mul, mul_zero]
  simp only [orbitIdentityPoint, Matrix.one_apply, mul_ite, ite_mul,
    mul_one, one_mul, mul_zero, zero_mul, Finset.sum_add_distrib,
    Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  simp [orbitCongruenceDifferential, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.add_apply, Matrix.of_apply, mul_comm, add_comm]

theorem orbitCongruenceFamily_jacobian_surjective
    (A : ι → Matrix ν ν K) (row col : ι → ν)
    (h : Function.Surjective (orbitCongruenceDifferential A row col)) :
    (TauCeti.jacobiMatrixAt (orbitCongruenceFamily A row col)
      (orbitIdentityPoint (K := K) (ν := ν))).mulVec.Surjective := by
  intro y
  obtain ⟨H, hH⟩ := h y
  refine ⟨H, ?_⟩
  rw [orbitCongruenceFamily_jacobian, hH]

/-- The polynomial whose nonvanishing says that the parameter matrix is invertible. -/
def orbitDeterminant : MvPolynomial (ν × ν) K :=
  (orbitUniversalMatrix (K := K) (ν := ν)).det

theorem orbitDeterminant_eval (x : (ν × ν) → K) :
    eval x (orbitDeterminant (K := K) (ν := ν)) =
      (Matrix.of fun i j ↦ x (i, j)).det := by
  rw [orbitDeterminant, RingHom.map_det]
  congr 1
  ext i j
  simp [orbitUniversalMatrix]

@[simp]
theorem orbitDeterminant_identity :
    eval (orbitIdentityPoint (K := K) (ν := ν))
      (orbitDeterminant (K := K) (ν := ν)) = 1 := by
  rw [orbitDeterminant_eval]
  change (1 : Matrix ν ν K).det = 1
  exact Matrix.det_one

theorem orbitDeterminant_ne_zero [Nontrivial K] :
    orbitDeterminant (K := K) (ν := ν) ≠ 0 := by
  intro h
  have h' := orbitDeterminant_identity (K := K) (ν := ν)
  rw [h, map_zero] at h'
  exact zero_ne_one h'

end PaperVerification.AlternatingForms
