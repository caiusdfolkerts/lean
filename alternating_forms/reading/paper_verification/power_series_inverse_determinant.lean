module

public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.RingTheory.PowerSeries.Inverse
public import Mathlib.Algebra.BigOperators.NatAntidiagonal
public import Mathlib.Tactic.Ring
public import Lean.Elab.Tactic.Omega

/-!
# The exact Hessenberg determinant for a reciprocal coefficient

The finite coefficient matrix of multiplication by a unit-constant power
series is lower triangular with determinant one.  Its first inverse column
is the coefficient vector of the reciprocal.  The adjugate formula gives
the Hessenberg determinant, including the zero-size case and every sign.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped BigOperators Matrix Classical

namespace PaperVerification.PowerSeriesInverseDeterminant

variable {R : Type*} [CommRing R]

def coefficientTriangular (φ : PowerSeries R) (s : ℕ) :
    Matrix (Fin (s+1)) (Fin (s+1)) R :=
  fun i j => if j.val ≤ i.val then PowerSeries.coeff (i.val-j.val) φ else 0

theorem coefficientTriangular_det (φ : PowerSeries R) (hφ : φ.constantCoeff = 1) (s : ℕ) :
    (coefficientTriangular φ s).det = 1 := by
  have hl : (coefficientTriangular φ s).IsLowerTriangular := by
    intro i j hij
    change (if j.val ≤ i.val then _ else (0 : R)) = 0
    exact if_neg (by exact Nat.not_le_of_gt hij)
  rw [Matrix.det_of_isLowerTriangular _ hl]
  simp only [coefficientTriangular, le_refl, if_true, Nat.sub_self,
    PowerSeries.coeff_zero_eq_constantCoeff_apply, hφ, Finset.prod_const_one]

theorem coefficientTriangular_mulVec (φ ψ : PowerSeries R) (s : ℕ) (i : Fin (s+1)) :
    (coefficientTriangular φ s *ᵥ (fun j => PowerSeries.coeff j.val ψ)) i =
      PowerSeries.coeff i.val (ψ*φ) := by
  rw [Matrix.mulVec, dotProduct]
  simp only [coefficientTriangular, ite_mul, zero_mul]
  rw [← Finset.sum_filter]
  rw [PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun a b => PowerSeries.coeff a ψ * PowerSeries.coeff b φ) i.val]
  apply Finset.sum_bij (fun j hj => j.val)
  · intro j hj
    have h := (Finset.mem_filter.mp hj).2
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le h)
  · intro j hj l hl h
    exact Fin.ext h
  · intro j hj
    have hj' := Finset.mem_range.mp hj
    refine ⟨⟨j, by have hi := i.isLt; omega⟩, ?_, rfl⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Nat.le_of_lt_succ hj'⟩
  · intro j hj
    exact mul_comm _ _

theorem coefficientTriangular_inverse_column (φ : PowerSeries R)
    (hφ : φ.constantCoeff = 1) (s : ℕ) :
    coefficientTriangular φ s *ᵥ
      (fun j => PowerSeries.coeff j.val (PowerSeries.invOfUnit φ 1)) = Pi.single 0 1 := by
  funext i
  rw [coefficientTriangular_mulVec, PowerSeries.invOfUnit_mul φ 1 hφ, PowerSeries.coeff_one]
  by_cases hi : i = 0
  · subst i
    simp
  · have hiv : i.val ≠ 0 := fun h => hi (Fin.ext h)
    simp [hi, hiv, Pi.single_apply, Ne.symm hi]

/-- The literal cofactor matrix, with the row and column signs distributed
so that alternating reciprocal coefficients become unsigned entries. -/
def inverseCoefficientMatrix (φ : PowerSeries R) (s : ℕ) : Matrix (Fin s) (Fin s) R :=
  fun i j => (-1 : R)^i.val * ((-1 : R)^(j.val+1) *
    (if i.val ≤ j.val+1 then PowerSeries.coeff (j.val+1-i.val) φ else 0))

theorem sign_products (s : ℕ) :
    (∏ i : Fin s, (-1 : R)^i.val) * (∏ i : Fin s, (-1 : R)^(i.val+1)) = (-1 : R)^s := by
  rw [← Finset.prod_mul_distrib]
  have hi (i : Fin s) : (-1 : R)^i.val * (-1 : R)^(i.val+1) = -1 := by
    rw [← pow_add, show i.val+(i.val+1)=2*i.val+1 by omega, pow_add, pow_mul]
    simp
  simp_rw [hi]
  simp

theorem inverseCoefficientMatrix_det (φ : PowerSeries R) (s : ℕ) :
    (inverseCoefficientMatrix φ s).det = (-1 : R)^s *
      ((coefficientTriangular φ s).submatrix Fin.succ Fin.castSucc).det := by
  let B := (coefficientTriangular φ s).submatrix Fin.succ Fin.castSucc
  have he : inverseCoefficientMatrix φ s =
      Matrix.of (fun i j : Fin s => (-1 : R)^i.val *
        (Matrix.of (fun l r : Fin s => (-1 : R)^(r.val+1) * Bᵀ l r)) i j) := by
    ext i j
    rfl
  rw [he, Matrix.det_mul_column, Matrix.det_mul_row, ← mul_assoc, sign_products,
    Matrix.det_transpose]

/-- The reciprocal coefficient equals a genuine finite determinant.  The
proof uses only actual multiplication coefficients and the adjugate identity. -/
theorem coeff_inverse_eq_det (φ : PowerSeries R) (hφ : φ.constantCoeff = 1) (s : ℕ) :
    PowerSeries.coeff s (PowerSeries.invOfUnit φ 1) = (inverseCoefficientMatrix φ s).det := by
  let T := coefficientTriangular φ s
  let v : Fin (s+1) → R := fun j => PowerSeries.coeff j.val (PowerSeries.invOfUnit φ 1)
  have hv : T *ᵥ v = Pi.single 0 1 := coefficientTriangular_inverse_column φ hφ s
  have hd : T.det = 1 := coefficientTriangular_det φ hφ s
  have he := congrArg (fun w : Fin (s+1) → R => T.adjugate *ᵥ w) hv
  rw [Matrix.mulVec_mulVec, Matrix.adjugate_mul, hd, one_smul,
    Matrix.one_mulVec, Matrix.mulVec_single_one] at he
  have hc := congrFun he (Fin.last s)
  change PowerSeries.coeff s (PowerSeries.invOfUnit φ 1) = T.adjugate (Fin.last s) 0 at hc
  rw [Matrix.adjugate_fin_succ_eq_det_submatrix] at hc
  simp only [Fin.val_zero, Fin.val_last, Nat.zero_add, Fin.zero_succAbove,
    Fin.succAbove_last] at hc
  rw [inverseCoefficientMatrix_det]
  exact hc

end PaperVerification.PowerSeriesInverseDeterminant
