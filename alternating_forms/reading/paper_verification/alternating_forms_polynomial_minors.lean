module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.Polynomial.Eval.Defs

/-!
# Coefficient minors detected by an actual specialization

These lemmas concern matrices and polynomials themselves.  In particular, a
nonzero minor after specialization proves that the original minor is nonzero.
The coefficient version turns distinct monomial specializations into such a
minor and hence into linear independence.  The scaled version retains the
exact scalar factors removed during a polynomial normalization.
-/

@[expose] public section
noncomputable section

set_option autoImplicit false

namespace PaperVerification.AlternatingForms.PolynomialMinors

open scoped BigOperators

variable {R S σ ι : Type*} [CommRing R] [CommRing S]
variable [Fintype ι] [DecidableEq ι]

/-- An actual ring specialization to a nonzero determinant detects a nonzero
determinant in the original coefficient ring. -/
theorem det_ne_zero_of_specialization (φ : R →+* S) (A : Matrix ι ι R)
    (h : (φ.mapMatrix A).det ≠ 0) : A.det ≠ 0 := by
  intro hz
  apply h
  rw [← φ.map_det, hz, map_zero]

/-- A matrix that specializes to the identity has a nonzero determinant. -/
theorem det_ne_zero_of_map_eq_one [Nontrivial S] (φ : R →+* S)
    (A : Matrix ι ι R) (h : φ.mapMatrix A = 1) : A.det ≠ 0 := by
  apply det_ne_zero_of_specialization φ A
  rw [h, Matrix.det_one]
  exact one_ne_zero

/-- This form is convenient for matrices with polynomial entries. -/
theorem det_ne_zero_of_eval_zero_eq_one [Nontrivial R]
    (A : Matrix ι ι (Polynomial R))
    (h : (Polynomial.evalRingHom (0 : R)).mapMatrix A = 1) : A.det ≠ 0 :=
  det_ne_zero_of_map_eq_one (Polynomial.evalRingHom 0) A h

/-- Removing a separate nonzero factor from each specialized column preserves
the nonvanishing of the original minor. -/
theorem det_ne_zero_of_map_eq_column_scaled [IsDomain S]
    (φ : R →+* S) (A : Matrix ι ι R) (B : Matrix ι ι S) (c : ι → S)
    (hc : ∀ i, c i ≠ 0)
    (h : φ.mapMatrix A = fun i j => c j * B i j)
    (hB : B.det ≠ 0) : A.det ≠ 0 := by
  apply det_ne_zero_of_specialization φ A
  have h' : φ.mapMatrix A = Matrix.of (fun i j => c j * B i j) := h
  rw [h', Matrix.det_mul_row c B]
  exact mul_ne_zero (Finset.prod_ne_zero_iff.mpr (fun i _ => hc i)) hB

/-- Rows select monomial coefficients; columns are the actual vectors. -/
def coefficientMatrix (a : ι → σ →₀ ℕ) (p : ι → MvPolynomial σ R) :
    Matrix ι ι R := fun i j => (p j).coeff (a i)

theorem coefficientMatrix_map (φ : R →+* S) (a : ι → σ →₀ ℕ)
    (p : ι → MvPolynomial σ R) :
    φ.mapMatrix (coefficientMatrix a p) =
      coefficientMatrix a (fun i => MvPolynomial.map φ (p i)) := by
  ext i j
  exact (MvPolynomial.coeff_map φ (p j) (a i)).symm

/-- Distinct literal monomials give the identity coefficient matrix. -/
theorem coefficientMatrix_monomials (a : ι → σ →₀ ℕ)
    (ha : Function.Injective a) :
    coefficientMatrix a (fun i => MvPolynomial.monomial (a i) (1 : R)) = 1 := by
  classical
  ext i j
  simp [coefficientMatrix, Matrix.one_apply, ha.eq_iff, eq_comm]

theorem coefficientMatrix_map_eq_one (φ : R →+* S)
    (a : ι → σ →₀ ℕ) (ha : Function.Injective a)
    (p : ι → MvPolynomial σ R)
    (hp : ∀ i, MvPolynomial.map φ (p i) = MvPolynomial.monomial (a i) 1) :
    φ.mapMatrix (coefficientMatrix a p) = 1 := by
  rw [coefficientMatrix_map]
  simp_rw [hp]
  exact coefficientMatrix_monomials a ha

theorem coefficient_det_ne_zero_of_monomial_specialization [Nontrivial S]
    (φ : R →+* S) (a : ι → σ →₀ ℕ) (ha : Function.Injective a)
    (p : ι → MvPolynomial σ R)
    (hp : ∀ i, MvPolynomial.map φ (p i) = MvPolynomial.monomial (a i) 1) :
    (coefficientMatrix a p).det ≠ 0 :=
  det_ne_zero_of_map_eq_one φ _ (coefficientMatrix_map_eq_one φ a ha p hp)

/-- An invertible coefficient minor certifies independence of the complete
polynomials, not just their displayed coefficients. -/
theorem linearIndependent_of_coefficient_det_ne_zero [IsDomain R]
    (a : ι → σ →₀ ℕ) (p : ι → MvPolynomial σ R)
    (h : (coefficientMatrix a p).det ≠ 0) : LinearIndependent R p := by
  let f : MvPolynomial σ R →ₗ[R] (ι → R) :=
    LinearMap.pi (fun i => MvPolynomial.lcoeff R (a i))
  apply LinearIndependent.of_comp f
  exact Matrix.linearIndependent_cols_of_det_ne_zero h

theorem linearIndependent_of_monomial_specialization [IsDomain R] [Nontrivial S]
    (φ : R →+* S) (a : ι → σ →₀ ℕ) (ha : Function.Injective a)
    (p : ι → MvPolynomial σ R)
    (hp : ∀ i, MvPolynomial.map φ (p i) = MvPolynomial.monomial (a i) 1) :
    LinearIndependent R p :=
  linearIndependent_of_coefficient_det_ne_zero a p
    (coefficient_det_ne_zero_of_monomial_specialization φ a ha p hp)

end PaperVerification.AlternatingForms.PolynomialMinors
