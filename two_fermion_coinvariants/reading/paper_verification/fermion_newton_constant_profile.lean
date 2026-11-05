module

public import PaperVerification.FermionNewtonAllOneNonzero

/-!
# Constant multiplicities in the literal Newton matrix

Multiplication of a rational interpolation numerator by a polynomial scales
the entire column, including every forced residue, by its evaluations in the
corresponding rows. Thus every constant profile follows from the all-one
profile, including multiplicity zero.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PaperVerification.Fermion.Newton

open Polynomial
open scoped BigOperators Matrix

variable {L : Type*} [Field L] {n : ℕ}

def profileNumerator (δ : Fin n → ℕ) (σ : Fin n → ℤ) (x : Fin n → L) (i : Fin n) : L[X] :=
  X ^ δ i * Lagrange.nodal (earlierPositive σ i) x

def profileNewtonMatrix (δ : Fin n → ℕ) (σ : Fin n → ℤ)
    (x β : Fin n → L) : Matrix (Fin n) (Fin n) L :=
  fun k i ↦ rationalColumn (profileNumerator δ σ x i)
    (earlierNegative σ i) (activeInterval δ i) x β k

theorem profileNewtonMatrix_one (σ : Fin n → ℤ) (x β : Fin n → L) :
    profileNewtonMatrix (fun _ ↦ 1) σ x β = allOneNewtonMatrix σ x β := by
  ext k i
  simp only [profileNewtonMatrix, allOneNewtonMatrix, profileNumerator, allOneNumerator,
    pow_one, activeInterval_constant_eq_activeTail]

theorem profileNewtonMatrix_constant_row_scaling
    (d : ℕ) (σ : Fin n → ℤ) (x β : Fin n → L) :
    profileNewtonMatrix (fun _ ↦ d) σ x β =
      Matrix.diagonal (fun k ↦ x k ^ d) * profileNewtonMatrix (fun _ ↦ 0) σ x β := by
  ext k i
  rw [Matrix.diagonal_mul]
  change rationalColumn _ _ _ _ _ _ = _ * rationalColumn _ _ _ _ _ _
  rw [activeInterval_constant_eq_activeTail, activeInterval_constant_eq_activeTail]
  have hN : profileNumerator (fun _ : Fin n ↦ d) σ x i =
      profileNumerator (fun _ : Fin n ↦ 0) σ x i * X ^ d := by
    simp only [profileNumerator, pow_zero, one_mul]
    ring
  rw [hN, rationalColumn_mul_polynomial, eval_pow, eval_X]

theorem profileNewtonMatrix_constant_det_ne_zero
    (d : ℕ) (σ : Fin n → ℤ) (x β : Fin n → L)
    (hx : ∀ i, x i ≠ 0) (hM : (allOneNewtonMatrix σ x β).det ≠ 0) :
    (profileNewtonMatrix (fun _ ↦ d) σ x β).det ≠ 0 := by
  have hzero : (profileNewtonMatrix (fun _ ↦ 0) σ x β).det ≠ 0 := by
    intro hz
    apply hM
    rw [← profileNewtonMatrix_one, profileNewtonMatrix_constant_row_scaling 1,
      Matrix.det_mul, hz, mul_zero]
  rw [profileNewtonMatrix_constant_row_scaling d, Matrix.det_mul, Matrix.det_diagonal]
  exact mul_ne_zero (Finset.prod_ne_zero_iff.mpr (fun k hk ↦ pow_ne_zero d (hx k))) hzero

theorem profileNewtonMatrix_map {E : Type*} [Field E]
    (f : L →+* E) (δ : Fin n → ℕ) (σ : Fin n → ℤ) (x β : Fin n → L) :
    (profileNewtonMatrix δ σ x β).map f = profileNewtonMatrix δ σ (f ∘ x) (f ∘ β) := by
  ext k i
  change f (rationalColumn _ _ _ _ _ _) = _
  rw [rationalColumn_map_coefficients]
  have hN : (profileNumerator δ σ x i).map f = profileNumerator δ σ (f ∘ x) i := by
    simp only [profileNumerator, Polynomial.map_mul, Polynomial.map_pow,
      Polynomial.map_X, nodal_map_coefficients]
  rw [hN]
  rfl

variable (F : Type*) [Field F]

theorem constantProfileGeneric_det_ne_zero (n d : ℕ)
    (σ : Fin n → ℤ) (β : Fin n → F)
    (hσ : ∀ i, σ i = -1 ∨ σ i = 0 ∨ σ i = 1)
    (hβ : ∀ U : Finset (Fin n), U.Nonempty → IsUnit (∑ i ∈ U, β i)) :
    (profileNewtonMatrix (fun _ ↦ d) σ (successiveNode F n)
      (successiveBaseMap F n ∘ β)).det ≠ 0 :=
  profileNewtonMatrix_constant_det_ne_zero d σ _ _ (successiveNode_ne_zero F n)
    (allOneGeneric_det_and_pattern F n σ β hσ hβ).1

theorem newtonColumn_eq_profileNewtonMatrix
    (β : Fin n → F) (δ : Fin n → ℕ) (σ : Fin n → ℤ) (i k : Fin n) :
    newtonColumn β δ σ i k =
      profileNewtonMatrix δ σ (rationalNode (F := F))
        (fun j ↦ algebraMap F (RationalFunctions (F := F)) (β j)) k i := by
  simp only [newtonColumn, profileNewtonMatrix, columnNumerator,
    Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_prod,
    Polynomial.map_sub, Polynomial.map_C, profileNumerator, Lagrange.nodal, rationalNode]

theorem newtonColumn_constant_det_ne_zero (n d : ℕ)
    (σ : Fin n → ℤ) (β : Fin n → F)
    (hσ : ∀ i, σ i = -1 ∨ σ i = 0 ∨ σ i = 1)
    (hβ : ∀ U : Finset (Fin n), U.Nonempty → IsUnit (∑ i ∈ U, β i)) :
    Matrix.det (fun k i : Fin n ↦ newtonColumn β (fun _ ↦ d) σ i k) ≠ 0 := by
  simp_rw [newtonColumn_eq_profileNewtonMatrix F]
  apply profileNewtonMatrix_constant_det_ne_zero
  · intro i hi
    exact MvPolynomial.X_ne_zero i
      (IsFractionRing.injective (MvPolynomial (Fin n) F) (RationalFunctions (F := F))
        (by simpa only [rationalNode, map_zero] using hi))
  · exact allOneNewtonMatrix_rational_det_ne_zero F n σ β hσ hβ

end PaperVerification.Fermion.Newton
