module

public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.LinearAlgebra.Span.Basic

/-!
# The scalar moment recurrence

Monic division by the actual characteristic polynomial expresses every
module-valued moment in terms of the first `n`. No noncommutative quotient
machinery is required in this leaf module.
-/

@[expose] public section

set_option autoImplicit false

namespace PaperVerification.Fermion

open scoped BigOperators
open Polynomial

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
variable {n : ℕ}

/-- A moment with commuting scalar parameters and arbitrary module coefficients. -/
def moment (x : Fin n → R) (v : Fin n → M) (k : ℕ) : M :=
  ∑ i, x i ^ k • v i

/-- The monic polynomial whose listed roots are the moment parameters. -/
noncomputable def parameterPolynomial (x : Fin n → R) : R[X] :=
  ∏ i, (X - C (x i))

theorem parameterPolynomial_monic (x : Fin n → R) :
    (parameterPolynomial x).Monic := by
  exact monic_prod_of_monic _ _ fun i _ ↦ monic_X_sub_C (x i)

theorem parameterPolynomial_degree_le (x : Fin n → R) :
    (parameterPolynomial x).degree ≤ n := by
  nontriviality R
  rw [degree_eq_natDegree (parameterPolynomial_monic x).ne_zero]
  simp [parameterPolynomial]

theorem parameterPolynomial_eval (x : Fin n → R) (i : Fin n) :
    (parameterPolynomial x).eval (x i) = 0 := by
  classical
  rw [parameterPolynomial, eval_prod]
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  simp

/-- All scalar powers have the same remainder formula simultaneously at the parameters. -/
theorem powers_as_remainder (x : Fin n → R) (k : ℕ) (i : Fin n) :
    x i ^ k = ∑ j : Fin n,
      ((X ^ k) %ₘ parameterPolynomial x).coeff j * x i ^ (j : ℕ) := by
  have h := congrArg (fun p : R[X] ↦ p.eval (x i))
    (modByMonic_add_div (X ^ k) (parameterPolynomial x))
  simp only [eval_add, eval_mul, parameterPolynomial_eval, zero_mul, add_zero,
    eval_pow, eval_X] at h
  have hh := congrArg (fun p : R[X] ↦ p.eval (x i))
    (sum_modByMonic_coeff (p := X ^ k) (parameterPolynomial_monic x)
      (parameterPolynomial_degree_le x))
  simpa only [eval_finsetSum, eval_monomial] using h.symm.trans hh.symm

/-- Every moment is a linear combination of the first `n` moments. -/
theorem moment_eq_sum_first (x : Fin n → R) (v : Fin n → M) (k : ℕ) :
    moment x v k = ∑ j : Fin n,
      ((X ^ k) %ₘ parameterPolynomial x).coeff j • moment x v (j : ℕ) := by
  unfold moment
  simp_rw [powers_as_remainder x k, Finset.sum_smul, mul_smul]
  rw [Finset.sum_comm]
  simp_rw [Finset.smul_sum]

/-- The infinite list of moments has exactly the span of its first `n` entries. -/
theorem moment_span_eq (x : Fin n → R) (v : Fin n → M) :
    Submodule.span R (Set.range (moment x v)) =
      Submodule.span R (Set.range fun j : Fin n ↦ moment x v (j : ℕ)) := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    rw [moment_eq_sum_first]
    exact Submodule.sum_mem _ fun j _ ↦
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  · apply Submodule.span_mono
    rintro _ ⟨j, rfl⟩
    exact ⟨(j : ℕ), rfl⟩

/-- Vanishing of all moments is equivalent to vanishing of the first `n`. -/
theorem all_moments_eq_zero_iff (x : Fin n → R) (v : Fin n → M) :
    (∀ k : ℕ, moment x v k = 0) ↔
      ∀ j : Fin n, moment x v (j : ℕ) = 0 := by
  refine ⟨fun h j ↦ h j, ?_⟩
  intro h k
  rw [moment_eq_sum_first]
  simp [h]

/-- Increasing the starting index is absorbed into the coefficients. -/
theorem moment_shift (x : Fin n → R) (v : Fin n → M) (q k : ℕ) :
    moment x (fun i ↦ x i ^ q • v i) k = moment x v (k + q) := by
  simp only [moment, pow_add, mul_smul]

end PaperVerification.Fermion
