module

public import VolumePolynomials.CubicSlice

@[expose] public section

set_option autoImplicit false
noncomputable section

/-! # The exact higher-dimensional coefficient slice

These definitions and evaluation lemmas are shared by the two geometric
implications. Their declaration bodies are preserved from HigherLiftConverse;
no construction or existence of a realizing tuple is part of this specification.
-/

open Set MeasureTheory MvPolynomial
open scoped Pointwise BigOperators

namespace VolumePolynomials.HigherLift

def correction (k : ℕ) : ℝ := 2 * (k + 1 : ℝ) / (k + 2 : ℝ)

def polynomial (k : ℕ) (α s z : ℝ) : MvPolynomial (Fin 3) ℝ :=
  X 0 ^ k * CubicSlice.polynomial (correction k * α) s z

theorem polynomial_homogeneous (k : ℕ) (α s z : ℝ) :
    (polynomial k α s z).IsHomogeneous (3 + k) := by
  first
  | simpa only [polynomial, Nat.add_comm, one_mul] using
      ((isHomogeneous_X ℝ (0 : Fin 3)).pow k).mul
        (CubicSlice.polynomial_homogeneous (correction k * α) s z)

def coefficients (k : ℕ) (α s z : ℝ) : Coefficients 3 (3 + k) :=
  coefficientsOfPolynomial (polynomial k α s z)

theorem evaluate_coefficients (k : ℕ) (α s z : ℝ) (t : Fin 3 → ℝ) :
    evaluate (coefficients k α s z) t =
      t 0 ^ k * CubicSlice.value (correction k * α) s z t := by
  first
  | rw [coefficients, evaluate_eq_polynomial_eval,
      coefficientPolynomial_coefficientsOfPolynomial _ (polynomial_homogeneous k α s z)]
    simp only [polynomial, map_mul, map_pow, eval_X,
      ← CubicSlice.evaluate_coefficients, CubicSlice.coefficients,
      evaluate_eq_polynomial_eval,
      coefficientPolynomial_coefficientsOfPolynomial _
        (CubicSlice.polynomial_homogeneous (correction k * α) s z)]

end VolumePolynomials.HigherLift
