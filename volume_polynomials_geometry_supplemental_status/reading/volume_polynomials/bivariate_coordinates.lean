module

public import Mathlib.Algebra.Polynomial.Bivariate
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.FinCases

@[expose] public section

/-! # Faithful conversion between two polynomial representations -/

open Polynomial
open scoped Polynomial.Bivariate

namespace VolumePolynomials

/-- Coordinate zero becomes the outer variable; coordinate one the inner variable. -/
noncomputable def twoVariableEquiv :
    MvPolynomial (Fin 2) ℝ ≃ₐ[ℝ] ℝ[X][Y] :=
  (Polynomial.Bivariate.equivMvPolynomial ℝ).symm.trans Polynomial.Bivariate.swap

theorem twoVariableEquiv_eval (p : MvPolynomial (Fin 2) ℝ) (s y : ℝ) :
    (twoVariableEquiv p).evalEval y s = MvPolynomial.eval ![s, y] p := by
  induction p using MvPolynomial.induction_on with
  | C a =>
      simp [twoVariableEquiv, Polynomial.Bivariate.swap_C_C]
  | add p q hp hq =>
      simpa only [map_add, evalEval_add, MvPolynomial.eval_add] using congrArg₂ (· + ·) hp hq
  | mul_X p i hp =>
      rw [map_mul, evalEval_mul, MvPolynomial.eval_mul, hp]
      congr 1
      fin_cases i <;>
        simp [twoVariableEquiv,
          Polynomial.Bivariate.swap_X, Polynomial.Bivariate.swap_Y,
          evalEval_C]

/-- Swapping the two variables preserves their actual scalar evaluations. -/
theorem bivariate_eval_swap (p : ℝ[X][Y]) (s y : ℝ) :
    (Polynomial.Bivariate.swap p).evalEval s y = p.evalEval y s := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, evalEval_add, hp, hq]
  | monomial n a =>
      rw [Polynomial.Bivariate.swap_monomial, evalEval_mul, evalEval_map_C,
        evalEval_C]
      simp only [evalEval, eval_monomial, eval_mul, eval_pow, eval_C, eval_X]

/-- Substituting a polynomial into the outer variable commutes with scalar evaluation. -/
theorem bivariate_eval_polynomial (p : ℝ[X][Y]) (q : ℝ[X]) (y : ℝ) :
    (p.eval q).eval y = p.evalEval y (q.eval y) := by
  induction p using Polynomial.induction_on' with
  | add p r hp hr => simp only [eval_add, evalEval_add, hp, hr]
  | monomial n a => simp only [eval_monomial, eval_mul, eval_pow, evalEval, eval_C]

end VolumePolynomials
