module

public import PaperVerification.FermionFiniteGrading
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Lean.Elab.Tactic.Omega

/-!
# Equality in every degree from total dimension and degreewise inequalities

The argument uses the complete Hilbert polynomials of the two actual finite
graded spaces. The coefficientwise nonnegative difference has value zero at
one, so all its coefficients vanish. No truncation degree is supplied.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open scoped BigOperators

namespace PaperVerification.GradedHilbert

theorem polynomial_coeff_eq_zero_of_nonneg_of_eval_one_eq_zero (p : Polynomial ℤ)
    (hp : ∀ d, 0 ≤ p.coeff d) (he : p.eval 1 = 0) (d : ℕ) : p.coeff d = 0 := by
  have hsum : ∑ i ∈ p.support, p.coeff i = 0 := by
    simpa only [Polynomial.eval_eq_sum,Polynomial.sum,one_pow,mul_one] using he
  by_cases hd : d ∈ p.support
  · exact (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hp i)).mp hsum d hd
  · exact Polynomial.notMem_support_iff.mp hd

theorem piece_finrank_eq_of_piece_finrank_le_of_finrank_eq
    {K L V W : Type*} [Field K] [Field L]
    [AddCommGroup V] [Module K V] [Module.Finite K V]
    [AddCommGroup W] [Module L W] [Module.Finite L W]
    (GV : TauCeti.InternalGrading K V ℕ) (GW : TauCeti.InternalGrading L W ℕ)
    (hle : ∀ d, Module.finrank K (GV.piece d) ≤ Module.finrank L (GW.piece d))
    (he : Module.finrank K V = Module.finrank L W) (d : ℕ) :
    Module.finrank K (GV.piece d) = Module.finrank L (GW.piece d) := by
  let p := hilbertPolynomial GW - hilbertPolynomial GV
  have hp : ∀ e, 0 ≤ p.coeff e := by
    intro e
    change 0 ≤ (hilbertPolynomial GW - hilbertPolynomial GV).coeff e
    rw [Polynomial.coeff_sub,hilbertPolynomial_coeff,hilbertPolynomial_coeff]
    exact sub_nonneg.mpr (Int.ofNat_le.mpr (hle e))
  have hsum : p.eval 1 = 0 := by
    change (hilbertPolynomial GW - hilbertPolynomial GV).eval 1 = 0
    rw [Polynomial.eval_sub,hilbertPolynomial_eval_one,hilbertPolynomial_eval_one,he,sub_self]
  have hz := polynomial_coeff_eq_zero_of_nonneg_of_eval_one_eq_zero p hp hsum d
  change (hilbertPolynomial GW - hilbertPolynomial GV).coeff d = 0 at hz
  rw [Polynomial.coeff_sub,hilbertPolynomial_coeff,hilbertPolynomial_coeff] at hz
  omega

end PaperVerification.GradedHilbert
