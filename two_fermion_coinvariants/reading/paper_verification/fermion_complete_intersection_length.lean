module

public import PaperVerification.FermionIdealHilbert
public import PaperVerification.FermionFiniteGrading
public import Mathlib.Algebra.Ring.GeomSum

/-!
# The length of a weighted homogeneous complete intersection

The actual regular sequence gives its Hilbert-series identity. Finiteness
turns that series into a polynomial. Cancellation of the proved factor
`(1-X)^n` and evaluation at one give the complete weighted length formula.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PaperVerification.GradedHilbert

open scoped BigOperators
open MvPolynomial

variable {K : Type*} [Field K] {n : ℕ}

local notation "P" => MvPolynomial (Fin n) K

/-- The finite geometric polynomial, including the zero-degree case. -/
def geometricPolynomial (d : ℕ) : Polynomial ℤ :=
  ∑ j ∈ Finset.range d, Polynomial.X ^ j

theorem one_sub_X_pow_eq (d : ℕ) :
    (1 - Polynomial.X ^ d : Polynomial ℤ) = (1 - Polynomial.X) * geometricPolynomial d :=
  (mul_neg_geom_sum Polynomial.X d).symm

@[simp] theorem geometricPolynomial_eval_one (d : ℕ) :
    (geometricPolynomial d).eval 1 = (d : ℤ) := by
  simp [geometricPolynomial, Polynomial.eval_finsetSum]

theorem product_one_sub_X_pow (d : Fin n → ℕ) :
    (∏ i, (1 - Polynomial.X ^ d i : Polynomial ℤ)) =
      (1 - Polynomial.X) ^ n * ∏ i, geometricPolynomial (d i) := by
  simp only [one_sub_X_pow_eq, Finset.prod_mul_distrib, Fin.prod_const]

/-- A formal power-series Hilbert identity yields the exact weighted length
once the actual quotient is finite. The factor cancellation is in `ℤ[X]`,
so it introduces no restriction on the characteristic of the coefficient field. -/
theorem length_of_hilbert_identity
    {M : Type*} [AddCommGroup M] [Module K M] [Module.Finite K M]
    (G : TauCeti.InternalGrading K M ℕ) (w degree : Fin n → ℕ)
    (h : (∏ i, (1 - PowerSeries.X ^ w i)) * series G =
      ∏ j, (1 - PowerSeries.X ^ degree j)) :
    Module.finrank K M * (∏ i, w i) = ∏ j, degree j := by
  have hp : (∏ i, (1 - Polynomial.X ^ w i : Polynomial ℤ)) * hilbertPolynomial G =
      ∏ j, (1 - Polynomial.X ^ degree j : Polynomial ℤ) := by
    apply Polynomial.coe_injective ℤ
    change Polynomial.coeToPowerSeries.ringHom
      ((∏ i, (1 - Polynomial.X ^ w i : Polynomial ℤ)) * hilbertPolynomial G) =
      Polynomial.coeToPowerSeries.ringHom (∏ j, (1 - Polynomial.X ^ degree j : Polynomial ℤ))
    simpa only [map_mul, map_prod, map_sub, map_one, map_pow,
      Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_X,
      hilbertPolynomial_coe] using h
  rw [product_one_sub_X_pow, product_one_sub_X_pow, mul_assoc] at hp
  have hnonzero : (1 - Polynomial.X : Polynomial ℤ) ^ n ≠ 0 := by
    apply pow_ne_zero
    intro hzero
    have hc := congrArg (fun p : Polynomial ℤ ↦ p.coeff 0) hzero
    simpa using hc
  have hc := mul_left_cancel₀ hnonzero hp
  have he := congrArg (Polynomial.eval (1 : ℤ)) hc
  simp only [Polynomial.eval_mul, Polynomial.eval_prod, geometricPolynomial_eval_one,
    hilbertPolynomial_eval_one] at he
  have hn : (∏ i, w i) * Module.finrank K M = ∏ j, degree j := by
    exact_mod_cast he
  simpa only [Nat.mul_comm] using hn

/-- The full weighted homogeneous complete-intersection dimension theorem.

Every hypothesis concerns the actual generators or the actual quotient.
In particular no Hilbert function, colength formula, or missing exactness
statement occurs among the assumptions.
-/
theorem weighted_complete_intersection_finrank
    (w : Fin n → ℕ) (hw : ∀ i, 0 < w i)
    (f : Fin n → P) (degree : Fin n → ℕ)
    (hhom : ∀ i, (f i).IsWeightedHomogeneous w (degree i))
    (hregular : RingTheory.Sequence.IsWeaklyRegular P (List.ofFn f))
    [Module.Finite K (P ⧸ Ideal.span (Set.range f))] :
    Module.finrank K (P ⧸ Ideal.span (Set.range f)) * (∏ i, w i) =
      ∏ j, degree j :=
  length_of_hilbert_identity (familyGrading w f degree hhom) w degree
    (regular_family_hilbert_identity w hw f degree hhom hregular)

/-- Ordinary homogeneous complete intersections have dimension equal to the
product of the degrees, in every characteristic. -/
theorem homogeneous_complete_intersection_finrank
    (f : Fin n → P) (degree : Fin n → ℕ)
    (hhom : ∀ i, (f i).IsWeightedHomogeneous (fun _ ↦ 1) (degree i))
    (hregular : RingTheory.Sequence.IsWeaklyRegular P (List.ofFn f))
    [Module.Finite K (P ⧸ Ideal.span (Set.range f))] :
    Module.finrank K (P ⧸ Ideal.span (Set.range f)) = ∏ j, degree j := by
  simpa using weighted_complete_intersection_finrank (fun _ ↦ 1) (by simp)
    f degree hhom hregular

end PaperVerification.GradedHilbert
