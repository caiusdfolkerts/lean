module

public import PaperVerification.FermionOrdinaryParameters
public import PaperVerification.FermionCompleteIntersectionLength
public import Mathlib.Data.Nat.Factorial.BigOperators

/-!
# The exact length of the ordinary power-moment quotient

This specializes the proved weighted complete-intersection formula to the
actual first `n` ordinary moments. The coefficient hypothesis is precisely
invertibility of all nonempty subset sums; no characteristic-zero assumption
or pre-existing dimension formula is used.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PaperVerification.Fermion

open scoped BigOperators
open MvPolynomial

variable {K : Type*} [Field K] {n : ℕ}

theorem coveringWeight_product (r : Fin n → ℕ) :
    (∏ i, r i) * (∏ i, coveringWeight r i) = (∏ i, r i) ^ n := by
  rw [← Finset.prod_mul_distrib]
  simp only [coveringWeight_mul, Fin.prod_const]

/-- The ordinary quotient has the full length used in the paper's Frobenius
and harmonic arguments, for every positive covering degree. -/
theorem powerMoment_quotient_finrank_product
    (r : Fin n → ℕ) (β : Fin n → K) (s : ℕ)
    (hr : ∀ i, 0 < r i) (hs : 0 < s)
    (hβ : ∀ U : Finset (Fin n), U.Nonempty → IsUnit (∑ i ∈ U, β i)) :
    Module.finrank K (MvPolynomial (Fin n) K ⧸ powerMomentIdeal r β s) =
      (∏ i, r i) * ∏ k : Fin n, (s + (k : ℕ)) := by
  letI : Module.Finite K
      (MvPolynomial (Fin n) K ⧸ Ideal.span (Set.range fun k : Fin n ↦ powerMoment r β s k)) :=
    powerMoment_quotient_finite r β s hβ
  have h := GradedHilbert.weighted_complete_intersection_finrank
    (coveringWeight r) (coveringWeight_positive r hr)
    (fun k : Fin n ↦ powerMoment r β s k)
    (fun k : Fin n ↦ (∏ i, r i) * (s + (k : ℕ)))
    (fun k ↦ powerMoment_homogeneous r β s k)
    (powerMoments_isWeaklyRegular r β s hr hs hβ)
  change Module.finrank K (MvPolynomial (Fin n) K ⧸ powerMomentIdeal r β s) *
      (∏ i, coveringWeight r i) = ∏ k : Fin n, (∏ i, r i) * (s + (k : ℕ)) at h
  rw [Finset.prod_mul_distrib, Fin.prod_const, ← coveringWeight_product r] at h
  have hW : (∏ i, coveringWeight r i) ≠ 0 :=
    (Finset.prod_pos fun i _ ↦ coveringWeight_positive r hr i).ne'
  apply mul_right_cancel₀ hW
  calc
    _ = ((∏ i, r i) * (∏ i, coveringWeight r i)) *
        ∏ k : Fin n, (s + (k : ℕ)) := h
    _ = _ := by ac_rfl

/-- The paper writes the rising-factorial factor as `(s)ₙ`. -/
theorem powerMoment_quotient_finrank
    (r : Fin n → ℕ) (β : Fin n → K) (s : ℕ)
    (hr : ∀ i, 0 < r i) (hs : 0 < s)
    (hβ : ∀ U : Finset (Fin n), U.Nonempty → IsUnit (∑ i ∈ U, β i)) :
    Module.finrank K (MvPolynomial (Fin n) K ⧸ powerMomentIdeal r β s) =
      (∏ i, r i) * s.ascFactorial n := by
  rw [powerMoment_quotient_finrank_product r β s hr hs hβ,
    Nat.ascFactorial_eq_prod_range, Fin.prod_univ_eq_prod_range]

end PaperVerification.Fermion
