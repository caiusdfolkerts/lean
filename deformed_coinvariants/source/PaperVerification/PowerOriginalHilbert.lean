module

public import PaperVerification.PowerOriginalAction
public import PaperVerification.PowerHilbertSeries
public import PaperVerification.GradedHilbertTransport

/-!
# The exact Hilbert polynomial for the original operator family

The grading has already been identified with the images of the literal
homogeneous polynomial pieces. Transport by the actual diagonal quotient
equivalence therefore gives the original family's printed Hilbert formula.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open MvPolynomial
open scoped BigOperators

namespace PaperVerification.PowerOperators

variable {K : Type*} [Field K] {n : ℕ}

theorem originalTail_hilbert_series_eq_reversed
    (c : Fin n → K) (lam : K) (m : ℕ)
    (h : ∀ i, ∀ a : ℕ, c i + lam*(a : K) ≠ 0) :
    GradedHilbert.series (originalTailQuotientGrading c lam m h) =
      GradedHilbert.series (tailQuotientGrading c lam m) :=
  GradedHilbert.series_map _ _

theorem originalTailQuotientDegree_finrank_eq_artin_card
    (c : Fin n → K) (lam : K) (m : ℕ) (hm : 0 < m)
    (hnr : Nonresonant c lam m)
    (hlow : ∀ i, ∀ a : ℕ, a < m → c i+lam*(a : K) ≠ 0) (d : ℕ) :
    Module.finrank K (originalTailQuotientDegree c lam m d) =
      Fintype.card {a : ArtinIndex n m // a.val.degree=d} := by
  have he := congrArg (PowerSeries.coeff d)
    (originalTail_hilbert_series_eq_reversed c lam m (coordinate_factor_ne_zero hnr hlow))
  simp only [GradedHilbert.coeff_series] at he
  rw [originalTailQuotientGrading_piece, tailQuotientGrading_piece,
    tailQuotientDegree_finrank_eq_artin_card c lam m hm hnr] at he
  exact_mod_cast he

theorem paper_theorem_2_2_original_hilbert_polynomial
    (c : Fin n → K) (lam : K) (m : ℕ) (hm : 0 < m)
    (hnr : Nonresonant c lam m)
    (hlow : ∀ i, ∀ a : ℕ, a < m → c i+lam*(a : K) ≠ 0) :
    GradedHilbert.series
        (originalTailQuotientGrading c lam m (coordinate_factor_ne_zero hnr hlow)) =
      ((∏ j ∈ Finset.Ico m (m+n), qIntegerPolynomial j : Polynomial ℤ) :
        PowerSeries ℤ) := by
  rw [originalTail_hilbert_series_eq_reversed,
    paper_theorem_2_2_hilbert_polynomial c lam m hm hnr]

end PaperVerification.PowerOperators
