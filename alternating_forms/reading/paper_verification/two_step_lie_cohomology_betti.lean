module

public import PaperVerification.TwoStepLieCohomology
public import PaperVerification.AlternatingFormsBettiOrigin

/-!
# The paper's Lie-cohomology formula with the actual ordinary Tor polynomial

This final comparison substitutes the independently established ordinary
Tor identification from Proposition 5.4 into the actual CE Poincare formula.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

namespace PaperVerification.TwoStepLieCohomology

open AlternatingForms

variable {K M : Type u} [Field K] [AddCommGroup M] [Module K M]
  [FiniteDimensional K M]

/-- The full graded Lie-cohomology formula following Proposition 5.4,
with `B₁` defined by ordinary Mathlib Tor over the actual polynomial ring
and its coefficient field at the origin. -/
theorem paper_lie_cohomology_poincare (f g : ⋀[K]^2 M) :
    poincarePolynomial f g = exteriorQuotientHilbert f g +
      (LaurentPolynomial.T (-1) * exteriorOriginBettiPolynomial f g 1 +
        LaurentPolynomial.T ((Module.finrank K M : ℤ) + 2) *
          LaurentPolynomial.invert (exteriorQuotientHilbert f g)) := by
  rw [exteriorOriginBettiPolynomial_eq, exteriorBettiPolynomial_one]
  exact poincare_formula f g

/-- The same formula explicitly identifies each genuine categorical
cohomology dimension, in every integer degree. -/
theorem paper_lie_cohomology_degree (f g : ⋀[K]^2 M) (q : ℤ) :
    (Module.finrank K (cohomology f g q) : ℤ) =
      (exteriorQuotientHilbert f g +
        (LaurentPolynomial.T (-1) * exteriorOriginBettiPolynomial f g 1 +
          LaurentPolynomial.T ((Module.finrank K M : ℤ) + 2) *
            LaurentPolynomial.invert (exteriorQuotientHilbert f g))).coeff q := by
  rw [← poincarePolynomial_coeff, paper_lie_cohomology_poincare]

/-- The Poincare series is an ordinary polynomial. Its use of Laurent
notation in the formula does not add negative cohomological degrees. -/
theorem poincarePolynomial_is_ordinary (f g : ⋀[K]^2 M) :
    ∃! P : Polynomial ℤ, P.toLaurent = poincarePolynomial f g := by
  refine ⟨LaurentPolynomial.trunc (poincarePolynomial f g),
    toLaurent_trunc_of_nonnegative _ (fun q hq ↦ poincarePolynomial_negative f g hq), ?_⟩
  intro P hP
  apply Polynomial.toLaurent_injective
  rw [hP, toLaurent_trunc_of_nonnegative _ (fun q hq ↦ poincarePolynomial_negative f g hq)]

end PaperVerification.TwoStepLieCohomology
