module
public import shared_results.part024
public import mixed_results.mixed_integer_betti_polynomial

set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

@[expose] public section

/- BEGIN EXACT BODY: FourPapers.Sublattice.MixedBettiPolynomialTransfer -/
section

/-! # The mixed Betti formulas for the original homogeneous ideals

This applies the complete transfer theorem to the literal initial products.
All internal degrees remain integers, including the vanishing negative
normalized strands. No polynomial or coefficient is defined from the answer.
-/

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
noncomputable section
namespace FourPapers.Sublattice
open Classical CommAlg MvPolynomial
open FourPapers.MultichainCounting
attribute [local instance] MvPolynomial.weightedGradedAlgebra
universe u
variable {K : Type u} [Field K] {d r : ℕ} (n : Fin d → ℕ)
  (E : Fin r → Finset (FiniteTuple n)) (hE : ColoredLatticeClosed n E)
  (M : MonomialOrder (FiniteVariable.{u} n))
  (J : ULift.{u} (Fin r) → Ideal (MvPolynomial (FiniteVariable.{u} n) K))
  (hinit : ∀ a, FourPapers.initialIdeal M (powerProduct J a) =
    powerProduct (coloredIdeals (k := K) n E) a)
  (hJ : ∀ c, (J c).IsHomogeneous
    (weightedHomogeneousSubmodule K (fun _ : FiniteVariable.{u} n => (1 : ℕ))))


/-- The two ordinary integer presentations are the identical actual Tor
submodule; their homogeneous-ideal proofs are propositionally irrelevant. -/
theorem mixedIntegerMonomialBettiNumber_eq_literal
    (m : ULift.{u} (Fin r) →₀ ℕ) (p : ℕ) (q : ℤ) :
    mixedIntegerMonomialBettiNumber (K := K) n E M m p q =
      integerMixedTorBettiNumber (k := K) (E := E) M m p q := rfl

variable (hβ : ∀ c p q,
  mixedPowerBettiNumber n E M J hinit hJ (Finsupp.single c 1) p q =
    mixedMonomialBettiNumber (K := K) n E (Finsupp.single c 1) p q)

include hE hβ in
/-- The ordinary graded specialization of (5.2) for every original mixed
product, including the empty product. -/
theorem mixed_integer_chain_formula_transfer
    (m : ULift.{u} (Fin r) →₀ ℕ) (p : ℕ) (q : ℤ) :
    mixedIntegerPowerBettiNumber n E M J hinit hJ m p ((m.degree*d : ℕ)+q) =
      ∑ w : MixedColorChain (E := E) m,
        integerOrdinaryQuotientBettiNumber (K := K)
          (sameColorChainCoefficientFamily E w.val) q p := by
  rw [theorem55_betti n E hE M J hinit hJ hβ,
    mixedIntegerMonomialBettiNumber_eq_literal]
  exact mixed_integer_ordinary_chain_formula M hE m p q

include hE hβ in
/-- One explicit multivariate polynomial gives the normalized Betti entry
of every positive mixed product of the original ideals. -/
theorem mixed_integer_polynomial_transfer
    (m : ULift.{u} (Fin r) →₀ ℕ) (hm : ∀ c, 0 < m c) (p : ℕ) (q : ℤ) :
    MvPolynomial.eval (fun c => (m c : ℚ))
      (integerMixedBettiPolynomial (k := K) (E := E) q p) =
        (mixedIntegerPowerBettiNumber n E M J hinit hJ m p
          ((m.degree*d : ℕ)+q) : ℚ) := by
  rw [theorem55_betti n E hE M J hinit hJ hβ,
    mixedIntegerMonomialBettiNumber_eq_literal]
  exact mixed_integer_positive_polynomial M hE m hm p q

end FourPapers.Sublattice

#print axioms FourPapers.Sublattice.mixed_integer_chain_formula_transfer
#print axioms FourPapers.Sublattice.mixed_integer_polynomial_transfer

end
end
end


end
