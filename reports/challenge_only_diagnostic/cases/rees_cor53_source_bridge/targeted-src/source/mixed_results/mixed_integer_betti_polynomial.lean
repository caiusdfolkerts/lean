module
public import shared_results.part024
public import shared_results.part023

set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

@[expose] public section

/- BEGIN EXACT BODY: FourPapers.Sublattice.MixedIntegerBettiPolynomial -/
section

/-! # The mixed positive-binomial formula in all integer degrees

The normalized internal degree is an arbitrary integer. Negative normalized
degrees vanish in the actual derived Tor. The polynomial includes the empty
color set as a constant-polynomial case, so the unique vector with no color
coordinates is included as well.
-/

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 700000
noncomputable section
namespace FourPapers.Sublattice
open Classical CommAlg.Polymatroid
open FourPapers.MultichainCounting
universe u
variable {k : Type u} [Field k] {d r : ℕ} {n : Fin d → ℕ}
  {E : Fin r → Finset (FiniteTuple n)}
variable (o : MonomialOrder (FiniteVariable.{u} n))

def integerMixedTorBettiNumber (m : ULift.{u} (Fin r) →₀ ℕ) (p : ℕ) (q : ℤ) : ℕ :=
  integerMonomialTorBettiNumber (K := k) o (mixedRowPowerFamily n E m) p q

@[simp] theorem integerMixedTorBettiNumber_nat
    (m : ULift.{u} (Fin r) →₀ ℕ) (p q : ℕ) :
    integerMixedTorBettiNumber (k := k) (E := E) o m p (q : ℤ) =
      ordinaryMonomialBettiNumber (k := k) (mixedRowPowerFamily n E m) q p :=
  integerMonomialTorBettiNumber_nat o _ p q

theorem integerMixedTorBettiNumber_negative
    (m : ULift.{u} (Fin r) →₀ ℕ) (p : ℕ) (q : ℤ) (hq : q < 0) :
    integerMixedTorBettiNumber (k := k) (E := E) o m p q = 0 :=
  integerMonomialTorBettiNumber_negative o _ p q hq

theorem integerMixedTorBettiNumber_zero_below (hE : ColoredLatticeClosed n E)
    (m : ULift.{u} (Fin r) →₀ ℕ) (p : ℕ) (Q : ℤ) (hQ : Q < (m.degree*d : ℕ)) :
    integerMixedTorBettiNumber (k := k) (E := E) o m p Q = 0 := by
  by_cases hQ0 : 0 ≤ Q
  · obtain ⟨a,rfl⟩ := Int.eq_ofNat_of_zero_le hQ0
    rw [integerMixedTorBettiNumber_nat]
    exact ordinaryMixedBetti_zero_below hE m a p (by exact_mod_cast hQ)
  · exact integerMixedTorBettiNumber_negative o m p Q (lt_of_not_ge hQ0)

/-- Equation (5.2), summed in any integer ordinary degree, with the exact
chain-monomial shift and the actual coefficient quotient Tor. -/
theorem mixed_integer_ordinary_chain_formula (hE : ColoredLatticeClosed n E)
    (m : ULift.{u} (Fin r) →₀ ℕ) (p : ℕ) (q : ℤ) :
    integerMixedTorBettiNumber (k := k) (E := E) o m p ((m.degree*d : ℕ)+q) =
      ∑ w : MixedColorChain (E := E) m,
        integerOrdinaryQuotientBettiNumber (K := k)
          (sameColorChainCoefficientFamily E w.val) q p := by
  by_cases hq : 0 ≤ q
  · obtain ⟨a,rfl⟩ := Int.eq_ofNat_of_zero_le hq
    rw [← Nat.cast_add,integerMixedTorBettiNumber_nat]
    simp only [integerOrdinaryQuotientBettiNumber_nat]
    exact ordinaryMixedBetti_chain_sum hE m a p
  · have hneg := lt_of_not_ge hq
    rw [integerMixedTorBettiNumber_zero_below o hE m p _ (by omega)]
    symm
    apply Finset.sum_eq_zero
    intro w _
    exact integerOrdinaryQuotientBettiNumber_negative _ q hneg p

/-- The empty product has the independently specified quotient-Tor
coefficient of the polynomial ring itself. -/
theorem integerMixedTorBettiNumber_zero (hE : ColoredLatticeClosed n E)
    (p : ℕ) (q : ℤ) :
    integerMixedTorBettiNumber (k := k) (E := E) o 0 p q =
      integerOrdinaryQuotientBettiNumber (K := k)
        (∅ : Family (FiniteVariable.{u} n)) q p := by
  letI : Unique (MixedColorChain.{u} (E := E) 0) := {
    default := ⟨emptyColoredChain, by simp [chainColorCount, emptyColoredChain]⟩
    uniq := fun w => by
      apply Subtype.ext
      apply Subtype.ext
      funext i
      exact Fin.elim0 i }
  simpa only [map_zero, zero_mul, Nat.cast_zero, zero_add,
    Fintype.sum_unique, sameColorChainCoefficientFamily_empty] using
      mixed_integer_ordinary_chain_formula o hE 0 p q

def integerColoredSupportBettiCoefficient (q : ℤ) (p : ℕ)
    (s : StrictSupport (coloredFamily n E)) : ℕ :=
  if Function.Surjective (fun a : s.val => coloredSupportColor.{u} (E := E) a.val) then
    integerOrdinaryQuotientBettiNumber (K := k) (coloredStrictSupportCoefficientFamily s) q p
  else 0

@[simp] theorem integerColoredSupportBettiCoefficient_nat (q p : ℕ)
    (s : StrictSupport (coloredFamily n E)) :
    integerColoredSupportBettiCoefficient (k := k) (q : ℤ) p s =
      coloredStrictSupportBettiCoefficient (k := k) q p s := by
  simp only [integerColoredSupportBettiCoefficient,coloredStrictSupportBettiCoefficient,
    integerOrdinaryQuotientBettiNumber_nat]

theorem integerColoredSupportBettiCoefficient_negative (q : ℤ) (hq : q < 0) (p : ℕ)
    (s : StrictSupport (coloredFamily n E)) :
    integerColoredSupportBettiCoefficient (k := k) q p s = 0 := by
  simp only [integerColoredSupportBettiCoefficient,
    integerOrdinaryQuotientBettiNumber_negative _ q hq p,ite_self]

theorem mixed_integer_positive_binomial_formula (hE : ColoredLatticeClosed n E)
    (m : ULift.{u} (Fin r) →₀ ℕ) (hm : ∀ c, 0 < m c)
    (hM : 0 < m.degree) (p : ℕ) (q : ℤ) :
    integerMixedTorBettiNumber (k := k) (E := E) o m p ((m.degree*d : ℕ)+q) =
      ∑ s : StrictSupport (coloredFamily n E),
        integerColoredSupportBettiCoefficient (k := k) q p s *
          ∏ c, (m c-1).choose (coloredStrictSupportBinomialDegree s c) := by
  by_cases hq : 0 ≤ q
  · obtain ⟨a,rfl⟩ := Int.eq_ofNat_of_zero_le hq
    rw [← Nat.cast_add,integerMixedTorBettiNumber_nat]
    simp only [integerColoredSupportBettiCoefficient_nat]
    exact mixed_positive_binomial_formula hE m hm hM a p
  · have hneg := lt_of_not_ge hq
    rw [integerMixedTorBettiNumber_zero_below o hE m p _ (by omega)]
    simp only [integerColoredSupportBettiCoefficient_negative q hneg p,
      zero_mul,Finset.sum_const_zero]

/-- The empty list of colors gives the constant polynomial for the empty
mixed product. Every nonempty color list uses the stated positive-binomial
basis, with natural-number coefficients. -/
def integerMixedBettiPolynomial (q : ℤ) (p : ℕ) : MvPolynomial (ULift.{u} (Fin r)) ℚ :=
  if r = 0 then
    MvPolynomial.C (integerOrdinaryQuotientBettiNumber (K := k)
      (∅ : Family (FiniteVariable.{u} n)) q p : ℚ)
  else
    MultivariatePositiveBinomial.polynomial
      (integerColoredSupportBettiCoefficient (k := k) (E := E) q p)
      coloredStrictSupportBinomialDegree

/-- The polynomial statement after (5.2), with every integer internal
degree and every positive exponent vector, including the empty color set. -/
theorem mixed_integer_positive_polynomial (hE : ColoredLatticeClosed n E)
    (m : ULift.{u} (Fin r) →₀ ℕ) (hm : ∀ c, 0 < m c) (p : ℕ) (q : ℤ) :
    MvPolynomial.eval (fun c => (m c : ℚ))
      (integerMixedBettiPolynomial (k := k) (E := E) q p) =
        (integerMixedTorBettiNumber (k := k) (E := E) o m p
          ((m.degree*d : ℕ)+q) : ℚ) := by
  by_cases hr : r = 0
  · subst r
    have hm0 : m = 0 := by
      ext c
      exact Fin.elim0 c.down
    simp only [integerMixedBettiPolynomial,ite_true,MvPolynomial.eval_C,hm0,
      map_zero,zero_mul,Nat.cast_zero,zero_add,
      integerMixedTorBettiNumber_zero o hE]
  · have hm0 : m ≠ 0 := by
      intro h
      have hc := hm (ULift.up (⟨0,Nat.pos_of_ne_zero hr⟩ : Fin r))
      simp only [h,Finsupp.zero_apply,lt_self_iff_false] at hc
    have hM : 0 < m.degree := Nat.pos_of_ne_zero
      (fun h => hm0 ((Finsupp.degree_eq_zero_iff _).mp h))
    rw [integerMixedBettiPolynomial,if_neg hr,
      MultivariatePositiveBinomial.polynomial_eval _ _ m hm,
      mixed_integer_positive_binomial_formula o hE m hm hM]

end FourPapers.Sublattice

#print axioms FourPapers.Sublattice.mixed_integer_ordinary_chain_formula
#print axioms FourPapers.Sublattice.mixed_integer_positive_polynomial

end
end
end

end
