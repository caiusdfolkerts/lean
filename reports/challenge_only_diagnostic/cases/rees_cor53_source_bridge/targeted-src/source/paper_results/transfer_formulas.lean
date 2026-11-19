module
public import shared_results.part012
public import shared_results.part023
public import shared_results.part021
public import paper_results.part001

set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

@[expose] public section

/- BEGIN EXACT BODY: FourPapers.Sublattice.Theorem43 -/
section

/-! # Theorem 4.3: the full first-power criterion

This is the paper-facing conjunction of the unconditional symbolic-power
and initial-ideal identities with the conditional homological assertions.
The first Betti comparison and every resulting comparison use the original
homogeneous ideal and actual derived Tor. The companion theorem
`theorem43_finer_betti`, re-exported here, treats every finer additive
grading respected by the ideal and refining ordinary degree.

The equality of the literal symbolic and ordinary ideals identifies their
graded Tor modules as well; no alternate definition of symbolic power is
used in any assertion.
-/

section
set_option autoImplicit false
noncomputable section

namespace FourPapers.Sublattice

attribute [local instance] MvPolynomial.weightedGradedAlgebra

open MvPolynomial
open FourPapers.IntegerFiltered.MultiplicativeFiltration

universe u
variable {K : Type u} [Field K] {d : ℕ} (n : Fin d → ℕ)
  (m : MonomialOrder (FiniteVariable.{u} n))
  (J : Ideal (MvPolynomial (FiniteVariable.{u} n) K))
  (E : Finset (FiniteTuple n)) (hE : finiteLatticeClosed n E)
  (hinit : FourPapers.initialIdeal m J = finiteSublatticeIdeal n E)
  (hJ : J.IsHomogeneous (weightedHomogeneousSubmodule K
    (fun _ : FiniteVariable.{u} n => (1 : ℕ))))

/-- All assertions of Theorem 4.3 in the ordinary grading. The ideal
identities require no first-power Betti hypothesis. Algebra generation and
all-power Betti equality require exactly the paper's first-power equality.
The universal finer-grading conclusion is `theorem43_finer_betti`. -/
theorem theorem43 :
    (∀ s : ℕ,
      symbolicPower J s = J ^ s ∧
      radicalSymbolicPower J s = J ^ s ∧
      FourPapers.initialIdeal m (symbolicPower J s) =
        (finiteSublatticeIdeal n E) ^ s ∧
      FourPapers.initialIdeal m (J ^ s) = (finiteSublatticeIdeal n E) ^ s) ∧
    ((∀ p q, sublatticePowerBettiNumber n m J E hE hinit hJ 1 p q =
        sublatticeMonomialPowerBettiNumber (K := K) n E 1 p q) →
      (∀ s p q, sublatticePowerBettiNumber n m J E hE hinit hJ s p q =
        sublatticeMonomialPowerBettiNumber (K := K) n E s p q) ∧
      Algebra.adjoin K (selectedHomologyClasses (idealReesKoszulDGA J)
        (WeightedRees.auxiliaryPiece m J (canonicalPowerGenerators n J)
          (canonicalPowerGroebner n m J) (canonicalPowerUnitLeading n m J) 1)) = ⊤) := by
  refine ⟨fun s => finite_theorem43_ideal_identities n m J E hE hinit s, ?_⟩
  intro hβ
  exact ⟨theorem43_ordinary_betti n m J E hE hinit hJ hβ,
    theorem43_rees_homology_generation n m J E hE hinit hJ hβ⟩

end FourPapers.Sublattice

end
end
end


/- BEGIN EXACT BODY: FourPapers.Sublattice.BettiPolynomialTransfer -/
section

/-! # The formulas for every Betti-preserving initial-ideal deformation

The first-power premise is exactly the premise of Theorem 4.3. The entries
on the deformation side are the actual ordinary submodules of derived Tor.
The all-power equality is invoked as a proved theorem, not assumed anew.
-/

section
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 600000
noncomputable section
namespace FourPapers.Sublattice
open Classical CommAlg CommAlg.Polymatroid MvPolynomial
open FourPapers.MultichainCounting
attribute [local instance] MvPolynomial.weightedGradedAlgebra
universe u
variable {K : Type u} [Field K] {d : ℕ} (n : Fin d → ℕ)
  (o : MonomialOrder (FiniteVariable.{u} n))
  (J : Ideal (MvPolynomial (FiniteVariable.{u} n) K))
  (E : Finset (FiniteTuple n)) (hE : finiteLatticeClosed n E)
  (hinit : FourPapers.initialIdeal o J = finiteSublatticeIdeal n E)
  (hJ : J.IsHomogeneous (weightedHomogeneousSubmodule K
    (fun _ : FiniteVariable.{u} n => (1 : ℕ))))
  (hβ : ∀ p q, sublatticePowerBettiNumber n o J E hE hinit hJ 1 p q =
    sublatticeMonomialPowerBettiNumber (K := K) n E 1 p q)

include hβ

/-- Corollary 5.1 for the literal powers of J under the exact first-power criterion. -/
theorem corollary51_transfer (m : ℕ) (hm : 0 < m) (q p : ℕ) :
    sublatticePowerBettiNumber n o J E hE hinit hJ m p (m*d+q) =
      ∑ s : StrictSupport E, (m-1).choose (s.val.card-1) *
        ordinaryQuotientBettiNumber (k := K) (strictSupportCoefficientFamily s) q p := by
  rw [theorem43_ordinary_betti n o J E hE hinit hJ hβ m p (m*d+q)]
  exact corollary51 hE m hm q p

/-- The same explicit rational polynomial gives every normalized entry for J. -/
theorem corollary52_polynomial_transfer (m : ℕ) (hm : 0 < m) (q p : ℕ) :
    (normalizedBettiPolynomial (k := K) (E := E) q p).eval (m : ℚ) =
      (sublatticePowerBettiNumber n o J E hE hinit hJ m p (m*d+q) : ℚ) := by
  rw [theorem43_ordinary_betti n o J E hE hinit hJ hβ m p (m*d+q)]
  exact corollary52_polynomial hE q p m hm

/-- Every order of ordinary integer forward difference is nonnegative for J. -/
theorem corollary52_forward_differences_transfer (q p j t : ℕ) :
    0 ≤ ((fwdDiff (1 : ℕ))^[j]
      (fun a => (sublatticePowerBettiNumber n o J E hE hinit hJ
        (a+1) p ((a+1)*d+q) : ℤ))) t := by
  have he : (fun a => (sublatticePowerBettiNumber n o J E hE hinit hJ
      (a+1) p ((a+1)*d+q) : ℤ)) =
      (fun a => (normalizedBettiSequence (k := K) (E := E) q p a : ℤ)) := by
    funext a
    exact congrArg (fun z : ℕ => (z : ℤ))
      (theorem43_ordinary_betti n o J E hE hinit hJ hβ (a+1) p ((a+1)*d+q))
  rw [he]
  exact corollary52_forward_differences hE q p j t

end FourPapers.Sublattice

#print axioms FourPapers.Sublattice.corollary51_transfer
#print axioms FourPapers.Sublattice.corollary52_forward_differences_transfer

end
end
end


/- BEGIN EXACT BODY: FourPapers.Sublattice.IntegerFirstPowerCriterion -/
section

/-! # The first-power criterion in all integer ordinary degrees

The first-power premise over all integers is equivalent to its natural
version. The resulting equality compares actual derived-Tor components
for every power, every homological degree, and every integer degree.
-/

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
noncomputable section
namespace FourPapers.Sublattice
open Classical CommAlg CommAlg.Polymatroid MvPolynomial
attribute [local instance] MvPolynomial.weightedGradedAlgebra

universe u
variable {K : Type u} [Field K] {d : ℕ} (n : Fin d → ℕ)
  (o : MonomialOrder (FiniteVariable.{u} n))
  (J : Ideal (MvPolynomial (FiniteVariable.{u} n) K))
  (E : Finset (FiniteTuple n)) (hE : finiteLatticeClosed n E)
  (hinit : FourPapers.initialIdeal o J = finiteSublatticeIdeal n E)
  (hJ : J.IsHomogeneous (weightedHomogeneousSubmodule K
    (fun _ : FiniteVariable.{u} n => (1 : ℕ))))

/-- Integer degree Betti numbers of the actual powers of the deformation. -/
def sublatticeIntegerPowerBettiNumber (m p : ℕ) (q : ℤ) : ℕ :=
  ordinaryIntegerIdealBettiNumber
    (sublatticePowerQuotientData n o J E hE hinit m)
    (homogeneousIdealPower n J hJ m) p q

@[simp] theorem sublatticeIntegerPowerBettiNumber_nat (m p q : ℕ) :
    sublatticeIntegerPowerBettiNumber n o J E hE hinit hJ m p (q : ℤ) =
      sublatticePowerBettiNumber n o J E hE hinit hJ m p q :=
  ordinaryIntegerIdealBettiNumber_nat _ _ p q

theorem sublatticeIntegerPowerBettiNumber_negative (m p : ℕ) (q : ℤ) (hq : q < 0) :
    sublatticeIntegerPowerBettiNumber n o J E hE hinit hJ m p q = 0 :=
  ordinaryIntegerIdealBettiNumber_negative _ _ p q hq

/-- No degree is lost when the first-power criterion is expressed over `ℕ`. -/
theorem sublattice_first_power_integer_iff :
    (∀ p q, sublatticeIntegerPowerBettiNumber n o J E hE hinit hJ 1 p q =
      integerMonomialTorBettiNumber (K := K) o
        (exponentPowerFamily (finiteRowFamily n E) 1) p q) ↔
    (∀ p q, sublatticePowerBettiNumber n o J E hE hinit hJ 1 p q =
      sublatticeMonomialPowerBettiNumber (K := K) n E 1 p q) := by
  constructor
  · intro h p q
    simpa only [sublatticeIntegerPowerBettiNumber_nat,
      integerMonomialTorBettiNumber_nat, sublatticeMonomialPowerBettiNumber]
      using h p (q : ℤ)
  · intro h p q
    by_cases hq : 0 ≤ q
    · obtain ⟨a, rfl⟩ := Int.eq_ofNat_of_zero_le hq
      simpa only [sublatticeIntegerPowerBettiNumber_nat,
        integerMonomialTorBettiNumber_nat, sublatticeMonomialPowerBettiNumber]
        using h p a
    · have hneg : q < 0 := lt_of_not_ge hq
      rw [sublatticeIntegerPowerBettiNumber_negative n o J E hE hinit hJ 1 p q hneg,
        integerMonomialTorBettiNumber_negative o _ p q hneg]

variable (hβ : ∀ p q, sublatticePowerBettiNumber n o J E hE hinit hJ 1 p q =
  sublatticeMonomialPowerBettiNumber (K := K) n E 1 p q)

include hβ in
/-- Theorem 4.3 in every integer ordinary degree. -/
theorem theorem43_integer_betti (m p : ℕ) (q : ℤ) :
    sublatticeIntegerPowerBettiNumber n o J E hE hinit hJ m p q =
      integerMonomialTorBettiNumber (K := K) o
        (exponentPowerFamily (finiteRowFamily n E) m) p q := by
  by_cases hq : 0 ≤ q
  · obtain ⟨a, rfl⟩ := Int.eq_ofNat_of_zero_le hq
    simpa only [sublatticeIntegerPowerBettiNumber_nat,
      integerMonomialTorBettiNumber_nat, sublatticeMonomialPowerBettiNumber]
      using theorem43_ordinary_betti n o J E hE hinit hJ hβ m p a
  · have hneg : q < 0 := lt_of_not_ge hq
    rw [sublatticeIntegerPowerBettiNumber_negative n o J E hE hinit hJ m p q hneg,
      integerMonomialTorBettiNumber_negative o _ p q hneg]

end FourPapers.Sublattice

end
end
end


/- BEGIN EXACT BODY: FourPapers.Sublattice.IntegerBettiPolynomialTransfer -/
section

/-! # Integer graded Betti formulas for the original homogeneous ideal

The degree parameter in Corollaries 5.1 and 5.2 ranges over all integers.
These statements use the homogeneous submodules of actual derived Tor for
the literal powers of `J`. The natural degree first-power premise is proved
equivalent to the premise in all integer degrees.
-/

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
noncomputable section

namespace FourPapers.Sublattice

open Classical CommAlg CommAlg.Polymatroid MvPolynomial
open FourPapers.MultichainCounting
attribute [local instance] MvPolynomial.weightedGradedAlgebra

universe u
variable {K : Type u} [Field K] {d : ℕ} (n : Fin d → ℕ)
  (o : MonomialOrder (FiniteVariable.{u} n))
  (J : Ideal (MvPolynomial (FiniteVariable.{u} n) K))
  (E : Finset (FiniteTuple n)) (hE : finiteLatticeClosed n E)
  (hinit : FourPapers.initialIdeal o J = finiteSublatticeIdeal n E)
  (hJ : J.IsHomogeneous (weightedHomogeneousSubmodule K
    (fun _ : FiniteVariable.{u} n => (1 : ℕ))))

variable (hβ : ∀ p q, sublatticePowerBettiNumber n o J E hE hinit hJ 1 p q =
  sublatticeMonomialPowerBettiNumber (K := K) n E 1 p q)

include hβ

/-- Corollary 5.1 for every power and every integer normalized degree of `J`. -/
theorem corollary51_integer_transfer (m : ℕ) (hm : 0 < m) (p : ℕ) (q : ℤ) :
    sublatticeIntegerPowerBettiNumber n o J E hE hinit hJ m p ((m*d : ℕ)+q) =
      ∑ s : StrictSupport E, (m-1).choose (s.val.card-1) *
        integerOrdinaryQuotientBettiNumber (K := K) (strictSupportCoefficientFamily s) q p := by
  rw [theorem43_integer_betti n o J E hE hinit hJ hβ]
  exact corollary51_integer o hE m hm p q

/-- Corollary 5.2 is valid from the first power, in all integer degrees. -/
theorem corollary52_integer_polynomial_transfer (q : ℤ) (p m : ℕ) (hm : 0 < m) :
    (integerNormalizedBettiPolynomial (K := K) (E := E) q p).eval (m : ℚ) =
      (sublatticeIntegerPowerBettiNumber n o J E hE hinit hJ m p
        ((m*d : ℕ)+q) : ℚ) := by
  rw [theorem43_integer_betti n o J E hE hinit hJ hβ]
  exact corollary52_integer_polynomial o hE q p m hm

/-- Every integer forward difference of every normalized entry is nonnegative. -/
theorem corollary52_integer_forward_differences_transfer (q : ℤ) (p j t : ℕ) :
    0 ≤ ((fwdDiff (1 : ℕ))^[j]
      (fun a => (sublatticeIntegerPowerBettiNumber n o J E hE hinit hJ
        (a+1) p (((a+1)*d : ℕ)+q) : ℤ))) t := by
  have he : (fun a => (sublatticeIntegerPowerBettiNumber n o J E hE hinit hJ
      (a+1) p (((a+1)*d : ℕ)+q) : ℤ)) =
      (fun a => (integerNormalizedBettiSequence (K := K) o (E := E) q p a : ℤ)) := by
    funext a
    exact congrArg (fun z : ℕ => (z : ℤ))
      (theorem43_integer_betti n o J E hE hinit hJ hβ (a+1) p (((a+1)*d : ℕ)+q))
  rw [he]
  exact corollary52_integer_forward_differences o hE q p j t

end FourPapers.Sublattice

#print axioms FourPapers.Sublattice.theorem43_integer_betti
#print axioms FourPapers.Sublattice.corollary51_integer_transfer
#print axioms FourPapers.Sublattice.corollary52_integer_forward_differences_transfer

end
end
end


/- BEGIN EXACT BODY: FourPapers.Sublattice.IntegerBettiGroupedCoefficients -/
section

/-!
# The printed coefficients in Corollary 5.2

The coefficient c_{p,q,r} is literally the sum of the quotient Betti
numbers over strict supports of cardinality r. The regrouping below
identifies that expression with the previously checked support formula,
including every integer normalized degree and every positive power.
-/

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 300000
noncomputable section
namespace FourPapers.Sublattice

open Classical CommAlg CommAlg.Polymatroid MvPolynomial FourPapers.MultichainCounting
attribute [local instance] MvPolynomial.weightedGradedAlgebra
universe u
variable {K : Type u} [Field K] {d : ℕ} {n : Fin d → ℕ} {E : Finset (FiniteTuple n)}

private theorem strictSupport_card_bounds_for_betti (s : StrictSupport E) :
    1 ≤ s.val.card ∧ s.val.card ≤ E.card := by
  refine ⟨Finset.card_pos.mpr s.property.1, ?_⟩
  simpa only [Fintype.card_coe] using Finset.card_le_univ s.val

/-- The paper's c_{p,q,r}, with the coefficient order q,p matching the
integer homogeneous quotient Betti function. -/
def integerBettiBinomialCoefficient (q : ℤ) (p r : ℕ) : ℕ :=
  ∑ s ∈ Finset.univ.filter (fun s : StrictSupport E => s.val.card = r),
    integerStrictSupportBettiCoefficient (K := K) q p s

/-- These are nonnegative integers because each summand is an actual
homogeneous homology dimension. -/
theorem integerBettiBinomialCoefficient_nonnegative (q : ℤ) (p r : ℕ) :
    0 ≤ (integerBettiBinomialCoefficient (K := K) (E := E) q p r : ℤ) :=
  Int.natCast_nonneg _

/-- The coefficient is zero outside the stated finite range, so the
finite displayed sum represents the paper's sum over all positive r. -/
theorem integerBettiBinomialCoefficient_eq_zero_of_not_mem
    (q : ℤ) (p r : ℕ) (hr : r ∉ Finset.Icc 1 E.card) :
    integerBettiBinomialCoefficient (K := K) (E := E) q p r = 0 := by
  unfold integerBettiBinomialCoefficient
  apply Finset.sum_eq_zero
  intro s hs
  have he : s.val.card = r := (Finset.mem_filter.mp hs).2
  exact (hr (he ▸ Finset.mem_Icc.mpr (strictSupport_card_bounds_for_betti s))).elim

/-- Regrouping the normalized entry by the length of the strict support. -/
theorem integerNormalizedBettiSequence_grouped
    (o : MonomialOrder (FiniteVariable.{u} n)) (hE : finiteLatticeClosed n E)
    (q : ℤ) (p t : ℕ) :
    integerNormalizedBettiSequence (K := K) o (E := E) q p t =
      ∑ r ∈ Finset.Icc 1 E.card,
        integerBettiBinomialCoefficient (K := K) (E := E) q p r * t.choose (r-1) := by
  rw [integerNormalizedBettiSequence_eq o hE]
  exact FinitePositiveGrouping.sum_grouped_by_positive_label
    (integerStrictSupportBettiCoefficient (K := K) (E := E) q p)
    (fun s => s.val.card) E.card strictSupport_card_bounds_for_betti
    (fun r => t.choose (r-1))

/-- The actual rational polynomial is the printed grouped binomial
polynomial, not only a function with the same sampled values. -/
theorem integerNormalizedBettiPolynomial_grouped (q : ℤ) (p : ℕ) :
    integerNormalizedBettiPolynomial (K := K) (E := E) q p =
      (∑ r ∈ Finset.Icc 1 E.card,
        Polynomial.C (integerBettiBinomialCoefficient (K := K) (E := E) q p r : ℚ) *
          PositiveBinomialPolynomial.binomialPolynomial (r-1)).comp
            (Polynomial.X - Polynomial.C 1) := by
  unfold integerNormalizedBettiPolynomial
  apply congrArg (fun f : Polynomial ℚ => f.comp (Polynomial.X - Polynomial.C 1))
  have h := FinitePositiveGrouping.sum_grouped_by_positive_label
    (fun s : StrictSupport E =>
      Polynomial.C (integerStrictSupportBettiCoefficient (K := K) q p s : ℚ))
    (fun s => s.val.card) E.card strictSupport_card_bounds_for_betti
    (fun r => PositiveBinomialPolynomial.binomialPolynomial (r-1))
  simpa only [PositiveBinomialPolynomial.polynomial, integerBettiBinomialCoefficient,
    Nat.cast_sum, map_sum] using h

/-- **Corollary 5.2 in its printed coefficient grouping.** All powers and
all integer normalized degrees refer to actual derived Tor components. -/
theorem corollary52_integer_grouped_expansion
    (o : MonomialOrder (FiniteVariable.{u} n)) (hE : finiteLatticeClosed n E)
    (q : ℤ) (p m : ℕ) (hm : 0 < m) :
    integerMonomialTorBettiNumber (K := K) o
      (exponentPowerFamily (finiteRowFamily n E) m) p ((m*d : ℕ)+q) =
      ∑ r ∈ Finset.Icc 1 E.card,
        integerBettiBinomialCoefficient (K := K) (E := E) q p r * (m-1).choose (r-1) := by
  have h := integerNormalizedBettiSequence_grouped (K := K) o hE q p (m-1)
  simpa only [integerNormalizedBettiSequence, Nat.sub_add_cancel (by omega : 1 ≤ m)] using h

/-- The same literal coefficients compute the actual original ideal J
under exactly the first-power Betti equality of Theorem 4.3. -/
theorem corollary52_integer_grouped_expansion_transfer
    (o : MonomialOrder (FiniteVariable.{u} n))
    (J : Ideal (MvPolynomial (FiniteVariable.{u} n) K))
    (hE : finiteLatticeClosed n E)
    (hinit : FourPapers.initialIdeal o J = finiteSublatticeIdeal n E)
    (hJ : J.IsHomogeneous (weightedHomogeneousSubmodule K
      (fun _ : FiniteVariable.{u} n => (1 : ℕ))))
    (hβ : ∀ a b, sublatticePowerBettiNumber n o J E hE hinit hJ 1 a b =
      sublatticeMonomialPowerBettiNumber (K := K) n E 1 a b)
    (q : ℤ) (p m : ℕ) (hm : 0 < m) :
    sublatticeIntegerPowerBettiNumber n o J E hE hinit hJ m p ((m*d : ℕ)+q) =
      ∑ r ∈ Finset.Icc 1 E.card,
        integerBettiBinomialCoefficient (K := K) (E := E) q p r * (m-1).choose (r-1) := by
  rw [theorem43_integer_betti n o J E hE hinit hJ hβ]
  exact corollary52_integer_grouped_expansion o hE q p m hm

end FourPapers.Sublattice

end
end
end


/- BEGIN EXACT BODY: FourPapers.Sublattice.BettiGeneratingSeries -/
section

/-! # The rational series following Corollary 5.1

The three formal variables are represented by nested power series:
the outer variable is the power parameter `z`, then the homological
variable `s`, then the internal-degree variable `v`. The coefficients
are the actual ordinary Betti numbers. Normalizing the internal degree
means taking degree `m*d+q`; the proved vanishing below `m*d` justifies
the factor `v^(-m*d)` used in the paper.
-/

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 400000
noncomputable section
namespace FourPapers.Sublattice
open Classical CommAlg.Polymatroid FourPapers.MultichainCounting
universe u
variable {d : ℕ} {n : Fin d → ℕ} {E : Finset (FiniteTuple n)}
  {k : Type u} [Field k]

/-- The ordinary Betti series, with homological degree outside internal degree. -/
def bigradedBettiSeries (b : ℕ → ℕ → ℕ) : PowerSeries (PowerSeries ℤ) :=
  PowerSeries.mk fun p => PowerSeries.mk fun q => (b p q : ℤ)

@[simp] theorem bigradedBettiSeries_coefficient (b : ℕ → ℕ → ℕ) (p q : ℕ) :
    PowerSeries.coeff q (PowerSeries.coeff p (bigradedBettiSeries b)) = (b p q : ℤ) := by
  simp only [bigradedBettiSeries, PowerSeries.coeff_mk]

/-- Passing to a series preserves every Betti number. Thus the series
formulation is an injective encoding of the entire bigraded table. -/
theorem bigradedBettiSeries_injective : Function.Injective bigradedBettiSeries := by
  intro b c h
  funext p q
  have hcoeff := congrArg (fun f : PowerSeries (PowerSeries ℤ) =>
    PowerSeries.coeff q (PowerSeries.coeff p f)) h
  simp only [bigradedBettiSeries_coefficient] at hcoeff
  exact_mod_cast hcoeff

/-- The normalization is multiplication by the original internal-degree
shift whenever all the preceding actual coefficients vanish. -/
theorem bigradedBettiSeries_shift (b : ℕ → ℕ → ℕ) (D : ℕ)
    (hzero : ∀ p q, q < D → b p q = 0) :
    bigradedBettiSeries b =
      PowerSeries.C (PowerSeries.X^D) * bigradedBettiSeries (fun p q => b p (D+q)) := by
  apply PowerSeries.ext
  intro p
  apply PowerSeries.ext
  intro q
  simp only [bigradedBettiSeries_coefficient, PowerSeries.coeff_C_mul,
    bigradedBettiSeries, PowerSeries.coeff_mk, PowerSeries.coeff_X_pow_mul']
  by_cases h : D ≤ q
  · rw [if_pos h, Nat.add_sub_of_le h]
  · rw [if_neg h, hzero p q (lt_of_not_ge h), Nat.cast_zero]

def coefficientBettiSeries (s : StrictSupport E) : PowerSeries (PowerSeries ℤ) :=
  bigradedBettiSeries fun p q =>
    ordinaryQuotientBettiNumber (k := k) (strictSupportCoefficientFamily s) q p

def normalizedPowerBettiSeries (m : ℕ) : PowerSeries (PowerSeries ℤ) :=
  bigradedBettiSeries fun p q =>
    ordinaryMonomialBettiNumber (k := k)
      (exponentPowerFamily (finiteRowFamily n E) m) (m*d+q) p

/-- Equality of the full series in `s` and `v`, rather than a selected set of entries. -/
theorem corollary51_series (hE : finiteLatticeClosed n E) (m : ℕ) (hm : 0 < m) :
    normalizedPowerBettiSeries (k := k) (E := E) m =
      ∑ s : StrictSupport E, ((m-1).choose (s.val.card-1) : PowerSeries (PowerSeries ℤ)) *
        coefficientBettiSeries (k := k) s := by
  apply PowerSeries.ext
  intro p
  apply PowerSeries.ext
  intro q
  simp only [normalizedPowerBettiSeries, coefficientBettiSeries,
    bigradedBettiSeries_coefficient, map_sum, PowerSeries.coeff_natCast_mul]
  rw [corollary51 hE m hm q p]
  simp only [Nat.cast_sum, Nat.cast_mul]

/-- Formula (5.1), including its literal factor `v^(d*m)`. -/
theorem corollary51_unshifted_series (hE : finiteLatticeClosed n E)
    (m : ℕ) (hm : 0 < m) :
    bigradedBettiSeries (fun p q => ordinaryMonomialBettiNumber (k := k)
      (exponentPowerFamily (finiteRowFamily n E) m) q p) =
      PowerSeries.C (PowerSeries.X^(m*d)) *
        ∑ s : StrictSupport E,
          ((m-1).choose (s.val.card-1) : PowerSeries (PowerSeries ℤ)) *
            coefficientBettiSeries (k := k) s := by
  rw [bigradedBettiSeries_shift _ (m*d)
    (fun p q hq => ordinaryPowerBetti_eq_zero_below hE m hm q p hq)]
  change PowerSeries.C (PowerSeries.X^(m*d)) * normalizedPowerBettiSeries m = _
  rw [corollary51_series hE m hm]

/-- The complete rational generating series displayed after (5.1).
Each rational factor is the actual series `z^|s|/(1-z)^|s|`, with its
denominator identity verified in `PositiveMultiplicitySeries`. -/
theorem corollary51_generating_series (hE : finiteLatticeClosed n E) :
    PowerSeries.mk (fun m => if m = 0 then 0 else
      normalizedPowerBettiSeries (k := k) (E := E) m) =
      ∑ s : StrictSupport E,
        PositiveMultiplicitySeries.series (PowerSeries (PowerSeries ℤ)) s.val.card *
          PowerSeries.C (coefficientBettiSeries (k := k) s) := by
  rw [← PositiveMultiplicitySeries.finite_sum
    (fun s : StrictSupport E => coefficientBettiSeries (k := k) s)
    (fun s => s.val.card) (fun s => Finset.card_pos.mpr s.property.1)]
  apply PowerSeries.ext
  intro m
  simp only [PowerSeries.coeff_mk]
  by_cases hm : m = 0
  · simp only [hm, if_pos]
  · simp only [if_neg hm]
    exact corollary51_series hE m (Nat.pos_of_ne_zero hm)

end FourPapers.Sublattice

#print axioms FourPapers.Sublattice.corollary51_generating_series

end
end
end


/- BEGIN EXACT BODY: FourPapers.Sublattice.BettiGeneratingSeriesTransfer -/
section

/-! # The generating-series formula for the original deformation

Every coefficient on the left is a Betti number of a literal power of `J`.
The first-power criterion supplies the comparison in all powers.
-/

section
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace FourPapers.Sublattice
open Classical CommAlg CommAlg.Polymatroid MvPolynomial
open FourPapers.MultichainCounting
attribute [local instance] MvPolynomial.weightedGradedAlgebra
universe u
variable {K : Type u} [Field K] {d : ℕ} (n : Fin d → ℕ)
  (o : MonomialOrder (FiniteVariable.{u} n))
  (J : Ideal (MvPolynomial (FiniteVariable.{u} n) K))
  (E : Finset (FiniteTuple n)) (hE : finiteLatticeClosed n E)
  (hinit : FourPapers.initialIdeal o J = finiteSublatticeIdeal n E)
  (hJ : J.IsHomogeneous (weightedHomogeneousSubmodule K
    (fun _ : FiniteVariable.{u} n => (1 : ℕ))))
  (hβ : ∀ p q, sublatticePowerBettiNumber n o J E hE hinit hJ 1 p q =
    sublatticeMonomialPowerBettiNumber (K := K) n E 1 p q)

include hβ

theorem corollary51_unshifted_series_transfer (m : ℕ) (hm : 0 < m) :
    bigradedBettiSeries (fun p q => sublatticePowerBettiNumber n o J E hE hinit hJ m p q) =
      PowerSeries.C (PowerSeries.X^(m*d)) *
        ∑ s : StrictSupport E,
          ((m-1).choose (s.val.card-1) : PowerSeries (PowerSeries ℤ)) *
            coefficientBettiSeries (k := K) s := by
  have he : (fun p q => sublatticePowerBettiNumber n o J E hE hinit hJ m p q) =
      (fun p q => ordinaryMonomialBettiNumber (k := K)
        (exponentPowerFamily (finiteRowFamily n E) m) q p) := by
    funext p q
    exact theorem43_ordinary_betti n o J E hE hinit hJ hβ m p q
  rw [he]
  exact corollary51_unshifted_series hE m hm

theorem corollary51_generating_series_transfer :
    PowerSeries.mk (fun m => if m = 0 then 0 else
      bigradedBettiSeries (fun p q => sublatticePowerBettiNumber n o J E hE hinit hJ
        m p (m*d+q))) =
      ∑ s : StrictSupport E,
        PositiveMultiplicitySeries.series (PowerSeries (PowerSeries ℤ)) s.val.card *
          PowerSeries.C (coefficientBettiSeries (k := K) s) := by
  have he : (fun m => if m = 0 then 0 else
      bigradedBettiSeries (fun p q => sublatticePowerBettiNumber n o J E hE hinit hJ
        m p (m*d+q))) =
      (fun m => if m = 0 then 0 else normalizedPowerBettiSeries (k := K) (E := E) m) := by
    funext m
    by_cases hm : m = 0
    · simp only [hm, if_pos]
    · simp only [if_neg hm, normalizedPowerBettiSeries]
      congr 1
      funext p q
      exact theorem43_ordinary_betti n o J E hE hinit hJ hβ m p (m*d+q)
  rw [he]
  exact corollary51_generating_series hE

end FourPapers.Sublattice

#print axioms FourPapers.Sublattice.corollary51_generating_series_transfer

end
end
end


end
