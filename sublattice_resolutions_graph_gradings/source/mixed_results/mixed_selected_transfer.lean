module
public import shared_results.part024

set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

@[expose] public section

/- BEGIN EXACT BODY: FourPapers.Sublattice.MixedSelectedTransfer -/
section

/-!
# Remark 5.4 for any set of multi-Rees degrees

The generating degrees need not be coordinate units. This statement uses
the literal mixed ideals and their actual graded Tor dimensions. The
initial identities and the numerical equalities in the chosen degrees
produce cycle lifts; the multiplicative theorem then propagates those
lifts to every mixed degree and preserves algebra generation.
-/

section
set_option autoImplicit false
set_option maxHeartbeats 900000
noncomputable section

namespace FourPapers.Sublattice
open Classical CommAlg MvPolynomial
open FourPapers.IntegerFiltered.MultiplicativeFiltration
attribute [local instance] MvPolynomial.weightedGradedAlgebra

universe u
variable {K : Type u} [Field K] {d r : ℕ} (n : Fin d → ℕ)
  (E : Fin r → Finset (FiniteTuple n))
  (M : MonomialOrder (FiniteVariable.{u} n))
  (J : ULift.{u} (Fin r) → Ideal (MvPolynomial (FiniteVariable.{u} n) K))
  (hinit : ∀ a, FourPapers.initialIdeal M (powerProduct J a) =
    powerProduct (coloredIdeals (k := K) n E) a)
  (hJ : ∀ c, (J c).IsHomogeneous
    (weightedHomogeneousSubmodule K (fun _ : FiniteVariable.{u} n => (1 : ℕ))))
  (U : Set (ULift.{u} (Fin r) →₀ ℕ))

local notation "G" => canonicalMixedGenerators n J
local notation "hG" => canonicalMixedGroebner n M J
local notation "hu" => canonicalMixedUnitLeading n M J
local notation "I" => coloredIdeals (k := K) n E

theorem selectedMixed_ordered_lifts
    (hβ : ∀ a ∈ U, ∀ p q, mixedPowerBettiNumber n E M J hinit hJ a p q =
      mixedMonomialBettiNumber (K := K) n E a p q)
    (a : ULift.{u} (Fin r) →₀ ℕ) (ha : a ∈ U) (p : ℕ) :
    MixedTransfer.PowerOrderedCoordinateLifts M J G hG hu a p := by
  have hh := actualIdeal_ordered_lifts_of_betti_eq
    (mixedPowerQuotientData n E M J hinit a)
    (homogeneousMixedProduct n J hJ a) (hβ a ha) p
  apply (MixedTransfer.nativePowerOrderedLifts_iff M J G hG hu a p).mp
  simpa only [ActualIdealOrderedLifts, MixedTransfer.NativePowerOrderedLifts,
    MixedTransfer.nativePowerCoefficientBasis, actualIdealCoefficientBasis,
    actualIdealDegree, mixedPowerQuotientData] using hh

variable (hgen : Algebra.adjoin K
  (selectedHomologyClasses
    (MixedTransfer.idealReesKoszulDGA (coloredIdeals (k := K) n E))
    (MixedTransfer.Auxiliary.initialSelectedPiece M J
      (coloredIdeals (k := K) n E) hinit
      (canonicalMixedGenerators n J) (canonicalMixedGroebner n M J)
      (canonicalMixedUnitLeading n M J) U)) = ⊤)

include hgen in
theorem mixed_selected_all_ordered_lifts
    (hβ : ∀ a ∈ U, ∀ p q, mixedPowerBettiNumber n E M J hinit hJ a p q =
      mixedMonomialBettiNumber (K := K) n E a p q)
    (a : ULift.{u} (Fin r) →₀ ℕ) (p : ℕ) :
    ActualIdealOrderedLifts (mixedPowerQuotientData n E M J hinit a) p := by
  have hh := MixedTransfer.all_mixed_ordered_coordinate_lifts M J G hG hu I hinit U
    hgen (selectedMixed_ordered_lifts n E M J hinit hJ U hβ) a p
  have hn := (MixedTransfer.nativePowerOrderedLifts_iff M J G hG hu a p).mpr hh
  simpa only [ActualIdealOrderedLifts, MixedTransfer.NativePowerOrderedLifts,
    MixedTransfer.nativePowerCoefficientBasis, actualIdealCoefficientBasis,
    actualIdealDegree, mixedPowerQuotientData] using hn

include hgen in
/-- Equality in any generating set of auxiliary degrees gives equality
of actual mixed-ideal Betti numbers in every integer internal degree. -/
theorem mixed_selected_betti
    (hβ : ∀ a ∈ U, ∀ p q, mixedPowerBettiNumber n E M J hinit hJ a p q =
      mixedMonomialBettiNumber (K := K) n E a p q)
    (a : ULift.{u} (Fin r) →₀ ℕ) (p : ℕ) (q : ℤ) :
    mixedIntegerPowerBettiNumber n E M J hinit hJ a p q =
      mixedIntegerMonomialBettiNumber (K := K) n E M a p q := by
  by_cases hq : 0 ≤ q
  · have he : (q.toNat : ℤ) = q := Int.toNat_of_nonneg hq
    rw [← he, mixedIntegerPowerBettiNumber_nat, mixedIntegerMonomialBettiNumber_nat]
    exact ordinaryIdealBettiNumber_eq_monomial_of_ordered_lifts
      (mixedPowerQuotientData n E M J hinit a) (homogeneousMixedProduct n J hJ a)
      (mixed_selected_all_ordered_lifts n E M J hinit hJ U hgen hβ a) p q.toNat
  · have hn : q < 0 := lt_of_not_ge hq
    unfold mixedIntegerPowerBettiNumber mixedIntegerMonomialBettiNumber
    rw [ordinaryIntegerIdealBettiNumber_negative _ _ p q hn,
      ordinaryIntegerIdealBettiNumber_negative _ _ p q hn]

include hgen in
/-- The same auxiliary degrees generate the original multi-Rees homology. -/
theorem mixed_selected_generation
    (hβ : ∀ a ∈ U, ∀ p q, mixedPowerBettiNumber n E M J hinit hJ a p q =
      mixedMonomialBettiNumber (K := K) n E a p q) :
    Algebra.adjoin K (selectedHomologyClasses (MixedTransfer.idealReesKoszulDGA J)
      (MixedTransfer.Auxiliary.selectedPiece M J G hG hu U)) = ⊤ :=
  MixedTransfer.mixed_homology_generated_of_selected_lifts M J G hG hu I hinit U hgen
    (selectedMixed_ordered_lifts n E M J hinit hJ U hβ)

end FourPapers.Sublattice

end
end
end


end
