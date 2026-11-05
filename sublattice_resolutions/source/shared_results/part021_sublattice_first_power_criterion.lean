module
public import graph_foundation.part014
public import shared_results.part021_ideal_order_betti_comparison

set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

@[expose] public section

/- BEGIN EXACT BODY: FourPapers.Sublattice.SublatticeFirstPowerCriterion -/
section

/-! # The all-power homological first-power criterion

The Gröbner data below are constructed canonically from the actual ideal;
no additional Gröbner-basis hypothesis is present in the theorem. The
all-power initial identities come from the checked sublattice theorem.
All Betti dimensions refer to ordinary homogeneous submodules of genuine
derived Tor objects, through the proved coordinate comparison.
-/

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace FourPapers.Sublattice

open Classical CommAlg CommAlg.Polymatroid MvPolynomial
open FourPapers.IntegerFiltered.MultiplicativeFiltration
attribute [local instance] MvPolynomial.weightedGradedAlgebra

universe u
variable {K : Type u} [Field K] {d : ℕ} (n : Fin d → ℕ)
  (m : MonomialOrder (FiniteVariable.{u} n))
  (J : Ideal (MvPolynomial (FiniteVariable.{u} n) K))
  (E : Finset (FiniteTuple n)) (hE : finiteLatticeClosed n E)
  (hinit : FourPapers.initialIdeal m J=finiteSublatticeIdeal n E)

def canonicalPowerGenerators (s : ℕ) : Set (MvPolynomial (FiniteVariable.{u} n) K) :=
  ((J ^ s : Ideal (MvPolynomial (FiniteVariable.{u} n) K)) :
    Set (MvPolynomial (FiniteVariable.{u} n) K))

theorem canonicalPowerGroebner (s : ℕ) : m.IsGroebnerBasis (canonicalPowerGenerators n J s) (J^s) :=
  m.isGroebnerBasis_self (J^s)

theorem canonicalPowerUnitLeading (s : ℕ) :
    ∀ g,g∈canonicalPowerGenerators n J s → g≠0 → IsUnit (m.leadingCoeff g) :=
  fun g _ hg => m.isUnit_leadingCoeff.mpr hg

def sublatticePowerInitial (s : ℕ) : initialIdealForBasis m (J^s)=(finiteSublatticeIdeal n E)^s :=
  finite_initialIdeal_power_eq n m J E hE hinit s

def sublatticePowerQuotientData (s : ℕ) : QuotientGroebnerData (FiniteVariable.{u} n) K where
  order := m
  ideal := J^s
  generators := canonicalPowerGenerators n J s
  groebner := canonicalPowerGroebner n m J s
  unitLeading := canonicalPowerUnitLeading n m J s
  family := exponentPowerFamily (finiteRowFamily n E) s
  standard a := by
    have h := monomial_mem_initial_iff_not_standard m (J^s)
      (canonicalPowerGenerators n J s) (canonicalPowerGroebner n m J s)
      (canonicalPowerUnitLeading n m J s) a
    change ((monomial a (1 : K)) ∈ initialIdealForBasis m (J^s) ↔
      a ∉ m.standardMonomials (J^s)) at h
    rw [sublatticePowerInitial n m J E hE hinit s,← finitePowerFamily_ideal (n := n),
      monomial_mem_iff] at h
    simpa only [QuotientAllowed, not_not] using (not_congr h).symm

theorem homogeneousIdealPower
    (hJ : J.IsHomogeneous (weightedHomogeneousSubmodule K
      (fun _ : FiniteVariable.{u} n => (1 : ℕ)))) (s : ℕ) :
    (J^s).IsHomogeneous (weightedHomogeneousSubmodule K
      (fun _ : FiniteVariable.{u} n => (1 : ℕ))) := by
  induction s with
  | zero => simpa only [pow_zero,Ideal.one_eq_top] using
      (Ideal.IsHomogeneous.top (weightedHomogeneousSubmodule K
        (fun _ : FiniteVariable.{u} n => (1 : ℕ))))
  | succ s ih => rw [pow_succ]; exact ih.mul hJ

variable (hJ : J.IsHomogeneous (weightedHomogeneousSubmodule K
  (fun _ : FiniteVariable.{u} n => (1 : ℕ))))

def sublatticePowerBettiNumber (s p q : ℕ) : ℕ :=
  ordinaryIdealBettiNumber (sublatticePowerQuotientData n m J E hE hinit s)
    (homogeneousIdealPower n J hJ s) p q

def sublatticeMonomialPowerBettiNumber (s p q : ℕ) : ℕ :=
  ordinaryMonomialBettiNumber (k:=K) (exponentPowerFamily (finiteRowFamily n E) s) q p

local notation "G" => canonicalPowerGenerators n J
local notation "hG" => canonicalPowerGroebner n m J
local notation "hu" => canonicalPowerUnitLeading n m J
local notation "I" => finiteSublatticeIdeal n (k:=K) E
local notation "hi" => sublatticePowerInitial n m J E hE hinit

theorem sublattice_initial_homology_generated :
    Algebra.adjoin K (selectedHomologyClasses (idealReesKoszulDGA I)
      (WeightedRees.initialAuxiliaryPiece m J I hi G hG hu 1))=⊤ := by
  exact initialReesKoszulHomology_generated_of_finite_generation E m J hi G hG hu hE
    (reesKoszulHomology_generated_in_degree_one (k:=K) hE)

theorem sublattice_first_ordered_lifts
    (hβ : ∀ p q,sublatticePowerBettiNumber n m J E hE hinit hJ 1 p q=
      sublatticeMonomialPowerBettiNumber (K:=K) n E 1 p q) :
    ∀ p,PowerOrderedCoordinateLifts m J G hG hu 1 p := by
  intro p
  have hh := actualIdeal_ordered_lifts_of_betti_eq
    (sublatticePowerQuotientData n m J E hE hinit 1) (homogeneousIdealPower n J hJ 1) hβ p
  apply (nativePowerOrderedLifts_iff m J G hG hu 1 p).mp
  simpa only [ActualIdealOrderedLifts, NativePowerOrderedLifts,
    nativePowerCoefficientBasis, actualIdealCoefficientBasis, actualIdealDegree,
    sublatticePowerQuotientData] using hh

theorem sublattice_all_power_ordered_lifts
    (hβ : ∀ p q,sublatticePowerBettiNumber n m J E hE hinit hJ 1 p q=
      sublatticeMonomialPowerBettiNumber (K:=K) n E 1 p q) (s p : ℕ) :
    ActualIdealOrderedLifts (sublatticePowerQuotientData n m J E hE hinit s) p := by
  have hh := all_power_ordered_coordinate_lifts m J G hG hu I hi
    (sublattice_initial_homology_generated n m J E hE hinit)
    (sublattice_first_ordered_lifts n m J E hE hinit hJ hβ) s p
  have hn := (nativePowerOrderedLifts_iff m J G hG hu s p).mpr hh
  simpa only [ActualIdealOrderedLifts, NativePowerOrderedLifts,
    nativePowerCoefficientBasis, actualIdealCoefficientBasis, actualIdealDegree,
    sublatticePowerQuotientData] using hn

/-- The ordinary graded Betti assertion of Theorem 4.3, for every field,
every finite row system, every sublattice, every original monomial order,
every homogeneous ideal with the specified initial ideal, and every power. -/
theorem theorem43_ordinary_betti
    (hβ : ∀ p q,sublatticePowerBettiNumber n m J E hE hinit hJ 1 p q=
      sublatticeMonomialPowerBettiNumber (K:=K) n E 1 p q) (s p q : ℕ) :
    sublatticePowerBettiNumber n m J E hE hinit hJ s p q=
      sublatticeMonomialPowerBettiNumber (K:=K) n E s p q :=
  ordinaryIdealBettiNumber_eq_monomial_of_ordered_lifts
    (sublatticePowerQuotientData n m J E hE hinit s) (homogeneousIdealPower n J hJ s)
    (sublattice_all_power_ordered_lifts n m J E hE hinit hJ hβ s) p q

/-- The homology-algebra generation assertion uses the literal Rees algebra
and actual tensor Koszul differential, with actual auxiliary-degree-one cycles. -/
theorem theorem43_rees_homology_generation
    (hβ : ∀ p q,sublatticePowerBettiNumber n m J E hE hinit hJ 1 p q=
      sublatticeMonomialPowerBettiNumber (K:=K) n E 1 p q) :
    Algebra.adjoin K (selectedHomologyClasses (idealReesKoszulDGA J)
      (WeightedRees.auxiliaryPiece m J G hG hu 1))=⊤ :=
  OrderedRees.homology_generated_in_degree_one m J I hi G hG hu
    (sublattice_initial_homology_generated n m J E hE hinit)
    (ordered_relative_lifts_of_power_coordinate_lifts m J G hG hu I hi 1
      (sublattice_first_ordered_lifts n m J E hE hinit hJ hβ))

end FourPapers.Sublattice

end
end
end


end
