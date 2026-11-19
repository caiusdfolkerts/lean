module
public import shared_results.part024
public import unit_interval_results.part002

set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

@[expose] public section

/- BEGIN EXACT BODY: FourPapers.Sublattice.UnitIntervalLemma61 -/
section

/-! # Lemma 6.1: the complete quotient Betti recursion

The outer polynomial variable is v (internal degree); the inner variable
is s (homological degree). The coefficient theorem identifies every
coefficient with actual ordinary derived Tor. Thus this is the paper's
finite polynomial identity, including its constant term and every degree.

`UnitIntervalRows d N` has d+1 rows, so the paper's factor s*v^d is written
with exponent d+1 here. Retained row sets are completely arbitrary.
-/

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency true
set_option synthInstance.maxHeartbeats 5000
noncomputable section
namespace FourPapers.Sublattice
open Classical CommAlg CommAlg.Koszul CommAlg.Polymatroid
universe u
variable {k : Type u} [Field k]
variable {d N : ℕ} {E : Finset ((Fin (d+1) → Fin N))}

/-- The full polynomial recursion in Lemma 6.1, for every variable
restriction. No interval hypothesis is imposed on the retained variables. -/
theorem lemma61_quotientBetti_recursion (hE : UnitIntervalFacetFamily E)
    (A : ∀ r : Fin (d+1),Finset (Fin N)) :
    quotientBettiPolynomial (k := k)
      (finiteRowFamily (UnitIntervalRows d N) (finiteRowRestriction E A)) =
    1+Polynomial.monomial (d+1) (Polynomial.X : Polynomial ℕ) *
      ∑ a : finiteRowRestriction E A,
        (1+Polynomial.monomial 1 (Polynomial.X : Polynomial ℕ))^
          (retainedFacetLinearVariables.{u} (E := E) A a.val).card *
        quotientBettiPolynomial (k := k) (retainedFacetResidualFamily (E := E) A a.val) := by
  rw [firstPowerQuotientBettiPolynomial_colon_recursion (k := k)
    (n := UnitIntervalRows d N) (E := finiteRowRestriction E A)
    (finiteRowRestriction_closed hE.latticeClosed A) (by omega)]
  congr 2
  apply Finset.sum_congr rfl
  intro a _
  rw [quotientBettiPolynomial_eq_of_contains (k := k)
    (unitIntervalRetainedPredecessor_contains_iff hE A a.property)]
  have hfactor := quotientBettiPolynomial_linear_factor (k := k)
    (retainedFacetLinearVariables.{u} (E := E) A a.val)
    (retainedFacetResidualFamily.{u} (E := E) A a.val)
    (retainedFacetResidualFamily_disjoint hE A a.val)
  refine Eq.trans ?_ hfactor
  apply quotientBettiPolynomial_eq_of_contains (k := k)
  intro α
  simp only [Contains, variableMonomialFamily, Finset.mem_union, Finset.mem_image]

/-- Reader-facing interpretation of every coefficient on the left side of
the recursion. This prevents a combinatorially stipulated polynomial from
standing in for the actual quotient Betti invariant. -/
theorem lemma61_quotientBetti_recursion_coeff
    (A : ∀ r : Fin (d+1),Finset (Fin N)) (q p : ℕ) :
    ((quotientBettiPolynomial (k := k)
      (finiteRowFamily (UnitIntervalRows d N) (finiteRowRestriction E A))).coeff q).coeff p =
      ordinaryQuotientBettiNumber (k := k)
        (finiteRowFamily (UnitIntervalRows d N) (finiteRowRestriction E A)) q p :=
  quotientBettiPolynomial_coeff _ finiteRowFamily_squarefree q p

/-- The same coefficient interpretation in the literal integer grading.
The negative-degree branch is zero by a proved vanishing of the actual
Koszul strands, not by replacing a negative degree with zero. -/
theorem lemma61_quotientBetti_recursion_integer_coeff
    (A : ∀ r : Fin (d+1),Finset (Fin N)) (q : ℤ) (p : ℕ) :
    (if 0≤q then
      ((quotientBettiPolynomial (k := k)
        (finiteRowFamily (UnitIntervalRows d N) (finiteRowRestriction E A))).coeff q.toNat).coeff p
      else 0) = integerOrdinaryQuotientBettiNumber (K := k)
        (finiteRowFamily (UnitIntervalRows d N) (finiteRowRestriction E A)) q p := by
  by_cases hq : 0≤q
  · obtain ⟨j,rfl⟩ := Int.eq_ofNat_of_zero_le hq
    rw [if_pos (by omega),Int.toNat_natCast,integerOrdinaryQuotientBettiNumber_nat]
    exact lemma61_quotientBetti_recursion_coeff A j p
  · rw [if_neg hq,integerOrdinaryQuotientBettiNumber_negative _ _ (lt_of_not_ge hq) p]

/-- The paper's exact smaller-ring form: each quotient polynomial is
computed over S_U itself. `retainedGeneratorFamily_ideal` proves that
its ideal is the literal inverse image I ∩ S_U. -/
theorem lemma61_quotientBetti_recursion_in_retained_ring
    (hE : UnitIntervalFacetFamily E) (A : ∀ r : Fin (d+1),Finset (Fin N)) :
    quotientBettiPolynomial (k := k)
      (retainedGeneratorFamily (retainedRowVariables A) (finiteRowFamily (UnitIntervalRows d N) E)) =
    1+Polynomial.monomial (d+1) (Polynomial.X : Polynomial ℕ) *
      ∑ a : finiteRowRestriction E A,
        (1+Polynomial.monomial 1 (Polynomial.X : Polynomial ℕ))^
          (retainedFacetLinearVariables.{u} (E := E) A a.val).card *
        quotientBettiPolynomial (k := k)
          (retainedGeneratorFamily (retainedRowVariables A)
            (finiteRowFamily (UnitIntervalRows d N) (facetResidualFacets E a.val))) := by
  simp_rw [retainedQuotientBettiPolynomial_eq,restrictMonomialFamily_rows]
  exact lemma61_quotientBetti_recursion (k := k) hE A

/-- Lemma 6.1 stated directly for an arbitrary subset of matrix variables.
The explicit inverse `retainedRowsOfVariables` proves that the rowwise
encoding in the computational formula imposes no restriction on `U`. -/
theorem lemma61_quotientBetti_recursion_arbitrary_variables
    (hE : UnitIntervalFacetFamily E)
    (U : Finset (FiniteVariable.{u} (UnitIntervalRows d N))) :
    quotientBettiPolynomial (k := k)
      (retainedGeneratorFamily U (finiteRowFamily (UnitIntervalRows d N) E)) =
    1 + Polynomial.monomial (d + 1) (Polynomial.X : Polynomial ℕ) *
      ∑ a : finiteRowRestriction E (retainedRowsOfVariables U),
        (1 + Polynomial.monomial 1 (Polynomial.X : Polynomial ℕ)) ^
          (retainedFacetLinearVariables.{u} (E := E) (retainedRowsOfVariables U) a.val).card *
        quotientBettiPolynomial (k := k)
          (retainedGeneratorFamily U
            (finiteRowFamily (UnitIntervalRows d N) (facetResidualFacets E a.val))) := by
  let A := retainedRowsOfVariables U
  let P := fun W : Finset (FiniteVariable.{u} (UnitIntervalRows d N)) =>
    quotientBettiPolynomial (k := k)
      (retainedGeneratorFamily W (finiteRowFamily (UnitIntervalRows d N) E)) =
    1 + Polynomial.monomial (d + 1) (Polynomial.X : Polynomial ℕ) *
      ∑ a : finiteRowRestriction E A,
        (1 + Polynomial.monomial 1 (Polynomial.X : Polynomial ℕ)) ^
          (retainedFacetLinearVariables.{u} (E := E) A a.val).card *
        quotientBettiPolynomial (k := k)
          (retainedGeneratorFamily W
            (finiteRowFamily (UnitIntervalRows d N) (facetResidualFacets E a.val)))
  exact Eq.mp (congrArg P
    (retainedRowVariables_rowsOfVariables (n := UnitIntervalRows d N) U))
      (lemma61_quotientBetti_recursion_in_retained_ring (k := k) hE A)

/-- All natural-degree coefficients in the literal smaller ring are the
actual derived Tor dimensions, including its homological-zero summand. -/
theorem lemma61_retained_ring_coeff
    (A : ∀ r : Fin (d+1),Finset (Fin N)) (q p : ℕ) :
    ((quotientBettiPolynomial (k := k)
      (retainedGeneratorFamily (retainedRowVariables A) (finiteRowFamily (UnitIntervalRows d N) E))).coeff q).coeff p =
      ordinaryQuotientBettiNumber (k := k)
        (retainedGeneratorFamily (retainedRowVariables A) (finiteRowFamily (UnitIntervalRows d N) E)) q p :=
  quotientBettiPolynomial_coeff _
    (retainedGeneratorFamily_squarefree _ _ finiteRowFamily_squarefree) q p

/-- The literal retained-ring interpretation also covers every integer
internal degree; the actual negative Koszul strands vanish. -/
theorem lemma61_retained_ring_integer_coeff
    (A : ∀ r : Fin (d+1), Finset (Fin N)) (q : ℤ) (p : ℕ) :
    (if 0 ≤ q then
      ((quotientBettiPolynomial (k := k)
        (retainedGeneratorFamily (retainedRowVariables A)
          (finiteRowFamily (UnitIntervalRows d N) E))).coeff q.toNat).coeff p
      else 0) = integerOrdinaryQuotientBettiNumber (K := k)
        (retainedGeneratorFamily (retainedRowVariables A)
          (finiteRowFamily (UnitIntervalRows d N) E)) q p := by
  by_cases hq : 0 ≤ q
  · obtain ⟨j, rfl⟩ := Int.eq_ofNat_of_zero_le hq
    rw [if_pos (by omega), Int.toNat_natCast, integerOrdinaryQuotientBettiNumber_nat]
    exact lemma61_retained_ring_coeff A j p
  · rw [if_neg hq, integerOrdinaryQuotientBettiNumber_negative _ _ (lt_of_not_ge hq) p]

end FourPapers.Sublattice

#print axioms FourPapers.Sublattice.lemma61_quotientBetti_recursion
#print axioms FourPapers.Sublattice.lemma61_quotientBetti_recursion_coeff

#print axioms FourPapers.Sublattice.lemma61_quotientBetti_recursion_in_retained_ring
#print axioms FourPapers.Sublattice.lemma61_retained_ring_integer_coeff
#print axioms FourPapers.Sublattice.retainedGeneratorFamily_ideal
#print axioms FourPapers.Sublattice.lemma61_quotientBetti_recursion_arbitrary_variables

end
end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.InitialColumnPrefixDeterminantal -/
section

/-! # Section 6.3 for initial-column determinantal prefixes

All initial and Betti comparisons below are derived for the actual
maximal-minor ideals. There is no additional first-power, colored-initial,
or characteristic-independence hypothesis.
-/

section
set_option autoImplicit false
set_option maxHeartbeats 20000
set_option synthInstance.maxHeartbeats 5000
noncomputable section
namespace FourPapers.Sublattice
open Classical CommAlg CommAlg.Polymatroid MvPolynomial
open IntegerFiltered.MultiplicativeFiltration
attribute [local instance] MvPolynomial.weightedGradedAlgebra
universe u
variable {K : Type u} [Field K] {d N r : ℕ}
  {E : Finset (FiniteTuple (UnitIntervalRows d N))}
local notation "n" => UnitIntervalRows d N
variable (hE : UnitIntervalFacetFamily E) (c : Fin r → ℕ) (hc : Monotone c)

def prefixMinorIdeals (E : Finset (FiniteTuple n)) (c : Fin r → ℕ) :
    ULift.{u} (Fin r) → Ideal (MvPolynomial (FiniteVariable.{u} n) K) :=
  fun i => facetMinorIdeal (initialColumnPrefix E (c i.down))

include hc in
theorem prefixMinorIdeals_mono : Monotone (prefixMinorIdeals (K := K) E c) := by
  intro i j hij
  apply Ideal.span_mono
  rintro f ⟨a,ha,rfl⟩
  exact ⟨a,initialColumnPrefix_mono E (hc hij) ha,rfl⟩

 theorem prefixMinorIdeals_homogeneous (i : ULift.{u} (Fin r)) :
    (prefixMinorIdeals (K := K) E c i).IsHomogeneous
      (weightedHomogeneousSubmodule K (fun _ : (FiniteVariable.{u} n) => (1 : ℕ))) := by
  simpa only [prefixMinorIdeals, pow_one] using
    facetMinorPower_ordinary_homogeneous (k := K) (initialColumnPrefix E (c i.down)) 1

include hE in
theorem prefixMinorIdeals_initial (i : ULift.{u} (Fin r)) :
    FourPapers.initialIdeal facetLexOrder (prefixMinorIdeals (K := K) E c i)=
      coloredIdeals (k := K) n (initialColumnPrefixes E c) i :=
  unitInterval_initialIdeal (hE.initialColumnPrefix (c i.down))

include hE hc in
theorem prefixMixed_initial (m : ULift.{u} (Fin r) →₀ ℕ) :
    FourPapers.initialIdeal facetLexOrder (powerProduct (prefixMinorIdeals (K := K) E c) m)=
      powerProduct (coloredIdeals (k := K) n (initialColumnPrefixes E c)) m :=
  corollary57_original_initial (prefixMinorIdeals E c) (initialColumnPrefixes E c)
    facetLexOrder (initialColumnPrefixes_colored hE c hc)
    (prefixMinorIdeals_mono c hc) (prefixMinorIdeals_initial hE c) m

 theorem prefixMixed_first_betti (hd : 2≤d) (i : ULift.{u} (Fin r)) (p q : ℕ) :
    mixedPowerBettiNumber n (initialColumnPrefixes E c) facetLexOrder
      (prefixMinorIdeals (K := K) E c) (prefixMixed_initial hE c hc)
      (prefixMinorIdeals_homogeneous c) (Finsupp.single i 1) p q=
    mixedMonomialBettiNumber (K := K) n (initialColumnPrefixes E c) (Finsupp.single i 1) p q := by
  let B := mixedRowPowerFamily n (initialColumnPrefixes E c) (Finsupp.single i 1)
  let C := exponentPowerFamily (finiteRowFamily n (initialColumnPrefix E (c i.down))) 1
  let l₀ : LinearOrder (FiniteVariable.{u} n) := finiteVariableLinearOrder n
  have hI : monomialIdeal K C=monomialIdeal K B := by
    rw [finitePowerFamily_ideal,pow_one,mixedRowPowerFamily_ideal,powerProduct_unit]
    rfl
  calc
    _ = unitIntervalGradedBetti (K := K) (hE.initialColumnPrefix (c i.down)) 1 p q := by
      apply ordinaryIdealBettiNumber_presentation (finiteVariableLinearOrder n) l₀
      change powerProduct (prefixMinorIdeals (K := K) E c) (Finsupp.single i 1)=
        facetMinorIdeal (initialColumnPrefix E (c i.down))^1
      rw [powerProduct_unit,pow_one]
      rfl
    _ = (haveI := l₀; ordinaryMonomialBettiNumber (k := K) C q p) :=
      theorem65_bettiEquality (hE.initialColumnPrefix (c i.down)) hd 1 (by omega) p q
    _ = _ := ordinaryMonomialBettiNumber_presentation l₀
      (finiteVariableLinearOrder n) facetLexOrder C B hI q p

def prefixMixedBettiNumber (m : ULift.{u} (Fin r) →₀ ℕ) (p : ℕ) (q : ℤ) : ℕ :=
  mixedIntegerPowerBettiNumber n (initialColumnPrefixes E c) facetLexOrder
    (prefixMinorIdeals (K := K) E c) (prefixMixed_initial hE c hc)
    (prefixMinorIdeals_homogeneous c) m p q

/-- All mixed Betti equalities for the literal initial-column determinant
ideals, in every integer ordinary degree. -/
theorem initialColumnPrefix_determinantal_mixed_betti (hd : 2≤d)
    (m : ULift.{u} (Fin r) →₀ ℕ) (p : ℕ) (q : ℤ) :
    prefixMixedBettiNumber (K := K) hE c hc m p q=
      mixedIntegerMonomialBettiNumber (K := K) n (initialColumnPrefixes E c) facetLexOrder m p q :=
  corollary57_betti n (initialColumnPrefixes E c) (initialColumnPrefixes_colored hE c hc)
    (prefixMinorIdeals E c) (prefixMinorIdeals_homogeneous c) facetLexOrder
    (prefixMinorIdeals_mono c hc) (prefixMinorIdeals_initial hE c)
    (prefixMixed_first_betti hE c hc hd) m p q

include hE hc in
/-- Every ideal equality (5.3) holds for the actual determinant prefixes. -/
theorem initialColumnPrefix_determinantal_ideal_identities
    (m : ULift.{u} (Fin r) →₀ ℕ) :
    powerProduct (prefixMinorIdeals (K := K) E c) m=
      (⨅ i,(prefixMinorIdeals (K := K) E c i)^prefixExponent m i) ∧
    powerProduct (coloredIdeals (k := K) n (initialColumnPrefixes E c)) m=
      (⨅ i,(coloredIdeals (k := K) n (initialColumnPrefixes E c) i)^prefixExponent m i) ∧
    FourPapers.initialIdeal facetLexOrder (powerProduct (prefixMinorIdeals (K := K) E c) m)=
      powerProduct (coloredIdeals (k := K) n (initialColumnPrefixes E c)) m :=
  corollary57_ideal_identities (prefixMinorIdeals E c) (initialColumnPrefixes E c)
    facetLexOrder (initialColumnPrefixes_colored hE c hc)
    (prefixMinorIdeals_mono c hc) (prefixMinorIdeals_initial hE c) m


 theorem initialColumnPrefix_determinantal_mixed_field_independent
    (L : Type u) [Field L] (hd : 2≤d)
    (m : ULift.{u} (Fin r) →₀ ℕ) (p : ℕ) (q : ℤ) :
    prefixMixedBettiNumber (K := K) hE c hc m p q=
      prefixMixedBettiNumber (K := L) hE c hc m p q := by
  rw [initialColumnPrefix_determinantal_mixed_betti hE c hc hd,
    initialColumnPrefix_determinantal_mixed_betti hE c hc hd]
  exact initialColumnPrefix_mixed_integer_monomial_field_independent hE c hc facetLexOrder L m p q

include hE hc in
theorem initialColumnPrefix_determinantal_generation (hd : 2≤d) :
    Algebra.adjoin K
      (selectedHomologyClasses (MixedTransfer.idealReesKoszulDGA (prefixMinorIdeals (K := K) E c))
        (MixedTransfer.Auxiliary.selectedPiece facetLexOrder (prefixMinorIdeals (K := K) E c)
          (canonicalMixedGenerators n (prefixMinorIdeals (K := K) E c))
          (canonicalMixedGroebner n facetLexOrder (prefixMinorIdeals (K := K) E c))
          (canonicalMixedUnitLeading n facetLexOrder (prefixMinorIdeals (K := K) E c))
          (coordinateUnitDegrees (r := r))))=⊤ :=
  corollary57_generation n (initialColumnPrefixes E c) (initialColumnPrefixes_colored hE c hc)
    (prefixMinorIdeals E c) (prefixMinorIdeals_homogeneous c) facetLexOrder
    (prefixMinorIdeals_mono c hc) (prefixMinorIdeals_initial hE c)
    (prefixMixed_first_betti hE c hc hd)

end FourPapers.Sublattice

#print axioms FourPapers.Sublattice.initialColumnPrefix_determinantal_mixed_betti

#print axioms FourPapers.Sublattice.initialColumnPrefix_determinantal_ideal_identities

#print axioms FourPapers.Sublattice.initialColumnPrefix_determinantal_mixed_field_independent

#print axioms FourPapers.Sublattice.initialColumnPrefix_determinantal_generation

end
end
end


end
