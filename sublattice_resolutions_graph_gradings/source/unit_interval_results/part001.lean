module
public import shared_results.part021
public import graph_homology
public import unit_diagonal_weight
public import unit_interval_support_foundation

set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

@[expose] public section

/- BEGIN EXACT BODY: FourPapers.Sublattice.UnitIntervalOrdinaryBetti -/
section

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 20000
set_option synthInstance.maxHeartbeats 5000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace FourPapers.Sublattice
open Classical CommAlg CommAlg.Koszul CommAlg.Polymatroid
universe u
variable {d N : ℕ} {E : Finset ((Fin (d+1) → Fin N))}

/-- The adjacent-degree gap is a statement about the actual ordinary
homology groups, uniformly in every leading monomial/weight component. -/
theorem unitInterval_ordinary_homology_gap {k : Type u} [CommRing k]
    (hE : UnitIntervalFacetFamily E) (hd : 2 ≤ d)
    (m : ℕ) (hm : 0 < m) (q p : ℕ) :
    Subsingleton (ordinaryMonomialHomology (k := k)
      (exponentPowerFamily (finiteRowFamily (UnitIntervalRows d N) E) m) q p) ∨
    Subsingleton (ordinaryMonomialHomology (k := k)
      (exponentPowerFamily (finiteRowFamily (UnitIntervalRows d N) E) m) q (p+1)) := by
  rcases unitInterval_power_ordinary_gap (k := k) hE hd m hm q p with hp | hp
  · exact Or.inl (ordinaryMonomialHomology_subsingleton_of_exact _ q p hp)
  · exact Or.inr (ordinaryMonomialHomology_subsingleton_of_exact _ q (p+1) hp)

/-- The common ordinary Betti table is independent of the characteristic.
The equality is derived from literal fine Tor after proving the coarsening
isomorphism of actual complexes. -/
theorem unitInterval_monomial_ordinary_betti_field_independent
    (K L : Type u) [Field K] [Field L] (hE : UnitIntervalFacetFamily E)
    (m : ℕ) (hm : 0 < m) (q p : ℕ) :
    ordinaryMonomialBettiNumber (k := K)
      (exponentPowerFamily (finiteRowFamily (UnitIntervalRows d N) E) m) q p =
    ordinaryMonomialBettiNumber (k := L)
      (exponentPowerFamily (finiteRowFamily (UnitIntervalRows d N) E) m) q p := by
  rw [ordinaryMonomialBettiNumber_eq_sum, ordinaryMonomialBettiNumber_eq_sum]
  apply Finset.sum_congr rfl
  intro α _
  exact unitInterval_power_betti_field_independent K L hE m hm α.val p

/-- The support condition in Theorem 6.5, in its equivalent additive
form in `ZMod (row count - 1)`. The ordinary degree includes the exterior
degree, as in the conventional graded Betti number. -/
theorem unitInterval_monomial_ordinary_betti_congruence
    {K : Type u} [Field K] (hE : UnitIntervalFacetFamily E)
    (m : ℕ) (hm : 0 < m) (q p : ℕ)
    (hp : ordinaryMonomialBettiNumber (k := K)
      (exponentPowerFamily (finiteRowFamily (UnitIntervalRows d N) E) m) q p ≠ 0) :
    (q : ZMod d) - (p : ZMod d) = (m : ZMod d) := by
  rw [ordinaryMonomialBettiNumber_eq_sum] at hp
  obtain ⟨α, _, hα⟩ := Finset.exists_ne_zero_of_sum_ne_zero hp
  have h := unitInterval_power_betti_congruence (K := K) hE m hm α.val p hα
  rw [α.property] at h
  linear_combination -h

end FourPapers.Sublattice
end

#print axioms FourPapers.Sublattice.unitInterval_ordinary_homology_gap
#print axioms FourPapers.Sublattice.unitInterval_monomial_ordinary_betti_field_independent
#print axioms FourPapers.Sublattice.unitInterval_monomial_ordinary_betti_congruence

end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.IdealGapComparison -/
section

/-!
# Betti preservation from a uniform adjacent-degree gap

The input is a genuine monic Gröbner basis and strict numerical tails.
The graded comparison acts on the actual polynomial ideal's Koszul
coordinates. A gap in the full ordinary strand produces actual cycle
lifts at every weight; finite filtered homology then gives equality with
the literal monomial ideal. No first-power equality is assumed here.
-/

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 100000
set_option synthInstance.maxHeartbeats 5000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace FourPapers.Sublattice
open Classical CategoryTheory CommAlg CommAlg.Koszul CommAlg.Polymatroid MvPolynomial
open FourPapers.Universal FourPapers.FilteredHomology
attribute [local instance] MvPolynomial.weightedGradedAlgebra
attribute [local instance] ordinaryPieceAddCommGroup ordinaryPieceModule
universe u

section Ring
variable {V k : Type u} [Fintype V] [LinearOrder V] [CommRing k] [Nontrivial k]
  (P : QuotientGroebnerData V k)


variable
  (hJ : P.ideal.IsHomogeneous (weightedHomogeneousSubmodule k (fun _ : V => (1 : ℕ))))
  (w : V → ℕ)
  (htail : ∀ g ∈ P.generators, g ≠ 0 →
    ∀ a ∈ (monomial (P.order.degree g) 1-g).support,
      Finsupp.weight w a < Finsupp.weight w (P.order.degree g))

theorem actualIdealGradedHomology_subsingleton_of_fine (q p : ℕ)
    (hzero : ∀ α : Exponent V, α.degree = q →
      Subsingleton ((homogeneousComplex (k := k) P.family α).homology p)) (n : ℕ) :
    Subsingleton (actualIdealGradedHomology P hJ w htail q p n) := by
  letI : ∀ α : IdealOrdinaryFineIndex w q n,
      Subsingleton ((homogeneousComplex (k := k) P.family α.val).homology p) :=
    fun α => hzero α.val (congrArg Prod.fst α.property)
  exact ⟨fun x y => (actualIdealGradedHomologyEquiv P hJ w htail
    (actualIdealPrevious_strictly_lowers_of_tails P w htail) q p n).injective
      (Subsingleton.elim _ _)⟩

/-- Expose the three graded maps while the homological degree is abstract.
Later successor specializations can compare these named maps directly. -/
private theorem actualIdealGradedHomology_subsingleton_of_fine_maps (q p : ℕ)
    (hzero : ∀ α : Exponent V, α.degree = q →
      Subsingleton ((homogeneousComplex (k := k) P.family α).homology p)) (n : ℕ) :
    Subsingleton (GradedHomology
      (actualIdealOrdinaryFiltration P w q (p+1)) (actualIdealOrdinaryFiltration P w q p)
      (actualIdealOrdinaryFiltration P w q p.pred)
      (actualIdealOrdinaryDifferential P hJ q p) (actualIdealOrdinaryPrevious P hJ q p)
      (actualIdealOrdinaryDifferential_preserves P hJ w htail q p)
      (actualIdealOrdinaryPrevious_preserves P hJ w htail q p)
      (actualIdealOrdinaryDifferential_comp P hJ q p) n) :=
  actualIdealGradedHomology_subsingleton_of_fine P hJ w htail q p hzero n

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency true in
include htail in
/-- A uniform gap in adjacent ordinary homology, across all fine degrees,
gives lifts of every associated cycle of the actual ordinary differential. -/
theorem actualIdealOrdinaryPrevious_lifts_of_fine_gap (q : ℕ)
    (hgap : ∀ p : ℕ,
      (∀ α : Exponent V, α.degree = q →
        Subsingleton ((homogeneousComplex (k := k) P.family α).homology p)) ∨
      (∀ α : Exponent V, α.degree = q →
        Subsingleton ((homogeneousComplex (k := k) P.family α).homology (p+1))))
    (p : ℕ) :
    LiftsCycles (actualIdealOrdinaryFiltration P w q p)
      (actualIdealOrdinaryFiltration P w q p.pred) (actualIdealOrdinaryPrevious P hJ q p) := by
  cases p with
  | zero =>
      intro n x hx _
      refine ⟨x, hx, rfl, ?_⟩
      simpa only [sub_self] using ((actualIdealOrdinaryFiltration P w q 0).level n).zero_mem
  | succ p =>
      apply liftsCycles_of_homology_gap
        (actualIdealOrdinaryFiltration P w q (p+2))
        (actualIdealOrdinaryFiltration P w q (p+1))
        (actualIdealOrdinaryFiltration P w q p)
        (actualIdealOrdinaryFiltration P w q p.pred)
        (actualIdealOrdinaryDifferential P hJ q (p+1))
        (actualIdealOrdinaryPrevious P hJ q (p+1))
        (actualIdealOrdinaryPrevious P hJ q p)
        (actualIdealOrdinaryDifferential_preserves P hJ w htail q (p+1))
        (actualIdealOrdinaryPrevious_preserves P hJ w htail q (p+1))
        (actualIdealOrdinaryPrevious_preserves P hJ w htail q p)
        (actualIdealOrdinaryDifferential_comp P hJ q (p+1))
        (actualIdealOrdinaryDifferential_comp P hJ q p)
      rcases hgap p with hp | hp
      · right
        exact actualIdealGradedHomology_subsingleton_of_fine_maps P hJ w htail q p hp
      · left
        exact actualIdealGradedHomology_subsingleton_of_fine_maps P hJ w htail q (p+1) hp

end Ring

section Field
variable {V k : Type u} [Fintype V] [LinearOrder V] [Field k]
  (P : QuotientGroebnerData V k)
  (hJ : P.ideal.IsHomogeneous (weightedHomogeneousSubmodule k (fun _ : V => (1 : ℕ))))
  (w : V → ℕ)
  (htail : ∀ g ∈ P.generators, g ≠ 0 →
    ∀ a ∈ (monomial (P.order.degree g) 1-g).support,
      Finsupp.weight w a < Finsupp.weight w (P.order.degree g))

include htail in
theorem actualIdealOrdinaryHomology_finrank_eq_initial_of_ordinary_lifts
    (M : ℕ) (hM : ∀ v, w v ≤ M) (q : ℕ)
    (hlift : ∀ p, LiftsCycles (actualIdealOrdinaryFiltration P w q p)
      (actualIdealOrdinaryFiltration P w q p.pred) (actualIdealOrdinaryPrevious P hJ q p))
    (p : ℕ) :
    Module.finrank k (actualIdealOrdinaryHomology P hJ q p) =
      Module.finrank k (initialActualIdealOrdinaryHomology P q p) := by
  letI := actualIdealOrdinaryPiece_finite P q (p+1)
  letI := actualIdealOrdinaryPiece_finite P q p
  have hactual := finrank_homology_eq_sum_graded
    (actualIdealOrdinaryFiltration P w q (p+1)) (actualIdealOrdinaryFiltration P w q p)
    (actualIdealOrdinaryFiltration P w q p.pred)
    (actualIdealOrdinaryDifferential P hJ q p) (actualIdealOrdinaryPrevious P hJ q p)
    (actualIdealOrdinaryDifferential_preserves P hJ w htail q p)
    (actualIdealOrdinaryPrevious_preserves P hJ w htail q p)
    (actualIdealOrdinaryDifferential_comp P hJ q p)
    (M*q+1) (actualIdealOrdinaryFiltration_top P w M hM q p) (hlift (p+1)) (hlift p)
  have hinitial := finrank_homology_eq_sum_graded
    (actualIdealOrdinaryFiltration P w q (p+1)) (actualIdealOrdinaryFiltration P w q p)
    (actualIdealOrdinaryFiltration P w q p.pred)
    (initialActualIdealOrdinaryDifferential P q p) (initialActualIdealOrdinaryPrevious P q p)
    (initialActualIdealOrdinaryPrevious_preserves P w q (p+1))
    (initialActualIdealOrdinaryPrevious_preserves P w q p)
    (initialActualIdealOrdinaryDifferential_comp P q p)
    (M*q+1) (actualIdealOrdinaryFiltration_top P w M hM q p)
    (initialActualIdealOrdinaryPrevious_lifts P w q (p+1))
    (initialActualIdealOrdinaryPrevious_lifts P w q p)
  refine Eq.trans hactual (Eq.trans ?_ hinitial.symm)
  apply Finset.sum_congr rfl
  intro n _
  exact (actualInitialIdealGradedHomologyEquiv P w hJ htail
    (actualIdealPrevious_strictly_lowers_of_tails P w htail) q p n).finrank_eq

include htail in
/-- Complete ordinary Betti comparison from a proved gap in the actual
initial homology. Its conclusion uses the literal ordinary monomial
homology and all homological degrees, not a support surrogate. -/
theorem actualIdealOrdinaryHomology_finrank_eq_monomial_of_gap
    (M : ℕ) (hM : ∀ v, w v ≤ M) (q : ℕ)
    (hgap : ∀ p : ℕ,
      (∀ α : Exponent V, α.degree = q →
        Subsingleton ((homogeneousComplex (k := k) P.family α).homology p)) ∨
      (∀ α : Exponent V, α.degree = q →
        Subsingleton ((homogeneousComplex (k := k) P.family α).homology (p+1))))
    (p : ℕ) :
    Module.finrank k (actualIdealOrdinaryHomology P hJ q p) =
      ordinaryMonomialBettiNumber (k := k) P.family q p := by
  rw [actualIdealOrdinaryHomology_finrank_eq_initial_of_ordinary_lifts
    P hJ w htail M hM q
    (actualIdealOrdinaryPrevious_lifts_of_fine_gap P hJ w htail q hgap) p]
  exact (initialActualIdealOrdinaryHomologyEquiv P q p).finrank_eq

end Field
end FourPapers.Sublattice
end

#print axioms FourPapers.Sublattice.actualIdealOrdinaryPrevious_lifts_of_fine_gap
#print axioms FourPapers.Sublattice.actualIdealOrdinaryHomology_finrank_eq_monomial_of_gap

end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.UnitIntervalTheorem65 -/
section

/-!
# Theorem 6.5: all powers of unit-interval determinantal ideals

The matrix has `d+1` rows, with `2 ≤ d`, and an arbitrary finite number
of columns. Its generators are the actual determinants. All powers,
ordinary degrees, homological degrees, and coefficient fields are
retained. The empty facet family is included. Gröbner identities,
homogeneity, diagonal weights, the no-adjacent-degree gap, and coefficient
independence are proved inputs rather than additional assumptions.

The left-hand Betti number is defined as the dimension of the ordinary
degree component inside Mathlib's genuine derived `Tor`. The monomial
side is actual ordinary Koszul homology, identified by the proved finite
coarsening isomorphism with the sum of genuine fine derived-Tor pieces.
-/

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 20000
set_option synthInstance.maxHeartbeats 5000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace FourPapers.Sublattice
open Classical CategoryTheory CommAlg CommAlg.Koszul CommAlg.Polymatroid
universe u
variable {d N : ℕ} {E : Finset ((Fin (d+1) → Fin N))}

theorem unitInterval_power_betti_eq_monomial {K : Type u} [Field K]
    (hE : UnitIntervalFacetFamily E) (hd : 2 ≤ d)
    (m : ℕ) (hm : 0 < m) (q p : ℕ) :
    unitIntervalBettiNumber (k := K) hE m q p =
      ordinaryMonomialBettiNumber (k := K)
        (exponentPowerFamily (finiteRowFamily (UnitIntervalRows d N) E) m) q p := by
  apply actualIdealOrdinaryHomology_finrank_eq_monomial_of_gap
    (unitIntervalPowerQuotientData (k := K) hE m)
    (facetMinorPower_ordinary_homogeneous E m)
    facetDiagonalWeight (unitInterval_minorProducts_weight_tails hE m)
    (d*N) facetDiagonalWeight_le q _ p
  intro r
  rcases unitInterval_power_uniform_homology_gap (k := K) hE hd m hm q r with hr | hr
  · left
    intro α hα
    exact ModuleCat.isZero_iff_subsingleton.mp (hr α hα)
  · right
    intro α hα
    exact ModuleCat.isZero_iff_subsingleton.mp (hr α hα)

/-- The conventional argument order `p,q`, and the actual ordinary
graded derived Tor of the literal determinantal power. -/
abbrev unitIntervalGradedBetti {K : Type u} [Field K]
    (hE : UnitIntervalFacetFamily E) (m p q : ℕ) : ℕ :=
  ordinaryIdealBettiNumber (unitIntervalPowerQuotientData (k := K) hE m)
    (facetMinorPower_ordinary_homogeneous E m) p q

/-- The Betti equality of Theorem 6.5, in every positive power and every
ordinary and homological degree, for all fields and all row counts ≥3. -/
theorem theorem65_bettiEquality {K : Type u} [Field K]
    (hE : UnitIntervalFacetFamily E) (hd : 2 ≤ d)
    (m : ℕ) (hm : 0 < m) (p q : ℕ) :
    unitIntervalGradedBetti (K := K) hE m p q =
      ordinaryMonomialBettiNumber (k := K)
        (exponentPowerFamily (finiteRowFamily (UnitIntervalRows d N) E) m) q p := by
  rw [unitIntervalGradedBetti, ordinaryIdealBettiNumber_eq_finrank]
  exact unitInterval_power_betti_eq_monomial hE hd m hm q p

/-- The same equality expressed entirely through the established fine
derived-Tor dimensions of the actual initial ideal power. -/
theorem theorem65_bettiEquality_fineSum {K : Type u} [Field K]
    (hE : UnitIntervalFacetFamily E) (hd : 2 ≤ d)
    (m : ℕ) (hm : 0 < m) (p q : ℕ) :
    unitIntervalGradedBetti (K := K) hE m p q =
      ∑ α : OrdinaryFineIndex (FiniteVariable.{u} (UnitIntervalRows d N)) q,
        bettiNumber (k := K)
          (exponentPowerFamily (finiteRowFamily (UnitIntervalRows d N) E) m) α.val p := by
  rw [theorem65_bettiEquality hE hd m hm p q, ordinaryMonomialBettiNumber_eq_sum]

/-- The common ordinary Betti table is independent of the field, including
every positive characteristic. -/
theorem theorem65_fieldIndependence (K L : Type u) [Field K] [Field L]
    (hE : UnitIntervalFacetFamily E) (hd : 2 ≤ d)
    (m : ℕ) (hm : 0 < m) (p q : ℕ) :
    unitIntervalGradedBetti (K := K) hE m p q =
      unitIntervalGradedBetti (K := L) hE m p q := by
  rw [theorem65_bettiEquality hE hd m hm p q,
    theorem65_bettiEquality hE hd m hm p q]
  exact unitInterval_monomial_ordinary_betti_field_independent K L hE m hm q p

/-- The nonzero-entry congruence, with modulus exactly the row count
minus one. It is stated in the quotient ring of integers modulo that
modulus, so subtraction has its ordinary mathematical meaning. -/
theorem theorem65_supportCongruence {K : Type u} [Field K]
    (hE : UnitIntervalFacetFamily E) (hd : 2 ≤ d)
    (m : ℕ) (hm : 0 < m) (p q : ℕ)
    (hβ : unitIntervalGradedBetti (K := K) hE m p q ≠ 0) :
    (q : ZMod d) - (p : ZMod d) = (m : ZMod d) := by
  rw [theorem65_bettiEquality hE hd m hm p q] at hβ
  exact unitInterval_monomial_ordinary_betti_congruence hE m hm q p hβ

/-- All clauses of Theorem 6.5, with no Gröbner, homology, or
characteristic-independence assumptions left in the statement. -/
theorem theorem65 (K : Type u) [Field K]
    (hE : UnitIntervalFacetFamily E) (hd : 2 ≤ d)
    (m : ℕ) (hm : 0 < m) (p q : ℕ) :
    unitIntervalGradedBetti (K := K) hE m p q =
      ordinaryMonomialBettiNumber (k := K)
        (exponentPowerFamily (finiteRowFamily (UnitIntervalRows d N) E) m) q p ∧
    (∀ (L : Type u) [Field L], unitIntervalGradedBetti (K := K) hE m p q =
      unitIntervalGradedBetti (K := L) hE m p q) ∧
    (unitIntervalGradedBetti (K := K) hE m p q ≠ 0 →
      (q : ZMod d) - (p : ZMod d) = (m : ZMod d)) :=
  ⟨theorem65_bettiEquality hE hd m hm p q,
    (fun L _ => theorem65_fieldIndependence K L hE hd m hm p q),
    theorem65_supportCongruence hE hd m hm p q⟩

end FourPapers.Sublattice
end

#print axioms FourPapers.Sublattice.theorem65_bettiEquality
#print axioms FourPapers.Sublattice.theorem65_fieldIndependence
#print axioms FourPapers.Sublattice.theorem65_supportCongruence
#print axioms FourPapers.Sublattice.theorem65

end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.UnitIntervalIntegerTheorem65 -/
section

/-!
# Theorem 6.5 in every integer ordinary degree

Both sides below are the homogeneous submodules of the genuine derived
Tor of the displayed ideal powers. Natural-degree comparison uses the
proved identity between canonical monomial coordinates and the original
monomial Koszul complex. Negative degrees vanish by the actual integer
regrading of polynomial and exterior degrees.
-/

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 20000
set_option synthInstance.maxHeartbeats 5000
noncomputable section

namespace FourPapers.Sublattice

open Classical CommAlg CommAlg.Koszul CommAlg.Polymatroid MvPolynomial
attribute [local instance] MvPolynomial.weightedGradedAlgebra
universe u
variable {d N : ℕ} {E : Finset ((Fin (d+1) → Fin N))}
  {K : Type u} [Field K]

def unitIntervalIntegerGradedBetti (hE : UnitIntervalFacetFamily E)
    (m p : ℕ) (q : ℤ) : ℕ :=
  ordinaryIntegerIdealBettiNumber (unitIntervalPowerQuotientData (k := K) hE m)
    (facetMinorPower_ordinary_homogeneous E m) p q

theorem monomialPower_homogeneous (m : ℕ) :
    (monomialIdeal K
      (exponentPowerFamily (finiteRowFamily (UnitIntervalRows d N) E) m)).IsHomogeneous
      (weightedHomogeneousSubmodule K
        (fun _ : FiniteVariable.{u} (UnitIntervalRows d N) => (1 : ℕ))) := by
  apply Ideal.homogeneous_span
  rintro f ⟨a,ha,rfl⟩
  exact ⟨Finsupp.weight (fun _ : FiniteVariable.{u} (UnitIntervalRows d N) => (1 : ℕ)) a,
    isWeightedHomogeneous_monomial _ a (1 : K) rfl⟩

def unitIntervalIntegerMonomialBetti (E : Finset ((Fin (d+1) → Fin N)))
    (m p : ℕ) (q : ℤ) : ℕ :=
  ordinaryIntegerIdealBettiNumber
    (canonicalQuotientGroebnerData facetLexOrder
      (monomialIdeal K (exponentPowerFamily (finiteRowFamily (UnitIntervalRows d N) E) m)))
    (monomialPower_homogeneous (K := K) (E := E) m) p q

@[simp] theorem unitIntervalIntegerGradedBetti_nat (hE : UnitIntervalFacetFamily E)
    (m p q : ℕ) :
    unitIntervalIntegerGradedBetti (K := K) hE m p (q : ℤ) =
      unitIntervalGradedBetti (K := K) hE m p q :=
  ordinaryIntegerIdealBettiNumber_nat _ _ p q

@[simp] theorem unitIntervalIntegerMonomialBetti_nat (m p q : ℕ) :
    unitIntervalIntegerMonomialBetti (K := K) E m p (q : ℤ) =
      ordinaryMonomialBettiNumber (k := K)
        (exponentPowerFamily (finiteRowFamily (UnitIntervalRows d N) E) m) q p := by
  unfold unitIntervalIntegerMonomialBetti
  rw [ordinaryIntegerIdealBettiNumber_nat]
  exact canonicalMonomialBettiNumber_eq facetLexOrder _
    (monomialPower_homogeneous (K := K) (E := E) m) q p

/-- Equality of the integer-graded derived-Tor dimensions of the actual
determinantal power and the actual diagonal monomial power. -/
theorem theorem65_integer_bettiEquality (hE : UnitIntervalFacetFamily E) (hd : 2 ≤ d)
    (m : ℕ) (hm : 0 < m) (p : ℕ) (q : ℤ) :
    unitIntervalIntegerGradedBetti (K := K) hE m p q =
      unitIntervalIntegerMonomialBetti (K := K) E m p q := by
  by_cases hq : 0 ≤ q
  · have he : (q.toNat : ℤ) = q := Int.toNat_of_nonneg hq
    rw [← he, unitIntervalIntegerGradedBetti_nat, unitIntervalIntegerMonomialBetti_nat]
    exact theorem65_bettiEquality hE hd m hm p q.toNat
  · have hq' : q < 0 := lt_of_not_ge hq
    unfold unitIntervalIntegerGradedBetti unitIntervalIntegerMonomialBetti
    rw [ordinaryIntegerIdealBettiNumber_negative _ _ p q hq',
      ordinaryIntegerIdealBettiNumber_negative _ _ p q hq']

theorem theorem65_integer_fieldIndependence (L : Type u) [Field L]
    (hE : UnitIntervalFacetFamily E) (hd : 2 ≤ d)
    (m : ℕ) (hm : 0 < m) (p : ℕ) (q : ℤ) :
    unitIntervalIntegerGradedBetti (K := K) hE m p q =
      unitIntervalIntegerGradedBetti (K := L) hE m p q := by
  by_cases hq : 0 ≤ q
  · have he : (q.toNat : ℤ) = q := Int.toNat_of_nonneg hq
    rw [← he, unitIntervalIntegerGradedBetti_nat, unitIntervalIntegerGradedBetti_nat]
    exact theorem65_fieldIndependence K L hE hd m hm p q.toNat
  · have hq' : q < 0 := lt_of_not_ge hq
    unfold unitIntervalIntegerGradedBetti
    rw [ordinaryIntegerIdealBettiNumber_negative _ _ p q hq',
      ordinaryIntegerIdealBettiNumber_negative _ _ p q hq']

theorem theorem65_integer_supportCongruence (hE : UnitIntervalFacetFamily E) (hd : 2 ≤ d)
    (m : ℕ) (hm : 0 < m) (p : ℕ) (q : ℤ)
    (hβ : unitIntervalIntegerGradedBetti (K := K) hE m p q ≠ 0) :
    (q : ZMod d) - (p : ZMod d) = (m : ZMod d) := by
  by_cases hq : 0 ≤ q
  · have he : (q.toNat : ℤ) = q := Int.toNat_of_nonneg hq
    rw [← he, unitIntervalIntegerGradedBetti_nat] at hβ
    rw [← he]
    simpa only [Int.cast_natCast] using
      theorem65_supportCongruence hE hd m hm p q.toNat hβ
  · have hq' : q < 0 := lt_of_not_ge hq
    exact False.elim (hβ (ordinaryIntegerIdealBettiNumber_negative _ _ p q hq'))

/-- All clauses of paper Theorem 6.5, with unrestricted integer internal
degree and the genuine derived-Tor interpretation on both sides. -/
theorem theorem65_integer (hE : UnitIntervalFacetFamily E) (hd : 2 ≤ d)
    (m : ℕ) (hm : 0 < m) (p : ℕ) (q : ℤ) :
    unitIntervalIntegerGradedBetti (K := K) hE m p q =
      unitIntervalIntegerMonomialBetti (K := K) E m p q ∧
    (∀ (L : Type u) [Field L], unitIntervalIntegerGradedBetti (K := K) hE m p q =
      unitIntervalIntegerGradedBetti (K := L) hE m p q) ∧
    (unitIntervalIntegerGradedBetti (K := K) hE m p q ≠ 0 →
      (q : ZMod d) - (p : ZMod d) = (m : ZMod d)) :=
  ⟨theorem65_integer_bettiEquality hE hd m hm p q,
    (fun L _ => theorem65_integer_fieldIndependence L hE hd m hm p q),
    theorem65_integer_supportCongruence hE hd m hm p q⟩

end FourPapers.Sublattice

#print axioms FourPapers.Sublattice.theorem65_integer

end
end
end


end
