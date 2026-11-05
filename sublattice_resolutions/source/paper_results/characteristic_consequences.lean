module
public import paper_results.quotient_total_homology_dimension
public import shared_results.part023
public import paper_results.part005
public import paper_results.dimension_core
public import shared_results.part003
public import Mathlib.Order.Int.ConditionallyCompleteOrder
public import paper_results.part002
public import Mathlib.Data.Finsupp.MonomialOrder.DegLex
public import paper_results.ordinary_ideal_tor_bounds
public import graph_foundation.part010
public import paper_results.transfer_formulas
public import paper_results.theorem81_analytic_spread
public import paper_results.torsion_core
public import paper_results.graded_homology_core
public import Mathlib.Algebra.CharP.Basic
public import graph_foundation.part009
public import paper_results.part003
public import paper_results.part004
public import graph_foundation.part008
public import paper_results.part001
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Algebra.Field.ULift

set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

@[expose] public section

/- BEGIN EXACT BODY: FourPapers.Sublattice.CharacteristicBettiPolynomial -/
section

/-!
# The nonnegative polynomial characteristic excess

The coefficients are differences of genuine coefficient-quotient Betti
numbers. Integer-matrix specialization proves that these differences are
nonnegative before natural subtraction is used to record them.
-/

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 200000
noncomputable section
namespace FourPapers.Sublattice
open Classical CommAlg.Polymatroid
open FourPapers.MultichainCounting
universe u
variable {d : ℕ} {n : Fin d → ℕ} {E : Finset (FiniteTuple n)}
variable (Q K : Type u) [Field Q] [CharZero Q] [Field K]

theorem ordinaryQuotientBetti_charZero_le
    (B : Family (FiniteVariable.{u} n)) (q p : ℕ) :
    ordinaryQuotientBettiNumber (k := Q) B q p ≤
      ordinaryQuotientBettiNumber (k := K) B q p := by
  rw [ordinaryQuotientBettiNumber_eq_sum, ordinaryQuotientBettiNumber_eq_sum]
  exact Finset.sum_le_sum (fun a _ => quotientBettiNumber_charZero_le Q K B a.val p)

def strictSupportCharacteristicExcess (q p : ℕ) (s : StrictSupport E) : ℕ :=
  strictSupportBettiCoefficient (k := K) q p s -
    strictSupportBettiCoefficient (k := Q) q p s

theorem strictSupportCharacteristicExcess_cast (q p : ℕ) (s : StrictSupport E) :
    (strictSupportCharacteristicExcess Q K q p s : ℤ) =
      (strictSupportBettiCoefficient (k := K) q p s : ℤ) -
        (strictSupportBettiCoefficient (k := Q) q p s : ℤ) := by
  exact Nat.cast_sub (ordinaryQuotientBetti_charZero_le Q K _ q p)

/-- The actual integer difference of the normalized ordinary Betti entries. -/
def characteristicBettiExcess (q p t : ℕ) : ℤ :=
  (normalizedBettiSequence (k := K) (E := E) q p t : ℤ) -
    (normalizedBettiSequence (k := Q) (E := E) q p t : ℤ)

/-- The positive binomial expansion in Corollary 10.4, indexed before
collecting equal support sizes. The expansion is valid at every power. -/
theorem corollary104_excessExpansion (hE : finiteLatticeClosed n E) (q p t : ℕ) :
    characteristicBettiExcess Q K (E := E) q p t =
      (PositiveBinomialPolynomial.sequence
        (strictSupportCharacteristicExcess Q K (E := E) q p) (fun s => s.val.card-1) t : ℤ) := by
  rw [characteristicBettiExcess, normalizedBettiSequence_eq hE,
    normalizedBettiSequence_eq hE]
  simp only [PositiveBinomialPolynomial.sequence, Nat.cast_sum, Nat.cast_mul]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro s _
  rw [strictSupportCharacteristicExcess_cast]
  ring

theorem corollary104_excess_nonnegative (hE : finiteLatticeClosed n E) (q p t : ℕ) :
    0 ≤ characteristicBettiExcess Q K (E := E) q p t := by
  rw [corollary104_excessExpansion Q K hE]
  exact Int.natCast_nonneg _

/-- No truncation occurs in these differences: they are iterates of the
integer-valued forward-difference operator. -/
theorem corollary104_forward_differences (hE : finiteLatticeClosed n E) (q p j t : ℕ) :
    0 ≤ ((fwdDiff (1 : ℕ))^[j]
      (characteristicBettiExcess Q K (E := E) q p)) t := by
  have he : characteristicBettiExcess Q K (E := E) q p =
      fun t => (PositiveBinomialPolynomial.sequence
        (strictSupportCharacteristicExcess Q K (E := E) q p) (fun s => s.val.card-1) t : ℤ) :=
    funext (corollary104_excessExpansion Q K hE q p)
  rw [he]
  exact PositiveBinomialPolynomial.sequence_forward_differences_nonnegative _ _ j t

end FourPapers.Sublattice
end

#print axioms FourPapers.Sublattice.corollary104_excessExpansion
#print axioms FourPapers.Sublattice.corollary104_forward_differences

end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.CharacteristicCrossingBlocks -/
section

/-! # Characteristic independence through the crossing-block decomposition

The tensor factors are the actual predecessor quotient complexes, with their
original fine degrees. The signed tensor dimension formula is applied only
after proving the differential and parity identities for these complexes.
Uncovered degrees are handled by the explicit contracting homotopy.
-/

section
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 900000
noncomputable section
namespace FourPapers.Sublattice
open Classical CommAlg CommAlg.Koszul CommAlg.Polymatroid FilteredHomology
open scoped TensorProduct
universe u

section TotalDimension
variable {V k : Type u} [Fintype V] [LinearOrder V] [Field k]

lemma quotientTotalHomology_finrank_zero_of_contracting (B : Family V) (α : Exponent V)
    (H : Module.End k (TotalFaceModule (k := k) (quotientKoszulFaces B α)))
    (hH : quotientTotalDifferential B α * H + H * quotientTotalDifferential B α = 1) :
    Module.finrank k (QuotientTotalHomology (k := k) B α) = 0 := by
  let D := quotientTotalDifferential (k := k) B α
  let hDD := quotientTotalDifferential_comp (k := k) B α
  have hsur : Function.Surjective (boundaryMap D D hDD) := by
    intro x
    refine ⟨H x.val, Subtype.ext ?_⟩
    have he := LinearMap.congr_fun hH x.val
    change D (H x.val) + H (D x.val) = x.val at he
    change D (H x.val) = x.val
    simpa only [show D x.val = 0 from x.property, map_zero, add_zero] using he
  have htop : LinearMap.range (boundaryMap D D hDD) = ⊤ := LinearMap.range_eq_top.mpr hsur
  letI : Subsingleton (QuotientTotalHomology (k := k) B α) :=
    (Submodule.Quotient.subsingleton_iff).mpr htop
  exact Module.finrank_zero_of_subsingleton

end TotalDimension
section CrossingDimension
variable {k : Type u} [Field k]
  {d : ℕ} {n : Fin d → ℕ} {E : Finset (FiniteTuple n)} {m : ℕ}

/-- The Künneth dimension identity for the literal coefficient strand. -/
theorem crossingCoefficient_totalHomology_finrank (hE : finiteLatticeClosed n E)
    (w : FiniteMultichain n E m) (v : Exponent (FiniteVariable.{u} n))
    (hv : CrossingCovered w v) :
    Module.finrank k (QuotientTotalHomology (k := k) (finiteChainCoefficientFamily n w) v) =
      ∏ i : Fin m, Module.finrank k
        (QuotientTotalHomology (k := k) (finitePredecessorFamily n E (w.val i).val)
          (finiteBlockDegree w i v)) := by
  let P := crossingBlockFaces w v
  let D := fun i => projectedTotalDifferential (k := k) (P i)
  let S := fun i => totalFaceInvolute (k := k) (P i)
  have hdd (i : Fin m) : D i * D i = 0 := by
    change projectedTotalDifferential (quotientKoszulFaces _ _) *
      projectedTotalDifferential (quotientKoszulFaces _ _) = 0
    rw [← quotientTotalDifferential_eq_projected]
    exact quotientTotalDifferential_comp _ _
  have hds (i : Fin m) : D i * S i = -(S i * D i) :=
    projectedTotalDifferential_anticommute (P i)
  have hs (i : Fin m) : S i * S i = 1 := totalFaceInvolute_square (P i)
  have hchar (i : Fin m) (h2 : (2 : k) = 0) : S i = 1 :=
    totalFaceInvolute_eq_one_of_two_eq_zero (P i) h2
  letI (i : Fin m) : Module.Finite k (TotalFaceModule (k := k) (P i)) :=
    Module.Finite.of_basis (totalFaceBasis (P i))
  let T := TensorCycleSpanning.differential D S
  have hTT : T.comp T = 0 := TensorCycleSpanning.differential_square_zero D S hdd hds
  let e := crossingBlockTensorEquiv (k := k) hE w v hv
  let whole := quotientTotalDifferential (k := k) (finiteChainCoefficientFamily n w) v
  have he (x) : e (T x) = whole (e x) :=
    (LinearMap.congr_fun (crossingBlockTensorEquiv_is_chain (k := k) hE w v hv) x).symm
  let eh := threeTermHomologyEquiv T T hTT whole whole
    (quotientTotalDifferential_comp (finiteChainCoefficientFamily n w) v) e e e he he
  calc
    _ = Module.finrank k (Homology T T hTT) := eh.finrank_eq.symm
    _ = ∏ i, Module.finrank k (Homology (D i) (D i) (hdd i)) :=
      finrank_signedTensorHomology D S hdd hs hds hchar
    _ = _ := by
      apply Finset.prod_congr rfl
      intro i _
      let QD := quotientTotalDifferential (k := k)
        (finitePredecessorFamily n E (w.val i).val) (finiteBlockDegree w i v)
      have hDi : D i = QD :=
        (quotientTotalDifferential_eq_projected (k := k) _ _).symm
      let ei := LinearEquiv.refl k (TotalFaceModule (k := k) (P i))
      have hi (x) : ei (D i x) = QD (ei x) := LinearMap.congr_fun hDi x
      exact (threeTermHomologyEquiv (D i) (D i) (hdd i) QD QD
        (quotientTotalDifferential_comp (k := k) _ _) ei ei ei hi hi).finrank_eq

lemma uncoveredCoefficient_totalHomology_finrank_zero (hE : finiteLatticeClosed n E)
    (w : FiniteMultichain n E m) (v : Exponent (FiniteVariable.{u} n))
    (hv : ¬CrossingCovered w v) :
    Module.finrank k (QuotientTotalHomology (k := k) (finiteChainCoefficientFamily n w) v) = 0 := by
  change ¬(∀ x, v x ≠ 0 → ∃ i, finiteCrosses w i x) at hv
  obtain ⟨x, hx⟩ := not_forall.mp hv
  have hxpos : 0 < v x := Nat.pos_of_ne_zero (not_imp.mp hx).1
  have hnone : ∀ i, ¬finiteCrosses w i x := not_exists.mp (not_imp.mp hx).2
  obtain ⟨H, hH, _⟩ := uncoveredCrossingBlock_contractible (k := k) hE w v x hxpos hnone
  exact quotientTotalHomology_finrank_zero_of_contracting _ _ H hH

end CrossingDimension
section Compare
variable (Q K : Type u) [Field Q] [CharZero Q] [Field K]
  {d : ℕ} {n : Fin d → ℕ} {E : Finset (FiniteTuple n)}

/-- Every predecessor table controls every coefficient quotient, with all fine
and homological degrees retained. -/
theorem chainCoefficient_betti_eq_of_predecessor_eq (hE : finiteLatticeClosed n E)
    (hpre : ∀ a : E, ∀ b p,
      quotientBettiNumber (k := Q) (finitePredecessorFamily n E a.val) b p =
        quotientBettiNumber (k := K) (finitePredecessorFamily n E a.val) b p)
    {m : ℕ} (w : FiniteMultichain n E m) (v : Exponent (FiniteVariable.{u} n)) (p : ℕ) :
    quotientBettiNumber (k := Q) (finiteChainCoefficientFamily n w) v p =
      quotientBettiNumber (k := K) (finiteChainCoefficientFamily n w) v p := by
  apply quotientBetti_eq_of_totalHomology_finrank_eq _ _
    (fun j => quotientBettiNumber_charZero_le Q K _ _ j) _ p
  by_cases hv : CrossingCovered w v
  · rw [crossingCoefficient_totalHomology_finrank hE w v hv,
      crossingCoefficient_totalHomology_finrank hE w v hv]
    apply Finset.prod_congr rfl
    intro i _
    exact quotientTotalHomology_finrank_eq_of_betti_eq _ _ (hpre (w.val i) _)
  · rw [uncoveredCoefficient_totalHomology_finrank_zero hE w v hv,
      uncoveredCoefficient_totalHomology_finrank_zero hE w v hv]

/-- The converse characteristic-independence implication in Corollary 10.4. -/
theorem all_power_betti_eq_of_predecessor_eq (hE : finiteLatticeClosed n E)
    (hpre : ∀ a : E, ∀ b p,
      quotientBettiNumber (k := Q) (finitePredecessorFamily n E a.val) b p =
        quotientBettiNumber (k := K) (finitePredecessorFamily n E a.val) b p)
    (m : ℕ) (hm : 0 < m) (a : Exponent (FiniteVariable.{u} n)) (p : ℕ) :
    bettiNumber (k := Q) (exponentPowerFamily (finiteRowFamily n E) m) a p =
      bettiNumber (k := K) (exponentPowerFamily (finiteRowFamily n E) m) a p := by
  rw [allPowerBetti_admissible hE m hm p a, allPowerBetti_admissible hE m hm p a]
  exact Finset.sum_congr rfl (fun w _ =>
    chainCoefficient_betti_eq_of_predecessor_eq Q K hE hpre w.val _ p)

/-- The ordinary version follows by the actual fine-to-ordinary Tor decomposition. -/
theorem all_power_ordinary_betti_eq_of_predecessor_eq (hE : finiteLatticeClosed n E)
    (hpre : ∀ a : E, ∀ b p,
      quotientBettiNumber (k := Q) (finitePredecessorFamily n E a.val) b p =
        quotientBettiNumber (k := K) (finitePredecessorFamily n E a.val) b p)
    (m : ℕ) (hm : 0 < m) (q p : ℕ) :
    ordinaryMonomialBettiNumber (k := Q) (exponentPowerFamily (finiteRowFamily n E) m) q p =
      ordinaryMonomialBettiNumber (k := K) (exponentPowerFamily (finiteRowFamily n E) m) q p := by
  rw [ordinaryMonomialBettiNumber_eq_sum, ordinaryMonomialBettiNumber_eq_sum]
  exact Finset.sum_congr rfl (fun a _ => all_power_betti_eq_of_predecessor_eq Q K hE hpre m hm a.val p)

/-- Equality in one specified positive power is equivalent to equality in all
powers and to equality of every predecessor table. -/
theorem corollary104_one_power_iff_predecessors (hE : finiteLatticeClosed n E)
    (m : ℕ) (hm : 0 < m) :
    (∀ q p, ordinaryMonomialBettiNumber (k := Q)
        (exponentPowerFamily (finiteRowFamily n E) m) q p =
      ordinaryMonomialBettiNumber (k := K)
        (exponentPowerFamily (finiteRowFamily n E) m) q p) ↔
    (∀ a : E, ∀ b p, quotientBettiNumber (k := Q) (finitePredecessorFamily n E a.val) b p =
      quotientBettiNumber (k := K) (finitePredecessorFamily n E a.val) b p) :=
  ⟨fun h => predecessor_betti_eq_of_one_power_eq Q K hE m hm h,
    fun h => all_power_ordinary_betti_eq_of_predecessor_eq Q K hE h m hm⟩

/-- For each pair of fields, equality at one positive power is equivalent
 to equality at every positive power. Universally quantifying K gives the
 characteristic-independence assertion of Corollary 10.4. -/
theorem corollary104_one_power_iff_all_powers (hE : finiteLatticeClosed n E)
    (m : ℕ) (hm : 0 < m) :
    (∀ q p, ordinaryMonomialBettiNumber (k := Q)
        (exponentPowerFamily (finiteRowFamily n E) m) q p =
      ordinaryMonomialBettiNumber (k := K)
        (exponentPowerFamily (finiteRowFamily n E) m) q p) ↔
    (∀ r : ℕ, 0 < r → ∀ q p, ordinaryMonomialBettiNumber (k := Q)
        (exponentPowerFamily (finiteRowFamily n E) r) q p =
      ordinaryMonomialBettiNumber (k := K)
        (exponentPowerFamily (finiteRowFamily n E) r) q p) := by
  constructor
  · intro h r hr
    exact all_power_ordinary_betti_eq_of_predecessor_eq Q K hE
      ((corollary104_one_power_iff_predecessors Q K hE m hm).mp h) r hr
  · intro h
    exact h m hm

end Compare
end FourPapers.Sublattice

#print axioms FourPapers.Sublattice.crossingCoefficient_totalHomology_finrank
#print axioms FourPapers.Sublattice.corollary104_one_power_iff_predecessors

end
end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.IntegerCharacteristicBettiPolynomial -/
section

/-! # Characteristic excess in every integer normalized degree

This is the integer-degree form of Corollary 10.4. The difference is an
ordinary integer difference of dimensions of actual Tor submodules. Its
coefficients are proved nonnegative before natural subtraction is used to
record them. Any characteristic-zero field and any comparison field are
allowed, in particular Q and every prime field F_p.
-/

section
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 500000
noncomputable section
namespace FourPapers.Sublattice
open Classical CommAlg CommAlg.Polymatroid FourPapers.MultichainCounting
universe u
variable {d : ℕ} {n : Fin d → ℕ} {E : Finset (FiniteTuple n)}
  (Q K : Type u) [Field Q] [CharZero Q] [Field K]

lemma integerOrdinaryQuotientBetti_charZero_le (B : Family (FiniteVariable.{u} n))
    (q : ℤ) (p : ℕ) :
    integerOrdinaryQuotientBettiNumber (K := Q) B q p ≤
      integerOrdinaryQuotientBettiNumber (K := K) B q p := by
  by_cases hq : 0 ≤ q
  · obtain ⟨a, rfl⟩ := Int.eq_ofNat_of_zero_le hq
    simpa only [integerOrdinaryQuotientBettiNumber_nat] using
      ordinaryQuotientBetti_charZero_le Q K B a p
  · rw [integerOrdinaryQuotientBettiNumber_negative B q (lt_of_not_ge hq) p,
      integerOrdinaryQuotientBettiNumber_negative B q (lt_of_not_ge hq) p]

def integerStrictSupportCharacteristicExcess (q : ℤ) (p : ℕ) (s : StrictSupport E) : ℕ :=
  integerStrictSupportBettiCoefficient (K := K) q p s -
    integerStrictSupportBettiCoefficient (K := Q) q p s

lemma integerStrictSupportCharacteristicExcess_cast (q : ℤ) (p : ℕ) (s : StrictSupport E) :
    (integerStrictSupportCharacteristicExcess Q K q p s : ℤ) =
      (integerStrictSupportBettiCoefficient (K := K) q p s : ℤ) -
        (integerStrictSupportBettiCoefficient (K := Q) q p s : ℤ) :=
  Nat.cast_sub (integerOrdinaryQuotientBetti_charZero_le Q K _ q p)

variable (o : MonomialOrder (FiniteVariable.{u} n))

def integerCharacteristicBettiExcess (q : ℤ) (p t : ℕ) : ℤ :=
  (integerNormalizedBettiSequence (K := K) o (E := E) q p t : ℤ) -
    (integerNormalizedBettiSequence (K := Q) o (E := E) q p t : ℤ)

/-- The positive binomial expansion, valid for every integer normalized
internal degree and every positive power (indexed as t+1). -/
theorem corollary104_integer_excessExpansion (hE : finiteLatticeClosed n E)
    (q : ℤ) (p t : ℕ) : integerCharacteristicBettiExcess Q K o (E := E) q p t =
      (PositiveBinomialPolynomial.sequence
        (integerStrictSupportCharacteristicExcess Q K (E := E) q p)
        (fun s => s.val.card-1) t : ℤ) := by
  rw [integerCharacteristicBettiExcess, integerNormalizedBettiSequence_eq o hE,
    integerNormalizedBettiSequence_eq o hE]
  simp only [PositiveBinomialPolynomial.sequence, Nat.cast_sum, Nat.cast_mul]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro s _
  rw [integerStrictSupportCharacteristicExcess_cast]
  ring

theorem corollary104_integer_forward_differences (hE : finiteLatticeClosed n E)
    (q : ℤ) (p j t : ℕ) :
    0 ≤ ((fwdDiff (1 : ℕ))^[j]
      (integerCharacteristicBettiExcess Q K o (E := E) q p)) t := by
  have he : integerCharacteristicBettiExcess Q K o (E := E) q p =
      fun t => (PositiveBinomialPolynomial.sequence
        (integerStrictSupportCharacteristicExcess Q K (E := E) q p)
        (fun s => s.val.card-1) t : ℤ) :=
    funext (corollary104_integer_excessExpansion Q K o hE q p)
  rw [he]
  exact PositiveBinomialPolynomial.sequence_forward_differences_nonnegative _ _ j t

/-- The same characteristic-independence equivalence includes all integer
absolute internal degrees of the actual ideal Tor. -/
theorem corollary104_integer_one_power_iff_all_powers (hE : finiteLatticeClosed n E)
    (m : ℕ) (hm : 0 < m) :
    (∀ q : ℤ, ∀ p, integerMonomialTorBettiNumber (K := Q) o
        (exponentPowerFamily (finiteRowFamily n E) m) p q =
      integerMonomialTorBettiNumber (K := K) o
        (exponentPowerFamily (finiteRowFamily n E) m) p q) ↔
    (∀ r : ℕ, 0 < r → ∀ q : ℤ, ∀ p, integerMonomialTorBettiNumber (K := Q) o
        (exponentPowerFamily (finiteRowFamily n E) r) p q =
      integerMonomialTorBettiNumber (K := K) o
        (exponentPowerFamily (finiteRowFamily n E) r) p q) := by
  constructor
  · intro h r hr q p
    by_cases hq : 0 ≤ q
    · obtain ⟨a, rfl⟩ := Int.eq_ofNat_of_zero_le hq
      rw [integerMonomialTorBettiNumber_nat, integerMonomialTorBettiNumber_nat]
      apply (corollary104_one_power_iff_all_powers Q K hE m hm).mp _ r hr a p
      intro b j
      simpa only [integerMonomialTorBettiNumber_nat] using h (b : ℤ) j
    · rw [integerMonomialTorBettiNumber_negative o _ p q (lt_of_not_ge hq),
        integerMonomialTorBettiNumber_negative o _ p q (lt_of_not_ge hq)]
  · intro h
    exact h m hm

end FourPapers.Sublattice

#print axioms FourPapers.Sublattice.corollary104_integer_excessExpansion
#print axioms FourPapers.Sublattice.corollary104_integer_forward_differences
#print axioms FourPapers.Sublattice.corollary104_integer_one_power_iff_all_powers

end
end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.CharacteristicGroupedCoefficients -/
section

/-!
# The printed coefficients in Corollary 10.4

The coefficient indexed by r is the sum of the actual characteristic
excesses over strict supports of cardinality r. The finite regrouping
identifies the earlier support-indexed formula with the printed binomial
expansion. All integer internal degrees and all positive powers remain.
-/

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 300000
noncomputable section

namespace FourPapers.Sublattice

open Classical CommAlg CommAlg.Polymatroid FourPapers.MultichainCounting

universe u
variable {d : ℕ} {n : Fin d → ℕ} {E : Finset (FiniteTuple n)}
  (Q K : Type u) [Field Q] [CharZero Q] [Field K]

private theorem strictSupport_card_bounds (s : StrictSupport E) :
    1 ≤ s.val.card ∧ s.val.card ≤ E.card := by
  refine ⟨Finset.card_pos.mpr s.property.1, ?_⟩
  simpa only [Fintype.card_coe] using Finset.card_le_univ s.val

/-- The paper's A_{p,q,char(K),r}: sum over every strict support of length r.
The summands are natural differences only after their nonnegativity has
been proved over a characteristic-zero field. -/
def integerCharacteristicCoefficient (q : ℤ) (p r : ℕ) : ℕ :=
  ∑ s ∈ Finset.univ.filter (fun s : StrictSupport E => s.val.card = r),
    integerStrictSupportCharacteristicExcess Q K q p s

/-- The coefficient is the genuine integer sum of the Betti differences;
there is no loss caused by natural-number subtraction. -/
theorem integerCharacteristicCoefficient_cast (q : ℤ) (p r : ℕ) :
    (integerCharacteristicCoefficient Q K (E := E) q p r : ℤ) =
      ∑ s ∈ Finset.univ.filter (fun s : StrictSupport E => s.val.card = r),
        ((integerStrictSupportBettiCoefficient (K := K) q p s : ℤ) -
          (integerStrictSupportBettiCoefficient (K := Q) q p s : ℤ)) := by
  rw [integerCharacteristicCoefficient, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro s _
  exact integerStrictSupportCharacteristicExcess_cast Q K q p s

/-- Nonnegativity applies to the actual integer difference, not a truncated
record of it. -/
theorem integerCharacteristicCoefficient_nonnegative (q : ℤ) (p r : ℕ) :
    0 ≤ ∑ s ∈ Finset.univ.filter (fun s : StrictSupport E => s.val.card = r),
      ((integerStrictSupportBettiCoefficient (K := K) q p s : ℤ) -
        (integerStrictSupportBettiCoefficient (K := Q) q p s : ℤ)) := by
  rw [← integerCharacteristicCoefficient_cast Q K q p r]
  exact Int.natCast_nonneg _

/-- Coefficients outside the positive finite interval are zero. Thus the
finite sum below represents the paper's sum over every r ≥ 1. -/
theorem integerCharacteristicCoefficient_eq_zero_of_not_mem
    (q : ℤ) (p r : ℕ) (hr : r ∉ Finset.Icc 1 E.card) :
    integerCharacteristicCoefficient Q K (E := E) q p r = 0 := by
  unfold integerCharacteristicCoefficient
  apply Finset.sum_eq_zero
  intro s hs
  have he : s.val.card = r := (Finset.mem_filter.mp hs).2
  have hmem : s.val.card ∈ Finset.Icc 1 E.card :=
    Finset.mem_Icc.mpr (strictSupport_card_bounds s)
  exact (hr (he ▸ hmem)).elim

/-- The checked finite regrouping of the support-indexed positive sequence. -/
theorem integerCharacteristic_sequence_grouped (q : ℤ) (p t : ℕ) :
    PositiveBinomialPolynomial.sequence
      (integerStrictSupportCharacteristicExcess Q K (E := E) q p)
      (fun s => s.val.card - 1) t =
    ∑ r ∈ Finset.Icc 1 E.card,
      integerCharacteristicCoefficient Q K (E := E) q p r * t.choose (r-1) := by
  exact FinitePositiveGrouping.sum_grouped_by_positive_label
    (integerStrictSupportCharacteristicExcess Q K (E := E) q p)
    (fun s => s.val.card) E.card strictSupport_card_bounds
    (fun r => t.choose (r-1))

/-- **Corollary 10.4 in its printed coefficient grouping.** The two Betti
numbers are dimensions of actual integer-graded derived Tor components.
Each coefficient is exactly the sum over strict supports of length r;
it is nonnegative and is zero outside 1 ≤ r ≤ |E|. -/
theorem corollary104_integer_grouped_expansion
    (o : MonomialOrder (FiniteVariable.{u} n)) (hE : finiteLatticeClosed n E)
    (q : ℤ) (p m : ℕ) (hm : 0 < m) :
    ((integerMonomialTorBettiNumber (K := K) o
        (exponentPowerFamily (finiteRowFamily n E) m) p ((m*d : ℕ)+q) : ℤ) -
      (integerMonomialTorBettiNumber (K := Q) o
        (exponentPowerFamily (finiteRowFamily n E) m) p ((m*d : ℕ)+q) : ℤ)) =
      ∑ r ∈ Finset.Icc 1 E.card,
        (integerCharacteristicCoefficient Q K (E := E) q p r : ℤ) *
          ((m-1).choose (r-1) : ℤ) := by
  have h := corollary104_integer_excessExpansion Q K o hE q p (m-1)
  simp only [integerCharacteristicBettiExcess, integerNormalizedBettiSequence,
    Nat.sub_add_cancel (by omega : 1 ≤ m)] at h
  rw [h, integerCharacteristic_sequence_grouped]
  simp only [Nat.cast_sum, Nat.cast_mul]

/-- Field independence of the entire actual integer-graded Betti table of
one fixed power. Both fields and their field structures are quantified. -/
def IntegerPowerBettiFieldIndependent
    (o : MonomialOrder (FiniteVariable.{u} n)) (m : ℕ) : Prop :=
  ∀ (F L : Type u) [Field F] [Field L] (q : ℤ) (p : ℕ),
    integerMonomialTorBettiNumber (K := F) o
      (exponentPowerFamily (finiteRowFamily n E) m) p q =
    integerMonomialTorBettiNumber (K := L) o
      (exponentPowerFamily (finiteRowFamily n E) m) p q

/-- **Corollary 10.4, independence over all fields.** Independence for any
fixed positive power is equivalent to independence for every positive power.
The proof compares each field with the rational field in the same universe,
then composes the two actual Betti equalities. -/
theorem corollary104_integer_global_one_power_iff_all_powers
    (o : MonomialOrder (FiniteVariable.{u} n)) (hE : finiteLatticeClosed n E)
    (m : ℕ) (hm : 0 < m) :
    IntegerPowerBettiFieldIndependent (E := E) o m ↔
      ∀ r : ℕ, 0 < r → IntegerPowerBettiFieldIndependent (E := E) o r := by
  constructor
  · intro h r hr F L instF instL q p
    letI : CharZero (ULift.{u} ℚ) :=
      { cast_injective := by
          intro a b hab
          have he : (a : ℚ) = (b : ℚ) := congrArg ULift.down hab
          exact Nat.cast_injective he }
    have hF : ∀ a : ℤ, ∀ j,
        integerMonomialTorBettiNumber (K := ULift.{u} ℚ) o
          (exponentPowerFamily (finiteRowFamily n E) m) j a =
        integerMonomialTorBettiNumber (K := F) o
          (exponentPowerFamily (finiteRowFamily n E) m) j a :=
      fun a j => h (ULift.{u} ℚ) F a j
    have hL : ∀ a : ℤ, ∀ j,
        integerMonomialTorBettiNumber (K := ULift.{u} ℚ) o
          (exponentPowerFamily (finiteRowFamily n E) m) j a =
        integerMonomialTorBettiNumber (K := L) o
          (exponentPowerFamily (finiteRowFamily n E) m) j a :=
      fun a j => h (ULift.{u} ℚ) L a j
    have heF := (corollary104_integer_one_power_iff_all_powers
      (ULift.{u} ℚ) F o hE m hm).mp hF r hr q p
    have heL := (corollary104_integer_one_power_iff_all_powers
      (ULift.{u} ℚ) L o hE m hm).mp hL r hr q p
    exact heF.symm.trans heL
  · intro h
    exact h m hm

/-- The existential formulation in the paper: some positive power has a
field-independent table exactly when every positive power does. -/
theorem corollary104_integer_global_exists_iff_all_powers
    (o : MonomialOrder (FiniteVariable.{u} n)) (hE : finiteLatticeClosed n E) :
    (∃ m : ℕ, 0 < m ∧ IntegerPowerBettiFieldIndependent (E := E) o m) ↔
      ∀ r : ℕ, 0 < r → IntegerPowerBettiFieldIndependent (E := E) o r := by
  constructor
  · rintro ⟨m, hm, h⟩
    exact (corollary104_integer_global_one_power_iff_all_powers o hE m hm).mp h
  · intro h
    exact ⟨1, Nat.zero_lt_one, h 1 Nat.zero_lt_one⟩

end FourPapers.Sublattice

end
end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.IntegerFirstStrandOccurrence -/
section

/-! # First occurrence stated in the actual integer-graded Tor groups

The support formulation is converted explicitly back to the displayed
Betti numbers in Corollary 5.3. The conversion retains every integer
normalized degree, including the vanishing negative cases.
-/

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 400000
noncomputable section
namespace FourPapers.Sublattice
open Classical CommAlg CommAlg.Polymatroid MvPolynomial
attribute [local instance] MvPolynomial.weightedGradedAlgebra
universe u
variable {K : Type u} [Field K] {d : ℕ} {n : Fin d → ℕ}
  {E : Finset (FiniteTuple n)} (o : MonomialOrder (FiniteVariable.{u} n))

/-- The first assertion of Corollary 5.3, in the paper's displayed notation. -/
theorem corollary53_integer_first_occurrence (hE : finiteLatticeClosed n E)
    (m : ℕ) (hm : 0 < m) (p : ℕ) (hp : 0 < p) (q : ℤ)
    (h : integerMonomialTorBettiNumber (K := K) o
      (exponentPowerFamily (finiteRowFamily n E) m) p ((m*d : ℕ)+q) ≠ 0) :
    ∃ r : ℕ, 0 < r ∧ r ≤ p ∧
      integerMonomialTorBettiNumber (K := K) o
        (exponentPowerFamily (finiteRowFamily n E) r) p ((r*d : ℕ)+q) ≠ 0 := by
  have hnonneg : 0 ≤ ((m*d : ℕ) : ℤ)+q := by
    by_contra hh
    exact h (integerMonomialTorBettiNumber_negative o _ p _ (lt_of_not_ge hh))
  obtain ⟨Q,hQ⟩ := Int.eq_ofNat_of_zero_le hnonneg
  rw [hQ,integerMonomialTorBettiNumber_nat] at h
  have hs : (p,q) ∈ normalizedBettiSupport (k := K) (n := n) (E := E) m := by
    refine ⟨Q,h,?_⟩
    push_cast at hQ
    nlinarith
  obtain ⟨r,hr,hrp,hsr⟩ := corollary53_first_occurrence hE m hm p hp q hs
  obtain ⟨Qr,hQr,hqr⟩ := hsr
  refine ⟨r,hr,hrp,?_⟩
  have he : ((r*d : ℕ) : ℤ)+q = (Qr : ℤ) := by
    push_cast
    nlinarith
  rw [he,integerMonomialTorBettiNumber_nat]
  exact hQr

/-- The same first-occurrence conclusion follows for every deformation
covered by the paper's first-power Betti criterion. -/
theorem corollary53_integer_first_occurrence_transfer
    (J : Ideal (MvPolynomial (FiniteVariable.{u} n) K)) (hE : finiteLatticeClosed n E)
    (hinit : FourPapers.initialIdeal o J = finiteSublatticeIdeal n (k := K) E)
    (hJ : J.IsHomogeneous (weightedHomogeneousSubmodule K
      (fun _ : FiniteVariable.{u} n => (1 : ℕ))))
    (hβ : ∀ p q, sublatticePowerBettiNumber n o J E hE hinit hJ 1 p q =
      sublatticeMonomialPowerBettiNumber (K := K) n E 1 p q)
    (m : ℕ) (hm : 0 < m) (p : ℕ) (hp : 0 < p) (q : ℤ)
    (h : sublatticeIntegerPowerBettiNumber n o J E hE hinit hJ m p ((m*d : ℕ)+q) ≠ 0) :
    ∃ r : ℕ, 0 < r ∧ r ≤ p ∧
      sublatticeIntegerPowerBettiNumber n o J E hE hinit hJ r p ((r*d : ℕ)+q) ≠ 0 := by
  rw [theorem43_integer_betti n o J E hE hinit hJ hβ] at h
  obtain ⟨r,hr,hrp,hrβ⟩ := corollary53_integer_first_occurrence o hE m hm p hp q h
  refine ⟨r,hr,hrp,?_⟩
  rwa [theorem43_integer_betti n o J E hE hinit hJ hβ]

end FourPapers.Sublattice

#print axioms FourPapers.Sublattice.corollary53_integer_first_occurrence
#print axioms FourPapers.Sublattice.corollary53_integer_first_occurrence_transfer

end
end
end


end
