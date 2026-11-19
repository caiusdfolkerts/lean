module
public import graph_results.closed_graph_characteristic
public import shared_results.part016

set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

@[expose] public section

/- BEGIN EXACT BODY: FourPapers.Sublattice.ClosedGraphAllPowersCharacteristic -/
section

/-! # Characteristic independence including the zeroth ideal power

The substantive positive-power comparison is proved in
`ClosedGraphCharacteristic`. Here the actual Koszul complex of the unit
ideal supplies the zeroth power, so the phrase “all powers” in Corollary
6.3 can be read literally as every natural exponent.
-/

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 20000
set_option synthInstance.maxHeartbeats 5000
noncomputable section

namespace FourPapers.Sublattice
open Classical CategoryTheory CommAlg CommAlg.Koszul CommAlg.Polymatroid MvPolynomial
attribute [local instance] MvPolynomial.weightedGradedAlgebra
universe u v
variable {N : ℕ} (K L : Type u) [Field K] [Field L]

private theorem closedGraph_zero_power_fine_field_independent
    (G : SimpleGraph (Fin N)) (hG : ClosedLabeling G)
    (α : Exponent (FiniteVariable.{u} (GraphRows N))) (p : ℕ) :
    bettiNumber (k := K) (graphMonomialPowerFamily G 0) α p =
      bettiNumber (k := L) (graphMonomialPowerFamily G 0) α p := by
  let G' := graphComponentRelabeled G
  let w : FiniteMultichain (GraphRows N) (graphEdgeLattice G') 0 :=
    ⟨Fin.elim0, by intro i; exact Fin.elim0 i⟩
  have hc := unitInterval_coefficient_betti_field_independent K L
    (graphEdgeLattice_unitInterval G' (graphComponentRelabeled_interval G hG)) w α p
  have hw : finiteChainCoefficientFamily.{u} (GraphRows N) w = ∅ := by
    simp [finiteChainCoefficientFamily]
  rw [hw] at hc
  have comparison (F : Type u) [Field F] :
      bettiNumber (k := F) ({0} : Family (FiniteVariable.{u} (GraphRows N))) α p =
        quotientBettiNumber (k := F) ∅ α p := by
    unfold bettiNumber
    rw [← (gradedTorIso (k := F) ({0} : Family (FiniteVariable.{u} (GraphRows N)))
      α p).toLinearEquiv.finrank_eq, quotientBettiNumber_eq_homology]
    exact ((HomologicalComplex.homologyFunctor (ModuleCat F) (ComplexShape.down ℕ) p).mapIso
      (emptyPowerHomogeneousIso (k := F) α)).toLinearEquiv.finrank_eq
  change bettiNumber (k := K) ({0} : Family (FiniteVariable.{u} (GraphRows N))) α p =
    bettiNumber (k := L) ({0} : Family (FiniteVariable.{u} (GraphRows N))) α p
  exact (comparison K).trans (hc.trans (comparison L).symm)

variable {Γ : Type v} [AddCommMonoid Γ]

/-- Finite coarsening of the field-independent fine homology, including
the actual zeroth power of the original monomial ideal. -/
theorem closedGraph_weighted_monomial_field_independent_all
    (G : SimpleGraph (Fin N)) (hG : ClosedLabeling G)
    (ω : FiniteVariable.{u} (GraphRows N) → Γ) (ρ : Γ →+ ℤ)
    (hρ : ∀ x, ρ (ω x) = 1) (m p : ℕ) (γ : Γ) :
    graphWeightedMonomialBetti (K := K) G ω m p γ =
      graphWeightedMonomialBetti (K := L) G ω m p γ := by
  by_cases hm : 0 < m
  · exact closedGraph_weighted_monomial_field_independent K L G hG ω ρ hρ m hm p γ
  · have hm0 : m = 0 := Nat.eq_zero_of_not_pos hm
    subst m
    letI : Finite (FinerDegreeIndex ω γ) := finerDegreeIndex_finite ω ρ hρ γ
    letI : Fintype (FinerDegreeIndex ω γ) := Fintype.ofFinite _
    have hK := canonicalWeightedMonomialBettiNumber_eq (k := K)
      graphLexOrder (graphMonomialPowerFamily G 0) ω γ p
    have hL := canonicalWeightedMonomialBettiNumber_eq (k := L)
      graphLexOrder (graphMonomialPowerFamily G 0) ω γ p
    have hweight : weightedMonomialBettiNumber (k := K) (graphMonomialPowerFamily G 0) ω γ p =
        weightedMonomialBettiNumber (k := L) (graphMonomialPowerFamily G 0) ω γ p := by
      rw [weightedMonomialBettiNumber_eq_sum, weightedMonomialBettiNumber_eq_sum]
      apply Finset.sum_congr rfl
      intro α _
      exact closedGraph_zero_power_fine_field_independent K L G hG α.val p
    exact hK.trans (hweight.trans hL.symm)

/-- Corollary 6.3 in every integer exponent vector and every natural power. -/
theorem corollary63_monomial_integer_fine_all
    (G : SimpleGraph (Fin N)) (hG : ClosedLabeling G)
    (m p : ℕ) (γ : FiniteVariable.{u} (GraphRows N) →₀ ℤ) :
    graphWeightedMonomialBetti (K := K) G (fun x => Finsupp.single x (1 : ℤ)) m p γ =
      graphWeightedMonomialBetti (K := L) G (fun x => Finsupp.single x (1 : ℤ)) m p γ := by
  let ρ : (FiniteVariable.{u} (GraphRows N) →₀ ℤ) →+ ℤ :=
    Finsupp.weight (fun _ : FiniteVariable.{u} (GraphRows N) => (1 : ℤ))
  apply closedGraph_weighted_monomial_field_independent_all K L G hG
    (fun x => Finsupp.single x (1 : ℤ)) ρ ?_ m p γ
  intro x
  simp only [ρ, Finsupp.weight_single, one_smul]

/-- The natural binomial grading, with no restriction on the power. -/
theorem corollary63_binomial_natural_all
    (G : SimpleGraph (Fin N)) (hG : ClosedLabeling G)
    (m p : ℕ) (γ : GraphNaturalDegree N) :
    graphWeightedBinomialBetti G graphNaturalWeight
        (graphBinomialIdeal_natural_homogeneous (K := K) G) m p γ =
      graphWeightedBinomialBetti G graphNaturalWeight
        (graphBinomialIdeal_natural_homogeneous (K := L) G) m p γ := by
  rw [corollary62_natural G hG, corollary62_natural G hG]
  exact closedGraph_weighted_monomial_field_independent_all K L G hG graphNaturalWeight
    (graphNaturalRefinement N) graphNaturalRefinement_variable m p γ

/-- Separate row counts in each connected component, also in power zero. -/
theorem corollary63_binomial_component_rows_all
    (G : SimpleGraph (Fin N)) (hG : ClosedLabeling G)
    (m p : ℕ) (γ : GraphComponentDegree G) :
    graphWeightedBinomialBetti G (graphComponentWeight G)
        (graphBinomialIdeal_component_homogeneous (K := K) G) m p γ =
      graphWeightedBinomialBetti G (graphComponentWeight G)
        (graphBinomialIdeal_component_homogeneous (K := L) G) m p γ := by
  rw [corollary62_component_rows G hG, corollary62_component_rows G hG]
  exact closedGraph_weighted_monomial_field_independent_all K L G hG (graphComponentWeight G)
    (graphComponentRefinement G) (graphComponentRefinement_variable G) m p γ

private theorem closedGraph_ordinary_monomial_field_independent_all
    (G : SimpleGraph (Fin N)) (hG : ClosedLabeling G) (m p q : ℕ) :
    graphMonomialBetti (K := K) G m p q = graphMonomialBetti (K := L) G m p q := by
  have hK := canonicalMonomialBettiNumber_eq (K := K)
    graphLexOrder (graphMonomialPowerFamily G m)
    (monomialIdeal_ordinary_homogeneous (graphMonomialPowerFamily G m)) q p
  have hL := canonicalMonomialBettiNumber_eq (K := L)
    graphLexOrder (graphMonomialPowerFamily G m)
    (monomialIdeal_ordinary_homogeneous (graphMonomialPowerFamily G m)) q p
  have hord : ordinaryMonomialBettiNumber (k := K) (graphMonomialPowerFamily G m) q p =
      ordinaryMonomialBettiNumber (k := L) (graphMonomialPowerFamily G m) q p := by
    rw [ordinaryMonomialBettiNumber_eq_sum, ordinaryMonomialBettiNumber_eq_sum]
    apply Finset.sum_congr rfl
    intro α _
    by_cases hm : 0 < m
    · exact corollary63_monomial_fine K L G hG m hm p α.val
    · have hm0 : m = 0 := Nat.eq_zero_of_not_pos hm
      subst m
      exact closedGraph_zero_power_fine_field_independent K L G hG α.val p
  exact hK.trans (hord.trans hL.symm)

/-- Both ideal powers have field-independent ordinary Betti numbers in
every integer degree, for every natural exponent. -/
theorem corollary63_integer_ordinary_all
    (G : SimpleGraph (Fin N)) (hG : ClosedLabeling G) (m p : ℕ) (q : ℤ) :
    graphMonomialIntegerBetti (K := K) G m p q =
        graphMonomialIntegerBetti (K := L) G m p q ∧
    graphBinomialIntegerBetti (K := K) G m p q =
        graphBinomialIntegerBetti (K := L) G m p q := by
  have hmono : graphMonomialIntegerBetti (K := K) G m p q =
      graphMonomialIntegerBetti (K := L) G m p q := by
    by_cases hq : 0 ≤ q
    · have he : (q.toNat : ℤ) = q := Int.toNat_of_nonneg hq
      rw [← he, graphMonomialIntegerBetti_nat, graphMonomialIntegerBetti_nat]
      exact closedGraph_ordinary_monomial_field_independent_all K L G hG m p q.toNat
    · unfold graphMonomialIntegerBetti
      rw [ordinaryIntegerIdealBettiNumber_negative _ _ p q (lt_of_not_ge hq),
        ordinaryIntegerIdealBettiNumber_negative _ _ p q (lt_of_not_ge hq)]
  have hbin (F : Type u) [Field F] :
      graphBinomialIntegerBetti (K := F) G m p q =
        graphMonomialIntegerBetti (K := F) G m p q := by
    by_cases hm : 0 < m
    · exact theorem11_integer_bettiEquality G hG m hm p q
    · have hm0 : m = 0 := Nat.eq_zero_of_not_pos hm
      subst m
      have hP : graphMonomialPowerData (K := F) G 0 = graphBinomialPowerData (K := F) G 0 := by
        simp only [graphMonomialPowerData, graphMonomialPowerFamily, graphBinomialPowerData,
          finitePowerFamily_ideal, pow_zero]
      simp only [graphBinomialIntegerBetti, graphMonomialIntegerBetti, hP]
  exact ⟨hmono, (hbin K).trans (hmono.trans (hbin L).symm)⟩

end FourPapers.Sublattice

#print axioms FourPapers.Sublattice.closedGraph_weighted_monomial_field_independent_all

#print axioms FourPapers.Sublattice.corollary63_monomial_integer_fine_all

#print axioms FourPapers.Sublattice.corollary63_binomial_natural_all

#print axioms FourPapers.Sublattice.corollary63_binomial_component_rows_all

#print axioms FourPapers.Sublattice.corollary63_integer_ordinary_all

end
end
end


end
