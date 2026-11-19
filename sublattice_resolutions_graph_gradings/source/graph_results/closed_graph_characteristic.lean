module
public import graph_results.closed_graph_natural_grading
public import graph_results.closed_graph_integer_betti
public import graph_results.weighted_monomial_coarsening
public import shared_results.part009

set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

@[expose] public section

/- BEGIN EXACT BODY: FourPapers.Sublattice.ClosedGraphCharacteristic -/
section

/-!
# Corollary 6.3: characteristic independence in the original gradings

The monomial comparison starts in the finest exponent lattice. Finite
coarsening is an explicit direct-sum decomposition of the actual Koszul
homology. For an arbitrary closed labeling, the polynomial and exterior
renaming equivalences retain the original grading labels. The natural
binomial statement then follows through Corollary 6.2 over each field.
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
universe u v
variable {N : ℕ} {Γ : Type v} [AddCommMonoid Γ]


variable (K L : Type u) [Field K] [Field L]

/-- Finite coarsening of the integral fine-degree comparison. -/
theorem intervalGraph_weighted_betti_field_independent
    (G : SimpleGraph (Fin N)) (hG : IntervalLabeling G)
    (ω : FiniteVariable.{u} (GraphRows N) → Γ) (ρ : Γ →+ ℤ)
    (hρ : ∀ v, ρ (ω v) = 1) (m : ℕ) (hm : 0 < m) (p : ℕ) (γ : Γ) :
    graphWeightedMonomialBetti (K := K) G ω m p γ =
      graphWeightedMonomialBetti (K := L) G ω m p γ := by
  letI : Finite (FinerDegreeIndex ω γ) := finerDegreeIndex_finite ω ρ hρ γ
  letI : Fintype (FinerDegreeIndex ω γ) := Fintype.ofFinite _
  have hK := canonicalWeightedMonomialBettiNumber_eq (k := K)
    graphLexOrder (graphMonomialPowerFamily G m) ω γ p
  have hL := canonicalWeightedMonomialBettiNumber_eq (k := L)
    graphLexOrder (graphMonomialPowerFamily G m) ω γ p
  have hweight : weightedMonomialBettiNumber (k := K) (graphMonomialPowerFamily G m) ω γ p =
      weightedMonomialBettiNumber (k := L) (graphMonomialPowerFamily G m) ω γ p := by
    rw [weightedMonomialBettiNumber_eq_sum, weightedMonomialBettiNumber_eq_sum]
    apply Finset.sum_congr rfl
    intro α _
    exact unitInterval_power_betti_field_independent K L (graphEdgeLattice_unitInterval G hG)
      m hm α.val p
  exact hK.trans (hweight.trans hL.symm)

/-- Characteristic independence is invariant under the actual component
permutation, so the original closed labels need not be interval labels. -/
theorem closedGraph_weighted_monomial_field_independent
    (G : SimpleGraph (Fin N)) (hG : ClosedLabeling G)
    (ω : FiniteVariable.{u} (GraphRows N) → Γ) (ρ : Γ →+ ℤ)
    (hρ : ∀ v, ρ (ω v) = 1) (m : ℕ) (hm : 0 < m) (p : ℕ) (γ : Γ) :
    graphWeightedMonomialBetti (K := K) G ω m p γ =
      graphWeightedMonomialBetti (K := L) G ω m p γ := by
  let G' := graphComponentRelabeled G
  let e := graphVariableRelabeling (graphComponentRelabeling G)
  let ω' := fun v => ω (e.symm v)
  have hω : ∀ v, ω' (e v) = ω v := by intro v; exact congrArg ω (e.symm_apply_apply v)
  have hρ' : ∀ v, ρ (ω' v) = 1 := fun v => hρ (e.symm v)
  have renameField (F : Type u) [Field F] :
      graphWeightedMonomialBetti (K := F) G ω m p γ =
        graphWeightedMonomialBetti (K := F) G' ω' m p γ := by
    apply finerIdealBettiNumber_rename
      (graphMonomialPowerData (K := F) G m) (graphMonomialPowerData (K := F) G' m) ω ω'
      (monomialIdeal_weighted_homogeneous (graphMonomialPowerFamily G m) ω)
      (monomialIdeal_weighted_homogeneous (graphMonomialPowerFamily G' m) ω') e hω _ p γ
    rw [graphMonomialPowerData_ideal, graphMonomialPowerData_ideal]
    exact graphMonomialIdeal_component_relabel (K := F) G m
  exact (renameField K).trans ((intervalGraph_weighted_betti_field_independent K L G'
    (graphComponentRelabeled_interval G hG) ω' ρ hρ' m hm p γ).trans (renameField L).symm)

/-- **Corollary 6.3, finest monomial grading.** All original exponent
vectors, homological degrees, and positive powers are included. -/
theorem corollary63_monomial_fine (G : SimpleGraph (Fin N)) (hG : ClosedLabeling G)
    (m : ℕ) (hm : 0 < m) (p : ℕ) (α : Exponent (FiniteVariable.{u} (GraphRows N))) :
    bettiNumber (k := K) (graphMonomialPowerFamily G m) α p =
      bettiNumber (k := L) (graphMonomialPowerFamily G m) α p := by
  let ρ : Exponent (FiniteVariable.{u} (GraphRows N)) →+ ℤ :=
    (Nat.castAddMonoidHom ℤ).comp Finsupp.degree
  have hρ : ∀ v : FiniteVariable.{u} (GraphRows N), ρ (finestVariableWeight v) = 1 := by
    intro v
    simp [ρ, finestVariableWeight, Finsupp.degree_single]
  have h := closedGraph_weighted_monomial_field_independent K L G hG
    finestVariableWeight ρ hρ m hm p α
  change finerIdealBettiNumber (graphMonomialPowerData (K := K) G m) _ _ p α =
    finerIdealBettiNumber (graphMonomialPowerData (K := L) G m) _ _ p α at h
  simpa only [graphMonomialPowerData, canonicalWeightedMonomialBettiNumber_eq,
    weightedMonomialBettiNumber_finest] using h

/-- **Corollary 6.3 in the full integer fine grading.** Every integer
exponent vector is retained; negative-coordinate pieces are the actual
zero homogeneous submodules, not omitted parameter values. -/
theorem corollary63_monomial_integer_fine
    (G : SimpleGraph (Fin N)) (hG : ClosedLabeling G)
    (m : ℕ) (hm : 0 < m) (p : ℕ)
    (γ : FiniteVariable.{u} (GraphRows N) →₀ ℤ) :
    graphWeightedMonomialBetti (K:=K) G (fun v => Finsupp.single v (1:ℤ)) m p γ=
      graphWeightedMonomialBetti (K:=L) G (fun v => Finsupp.single v (1:ℤ)) m p γ := by
  let ρ : (FiniteVariable.{u} (GraphRows N) →₀ ℤ) →+ ℤ :=
    Finsupp.weight (fun _ : FiniteVariable.{u} (GraphRows N) => (1:ℤ))
  apply closedGraph_weighted_monomial_field_independent K L G hG
    (fun v => Finsupp.single v (1:ℤ)) ρ ?_ m hm p γ
  intro v
  simp only [ρ,Finsupp.weight_single,one_smul]

/-- **Corollary 6.3, natural binomial grading.** Integer vertex and row
labels are retained, including labels with a zero component. -/
theorem corollary63_binomial_natural (G : SimpleGraph (Fin N)) (hG : ClosedLabeling G)
    (m : ℕ) (hm : 0 < m) (p : ℕ) (γ : GraphNaturalDegree N) :
    graphWeightedBinomialBetti G graphNaturalWeight
        (graphBinomialIdeal_natural_homogeneous (K := K) G) m p γ =
      graphWeightedBinomialBetti G graphNaturalWeight
        (graphBinomialIdeal_natural_homogeneous (K := L) G) m p γ := by
  rw [corollary62_natural G hG, corollary62_natural G hG]
  exact closedGraph_weighted_monomial_field_independent K L G hG graphNaturalWeight
    (graphNaturalRefinement N) graphNaturalRefinement_variable m hm p γ

/-- The component-row refinement in Corollary 6.2 is likewise independent
of the field; the connected components and original vertex labels persist. -/
theorem corollary63_binomial_component_rows (G : SimpleGraph (Fin N)) (hG : ClosedLabeling G)
    (m : ℕ) (hm : 0 < m) (p : ℕ) (γ : GraphComponentDegree G) :
    graphWeightedBinomialBetti G (graphComponentWeight G)
        (graphBinomialIdeal_component_homogeneous (K := K) G) m p γ =
      graphWeightedBinomialBetti G (graphComponentWeight G)
        (graphBinomialIdeal_component_homogeneous (K := L) G) m p γ := by
  rw [corollary62_component_rows G hG, corollary62_component_rows G hG]
  exact closedGraph_weighted_monomial_field_independent K L G hG (graphComponentWeight G)
    (graphComponentRefinement G) (graphComponentRefinement_variable G) m hm p γ

/-- Finite coarsening gives the ordinary field-independence clause for the
actual monomial ideal, before using the binomial comparison. -/
theorem corollary63_monomial_ordinary (G : SimpleGraph (Fin N)) (hG : ClosedLabeling G)
    (m : ℕ) (hm : 0 < m) (p q : ℕ) :
    graphMonomialBetti (K := K) G m p q = graphMonomialBetti (K := L) G m p q := by
  calc
    graphMonomialBetti (K := K) G m p q =
        ordinaryMonomialBettiNumber (k := K) (graphMonomialPowerFamily G m) q p :=
      canonicalMonomialBettiNumber_eq graphLexOrder (graphMonomialPowerFamily G m)
        (monomialIdeal_ordinary_homogeneous _) q p
    _ = ordinaryMonomialBettiNumber (k := L) (graphMonomialPowerFamily G m) q p := by
      rw [ordinaryMonomialBettiNumber_eq_sum, ordinaryMonomialBettiNumber_eq_sum]
      apply Finset.sum_congr rfl
      intro α _
      exact corollary63_monomial_fine K L G hG m hm p α.val
    _ = graphMonomialBetti (K := L) G m p q :=
      (canonicalMonomialBettiNumber_eq graphLexOrder (graphMonomialPowerFamily G m)
        (monomialIdeal_ordinary_homogeneous _) q p).symm

/-- **Corollary 6.3, ordinary grading.** Both original ideal powers have
field-independent ordinary Betti numbers. -/
theorem corollary63_ordinary (G : SimpleGraph (Fin N)) (hG : ClosedLabeling G)
    (m : ℕ) (hm : 0 < m) (p q : ℕ) :
    graphMonomialBetti (K := K) G m p q = graphMonomialBetti (K := L) G m p q ∧
    graphBinomialBetti (K := K) G m p q = graphBinomialBetti (K := L) G m p q := by
  have hmono := corollary63_monomial_ordinary K L G hG m hm p q
  exact ⟨hmono, (theorem11_bettiEquality (K := K) G hG m hm p q).trans
    (hmono.trans (theorem11_bettiEquality (K := L) G hG m hm p q).symm)⟩

/-- The same ordinary conclusion includes all integer degrees. Negative
degrees vanish in the genuine homogeneous Tor submodules on both sides. -/
theorem corollary63_integer_ordinary (G : SimpleGraph (Fin N)) (hG : ClosedLabeling G)
    (m : ℕ) (hm : 0 < m) (p : ℕ) (q : ℤ) :
    graphMonomialIntegerBetti (K := K) G m p q =
        graphMonomialIntegerBetti (K := L) G m p q ∧
    graphBinomialIntegerBetti (K := K) G m p q =
        graphBinomialIntegerBetti (K := L) G m p q := by
  have hmono : graphMonomialIntegerBetti (K := K) G m p q =
      graphMonomialIntegerBetti (K := L) G m p q := by
    by_cases hq : 0 ≤ q
    · have he : (q.toNat : ℤ) = q := Int.toNat_of_nonneg hq
      rw [← he, graphMonomialIntegerBetti_nat, graphMonomialIntegerBetti_nat]
      exact corollary63_monomial_ordinary K L G hG m hm p q.toNat
    · have hq' : q < 0 := lt_of_not_ge hq
      unfold graphMonomialIntegerBetti
      rw [ordinaryIntegerIdealBettiNumber_negative _ _ p q hq',
        ordinaryIntegerIdealBettiNumber_negative _ _ p q hq']
  exact ⟨hmono, (theorem11_integer_bettiEquality (K := K) G hG m hm p q).trans
    (hmono.trans (theorem11_integer_bettiEquality (K := L) G hG m hm p q).symm)⟩

end FourPapers.Sublattice

#print axioms FourPapers.Sublattice.corollary63_monomial_fine

#print axioms FourPapers.Sublattice.corollary63_monomial_integer_fine

#print axioms FourPapers.Sublattice.corollary63_binomial_natural

#print axioms FourPapers.Sublattice.corollary63_binomial_component_rows

#print axioms FourPapers.Sublattice.corollary63_ordinary

#print axioms FourPapers.Sublattice.corollary63_integer_ordinary

end
end
end


end
