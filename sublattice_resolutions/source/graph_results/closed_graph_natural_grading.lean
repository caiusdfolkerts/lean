module
public import graph_results.canonical_finer_monomial_homology
public import shared_results.part021

set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

@[expose] public section

/- BEGIN EXACT BODY: FourPapers.Sublattice.ClosedGraphNaturalGrading -/
section

/-!
# Corollary 6.2: the original natural and component row gradings

The endpoints use the actual original-label binomial and monomial ideal
powers. Component sorting acts through polynomial and exterior renaming;
its temporary variable weights are pulled back along the inverse
permutation. Thus no interval-labeling assumption survives in the result.
The label groups contain all integer coordinates, including degrees in
which the homogeneous component is zero.
-/

section
set_option autoImplicit false
set_option maxHeartbeats 20000
set_option synthInstance.maxHeartbeats 5000
set_option maxRecDepth 4096
noncomputable section

namespace FourPapers.Sublattice

open Classical CommAlg CommAlg.Polymatroid MvPolynomial
attribute [local instance] MvPolynomial.weightedGradedAlgebra

universe u v
variable {K : Type u} [Field K] {N : ℕ}
  {Γ : Type v} [AddCommMonoid Γ]

/-- The literal homogeneous-ideal proposition, with its grading structures
fixed at the generic additive monoid. Concrete natural and component
weights use this same proposition when entering the Tor definitions. -/
def graphWeightedHomogeneous (G : SimpleGraph (Fin N))
    (ω : FiniteVariable.{u} (GraphRows N) → Γ) : Prop :=
  (graphBinomialIdeal (k := K) G).IsHomogeneous (weightedHomogeneousSubmodule K ω)

/-- The named interface is exactly ordinary weighted ideal homogeneity. -/
theorem graphWeightedHomogeneous_iff (G : SimpleGraph (Fin N))
    (ω : FiniteVariable.{u} (GraphRows N) → Γ) :
    graphWeightedHomogeneous (K := K) G ω ↔
      (graphBinomialIdeal (k := K) G).IsHomogeneous (weightedHomogeneousSubmodule K ω) := Iff.rfl

/-- Weighted Betti numbers of the literal original binomial power. -/
def graphWeightedBinomialBetti (G : SimpleGraph (Fin N))
    (ω : FiniteVariable.{u} (GraphRows N) → Γ)
    (hJ : graphWeightedHomogeneous (K := K) G ω)
    (s p : ℕ) (γ : Γ) : ℕ :=
  finerIdealBettiNumber (graphBinomialPowerData (K := K) G s) ω
    (homogeneousIdealPowerWeighted (GraphRows N) (graphBinomialIdeal G) ω hJ s) p γ

/-- Weighted Betti numbers of the literal original monomial power.
`graphMonomialPowerData_ideal` identifies the displayed coefficient ideal
with that actual ideal power. -/
def graphWeightedMonomialBetti (G : SimpleGraph (Fin N))
    (ω : FiniteVariable.{u} (GraphRows N) → Γ) (s p : ℕ) (γ : Γ) : ℕ :=
  finerIdealBettiNumber (graphMonomialPowerData (K := K) G s) ω
    (monomialIdeal_weighted_homogeneous (graphMonomialPowerFamily G s) ω) p γ

/-- In interval labels the universal first-power criterion retains every
compatible finer grading. The numerical first-power input is the already
proved comparison of the original ideal's genuine Tor groups. -/
theorem intervalGraph_weighted_betti_eq (G : SimpleGraph (Fin N)) (hG : IntervalLabeling G)
    (ω : FiniteVariable.{u} (GraphRows N) → Γ) (ρ : Γ →+ ℤ) (hρ : ∀ v, ρ (ω v) = 1)
    (hJ : graphWeightedHomogeneous (K := K) G ω)
    (s p : ℕ) (γ : Γ) :
    graphWeightedBinomialBetti (K := K) G ω hJ s p γ = graphWeightedMonomialBetti (K := K) G ω s p γ := by
  let hE := graphEdgeLattice_closed hG
  have hinit : FourPapers.initialIdeal graphLexOrder (graphBinomialIdeal (k := K) G) =
      finiteSublatticeIdeal (GraphRows N) (graphEdgeLattice G) := by
    simpa only [graphParameterIdeal_one] using
      graphParameter_initialIdeal (1 : K) one_ne_zero (intervalLabeling_closed hG)
  have hOrd : (graphBinomialIdeal (k := K) G).IsHomogeneous
      (weightedHomogeneousSubmodule K (fun _ : FiniteVariable.{u} (GraphRows N) => (1 : ℕ))) := by
    simpa only [pow_one] using graphBinomialPower_homogeneous (K := K) G 1
  let P := fun r => sublatticePowerQuotientData (GraphRows N) graphLexOrder
    (graphBinomialIdeal (k := K) G) (graphEdgeLattice G) hE hinit r
  have hfirst : ∀ a q, sublatticePowerBettiNumber (GraphRows N) graphLexOrder
      (graphBinomialIdeal (k := K) G) (graphEdgeLattice G) hE hinit hOrd 1 a q =
        sublatticeMonomialPowerBettiNumber (K := K) (GraphRows N) (graphEdgeLattice G) 1 a q := by
    intro a q
    calc
      _ = graphBinomialBetti (K := K) G 1 a q :=
        ordinaryIdealBettiNumber_rename (P 1) (graphBinomialPowerData G 1)
          (homogeneousIdealPower (GraphRows N) (graphBinomialIdeal G) hOrd 1)
          (graphBinomialPower_homogeneous G 1) (Equiv.refl _)
          (by change ((graphBinomialIdeal G)^1).map (MvPolynomial.rename id).toRingHom = _
              rw [MvPolynomial.rename_id]
              change Ideal.map (RingHom.id _) ((graphBinomialIdeal (k := K) G)^1) =
                (graphBinomialIdeal G)^1
              exact Ideal.map_id ((graphBinomialIdeal (k := K) G)^1)) a q
      _ = graphMonomialBetti (K := K) G 1 a q := intervalGraph_betti_eq G hG 1 a q
      _ = _ := canonicalMonomialBettiNumber_eq graphLexOrder (graphMonomialPowerFamily G 1)
        (monomialIdeal_ordinary_homogeneous _) q a
  calc
    graphWeightedBinomialBetti (K := K) G ω hJ s p γ =
        finerIdealBettiNumber (P s) ω
          (homogeneousIdealPowerWeighted (GraphRows N) (graphBinomialIdeal G) ω hJ s) p γ :=
      finerIdealBettiNumber_rename (graphBinomialPowerData G s) (P s) ω ω
        (homogeneousIdealPowerWeighted (GraphRows N) (graphBinomialIdeal G) ω hJ s)
        (homogeneousIdealPowerWeighted (GraphRows N) (graphBinomialIdeal G) ω hJ s)
        (Equiv.refl _) (fun _ => rfl)
        (by change ((graphBinomialIdeal G)^s).map (MvPolynomial.rename id).toRingHom = _
            rw [MvPolynomial.rename_id]
            change Ideal.map (RingHom.id _) ((graphBinomialIdeal (k := K) G)^s) =
              (graphBinomialIdeal G)^s
            exact Ideal.map_id ((graphBinomialIdeal (k := K) G)^s)) p γ
    _ = initialFinerBettiNumber (P s) ω p γ :=
      theorem43_finer_betti (GraphRows N) graphLexOrder (graphBinomialIdeal G)
        (graphEdgeLattice G) hE hinit hOrd ω ρ hρ hJ hfirst s p γ
    _ = graphWeightedMonomialBetti (K := K) G ω s p γ :=
      initialFinerBettiNumber_eq_canonical (P s) ω p γ

/-- Every compatible refinement of ordinary degree is preserved in every
original closed labeling. The grading labels remain fixed throughout the
actual variable-permutation equivalences. -/
theorem closedGraph_weighted_betti_eq (G : SimpleGraph (Fin N)) (hG : ClosedLabeling G)
    (ω : FiniteVariable.{u} (GraphRows N) → Γ) (ρ : Γ →+ ℤ) (hρ : ∀ v, ρ (ω v) = 1)
    (hJ : graphWeightedHomogeneous (K := K) G ω)
    (s p : ℕ) (γ : Γ) :
    graphWeightedBinomialBetti (K := K) G ω hJ s p γ = graphWeightedMonomialBetti (K := K) G ω s p γ := by
  let G' := graphComponentRelabeled G
  let e := graphVariableRelabeling (graphComponentRelabeling G)
  let ω' := fun v => ω (e.symm v)
  have hω : ∀ v, ω' (e v) = ω v := by intro v; dsimp only [ω']; rw [e.symm_apply_apply]
  have hρ' : ∀ v, ρ (ω' v) = 1 := fun v => hρ (e.symm v)
  have hJ' : graphWeightedHomogeneous (K := K) G' ω' := by
    change (graphBinomialIdeal (k := K) G').IsHomogeneous
      (weightedHomogeneousSubmodule K ω')
    have he : (graphBinomialIdeal (k := K) G).map (MvPolynomial.rename e).toRingHom =
        graphBinomialIdeal G' := by
      simpa only [pow_one] using graphBinomialIdeal_component_relabel (K := K) G 1
    rw [← he]
    exact homogeneousIdeal_rename_weighted (graphBinomialIdeal G) ω ω' e hω hJ
  have hbin : graphWeightedBinomialBetti (K := K) G ω hJ s p γ =
      graphWeightedBinomialBetti (K := K) G' ω' hJ' s p γ :=
    finerIdealBettiNumber_rename (graphBinomialPowerData G s) (graphBinomialPowerData G' s) ω ω'
      (homogeneousIdealPowerWeighted (GraphRows N) (graphBinomialIdeal G) ω hJ s)
      (homogeneousIdealPowerWeighted (GraphRows N) (graphBinomialIdeal G') ω' hJ' s)
      e hω (graphBinomialIdeal_component_relabel (K := K) G s) p γ
  have hmon : graphWeightedMonomialBetti (K := K) G ω s p γ =
      graphWeightedMonomialBetti (K := K) G' ω' s p γ := by
    apply finerIdealBettiNumber_rename (graphMonomialPowerData G s) (graphMonomialPowerData G' s) ω ω'
      (monomialIdeal_weighted_homogeneous (graphMonomialPowerFamily G s) ω)
      (monomialIdeal_weighted_homogeneous (graphMonomialPowerFamily G' s) ω') e hω _ p γ
    rw [graphMonomialPowerData_ideal, graphMonomialPowerData_ideal]
    exact graphMonomialIdeal_component_relabel (K := K) G s
  exact hbin.trans ((intervalGraph_weighted_betti_eq G'
    (graphComponentRelabeled_interval G hG) ω' ρ hρ' hJ' s p γ).trans hmon.symm)

/-- Full integer vertex degrees and the number of first-row variables. -/
abbrev GraphNaturalDegree (N : ℕ) := (Fin N →₀ ℤ) × ℤ

def graphNaturalWeight (v : FiniteVariable.{u} (GraphRows N)) : GraphNaturalDegree N :=
  (Finsupp.single v.2.down 1, if v.1 = 0 then 1 else 0)

def graphNaturalRefinement (N : ℕ) : GraphNaturalDegree N →+ ℤ :=
  (Finsupp.weight (R := ℤ) (fun _ : Fin N => (1 : ℤ))).comp (AddMonoidHom.fst _ _)

theorem graphNaturalRefinement_variable (v : FiniteVariable.{u} (GraphRows N)) :
    graphNaturalRefinement N (graphNaturalWeight v) = 1 := by
  simp [graphNaturalRefinement, graphNaturalWeight, Finsupp.weight_single]

/-- The component-row grading uses a separate integer count for every
connected component, with the same integer vertex coordinates. -/
abbrev GraphComponentDegree (G : SimpleGraph (Fin N)) :=
  (Fin N →₀ ℤ) × (G.ConnectedComponent →₀ ℤ)

def graphComponentWeight (G : SimpleGraph (Fin N))
    (v : FiniteVariable.{u} (GraphRows N)) : GraphComponentDegree G :=
  (Finsupp.single v.2.down 1,
    if v.1 = 0 then Finsupp.single (G.connectedComponentMk v.2.down) 1 else 0)

def graphComponentRefinement (G : SimpleGraph (Fin N)) : GraphComponentDegree G →+ ℤ :=
  (Finsupp.weight (R := ℤ) (fun _ : Fin N => (1 : ℤ))).comp (AddMonoidHom.fst _ _)

theorem graphComponentRefinement_variable (G : SimpleGraph (Fin N))
    (v : FiniteVariable.{u} (GraphRows N)) :
    graphComponentRefinement G (graphComponentWeight G v) = 1 := by
  simp [graphComponentRefinement, graphComponentWeight, Finsupp.weight_single]

lemma graphBinomialIdeal_weighted_homogeneous
    [hNat : Module ℕ Γ] [hDec : DecidableEq Γ] (G : SimpleGraph (Fin N))
    (ω : FiniteVariable.{u} (GraphRows N) → Γ)
    (hpairs : ∀ i j, G.Adj i j →
      Finsupp.weight ω (graphPairExponent i j) = Finsupp.weight ω (graphPairExponent j i)) :
    graphWeightedHomogeneous (K := K) G ω := by
  have hd : hDec = Classical.decEq Γ := Subsingleton.elim _ _
  subst hDec
  have hn : hNat = (AddCommMonoid.toNatModule : Module ℕ Γ) := Subsingleton.elim _ _
  subst hNat
  unfold graphWeightedHomogeneous
  apply Ideal.homogeneous_span
  rintro _ ⟨i, j, _, hij, rfl⟩
  refine ⟨Finsupp.weight ω (graphPairExponent i j), ?_⟩
  exact (isWeightedHomogeneous_monomial ω (graphPairExponent i j) (1 : K) rfl).sub
    (isWeightedHomogeneous_monomial ω (graphPairExponent j i) (1 : K) (hpairs i j hij).symm)

theorem graphBinomialIdeal_natural_homogeneous (G : SimpleGraph (Fin N)) :
    graphWeightedHomogeneous (K := K) G graphNaturalWeight := by
  have hpairs : ∀ i j, G.Adj i j →
      Finsupp.weight (graphNaturalWeight.{u} (N := N)) (graphPairExponent i j) =
        Finsupp.weight graphNaturalWeight.{u} (graphPairExponent j i) := by
    intro i j _
    simp [graphPairExponent, Finsupp.weight_single, graphNaturalWeight, add_comm]
  exact graphBinomialIdeal_weighted_homogeneous (K := K) G graphNaturalWeight hpairs

theorem graphBinomialIdeal_component_homogeneous (G : SimpleGraph (Fin N)) :
    graphWeightedHomogeneous (K := K) G (graphComponentWeight G) := by
  have hpairs : ∀ i j, G.Adj i j →
      Finsupp.weight (graphComponentWeight.{u} G) (graphPairExponent i j) =
        Finsupp.weight (graphComponentWeight.{u} G) (graphPairExponent j i) := by
    intro i j hij
    have hc : G.connectedComponentMk i = G.connectedComponentMk j :=
      SimpleGraph.ConnectedComponent.sound hij.reachable
    simp [graphPairExponent, Finsupp.weight_single, graphComponentWeight, hc, add_comm]
  exact graphBinomialIdeal_weighted_homogeneous (K := K) G (graphComponentWeight G) hpairs

/-- **Corollary 6.2, natural grading.** Every power, homological degree,
and integer natural multidegree of the original ideals is included. -/
theorem corollary62_natural (G : SimpleGraph (Fin N)) (hG : ClosedLabeling G)
    (s p : ℕ) (γ : GraphNaturalDegree N) :
    graphWeightedBinomialBetti (K := K) G graphNaturalWeight
        (graphBinomialIdeal_natural_homogeneous (K := K) G) s p γ =
      graphWeightedMonomialBetti (K := K) G graphNaturalWeight s p γ :=
  closedGraph_weighted_betti_eq (K := K) G hG graphNaturalWeight (graphNaturalRefinement N)
    graphNaturalRefinement_variable (graphBinomialIdeal_natural_homogeneous (K := K) G) s p γ

/-- **Corollary 6.2, component row counts.** Isolated vertices and any
number of connected components are retained in their original labels. -/
theorem corollary62_component_rows (G : SimpleGraph (Fin N)) (hG : ClosedLabeling G)
    (s p : ℕ) (γ : GraphComponentDegree G) :
    graphWeightedBinomialBetti (K := K) G (graphComponentWeight G)
        (graphBinomialIdeal_component_homogeneous (K := K) G) s p γ =
      graphWeightedMonomialBetti (K := K) G (graphComponentWeight G) s p γ :=
  closedGraph_weighted_betti_eq (K := K) G hG (graphComponentWeight G) (graphComponentRefinement G)
    (graphComponentRefinement_variable G) (graphBinomialIdeal_component_homogeneous (K := K) G) s p γ

end FourPapers.Sublattice

end
end
end


end
