module
public import graph_foundation.part014
public import shared_results.part021_canonical_monomial_homology

set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

@[expose] public section

/- BEGIN EXACT BODY: FourPapers.Sublattice.ClosedGraphTheorem11 -/
section

/-! # Theorem 1.1 for every closed labeling

The endpoints are graded submodules of the genuine derived Tor objects of
the displayed original-label ideals. Component sorting is an actual
variable permutation and is applied to both ideals. The Koszul renaming
proof retains ordinary degree and all exterior signs; no connectedness,
interval-labeling, nonempty-edge, or characteristic assumption is added.
-/

section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace FourPapers.Sublattice

open Classical MvPolynomial CommAlg CommAlg.Koszul CommAlg.Polymatroid
attribute [local instance] MvPolynomial.weightedGradedAlgebra
universe u
variable {N : ℕ}

/-- Put whole connected components in consecutive blocks, preserving the
original order within each component. -/
def graphComponentRelabeled (G : SimpleGraph (Fin N)) : SimpleGraph (Fin N) :=
  G.comap (graphComponentRelabeling G).symm

theorem graphComponentRelabeled_interval (G : SimpleGraph (Fin N)) (hG : ClosedLabeling G) :
    IntervalLabeling (graphComponentRelabeled G) :=
  closedGraph_relabeling_interval G hG

theorem graphComponentRelabeling_edge_lt (G : SimpleGraph (Fin N))
    {i j : Fin N} (hij : G.Adj i j) :
    graphComponentRelabeling G i < graphComponentRelabeling G j ↔ i < j := by
  rw [graphComponentRelabeling_lt_iff]
  have hc : graphComponentNumber G i=graphComponentNumber G j :=
    (graphComponentNumber_eq_iff G i j).mpr hij.reachable
  constructor
  · intro h
    exact (Prod.Lex.toLex_lt_toLex'.mp h).2 hc
  · intro h
    exact Prod.Lex.toLex_lt_toLex'.mpr ⟨le_of_eq hc, fun _ => h⟩

def graphVariableRelabeling (e : Fin N ≃ Fin N) :
    FiniteVariable.{u} (GraphRows N) ≃ FiniteVariable.{u} (GraphRows N) where
  toFun v := ⟨v.1,ULift.up (e v.2.down)⟩
  invFun v := ⟨v.1,ULift.up (e.symm v.2.down)⟩
  left_inv v := by rcases v with ⟨r,⟨i⟩⟩; simp only [Equiv.symm_apply_apply]
  right_inv v := by rcases v with ⟨r,⟨i⟩⟩; simp only [Equiv.apply_symm_apply]

theorem graphPairExponent_relabel (e : Fin N ≃ Fin N) (i j : Fin N) :
    (graphPairExponent i j).mapDomain (graphVariableRelabeling.{u} e) =
      graphPairExponent (e i) (e j) := by
  simp only [graphPairExponent, Finsupp.mapDomain_add, Finsupp.mapDomain_single,
    graphVariableRelabeling, Equiv.coe_fn_mk]

section Coefficients
variable {K : Type u} [CommRing K] [IsDomain K]

theorem graphBinomial_relabel (e : Fin N ≃ Fin N) (i j : Fin N) :
    MvPolynomial.rename (graphVariableRelabeling e) (graphBinomial (k := K) i j) =
      graphBinomial (e i) (e j) := by
  simp only [graphBinomial, map_sub, MvPolynomial.rename_monomial, graphPairExponent_relabel]

def graphMonomialGenerators (G : SimpleGraph (Fin N)) :
    Set (MvPolynomial (FiniteVariable.{u} (GraphRows N)) K) :=
  {f | ∃ i j, i<j ∧ G.Adj i j ∧ f=monomial (graphPairExponent i j) 1}

def graphMonomialIdeal (G : SimpleGraph (Fin N)) :
    Ideal (MvPolynomial (FiniteVariable.{u} (GraphRows N)) K) :=
  finiteSublatticeIdeal (GraphRows N) (graphEdgeLattice G)

theorem graphMonomialIdeal_eq_span (G : SimpleGraph (Fin N)) :
    graphMonomialIdeal (K := K) G = Ideal.span (graphMonomialGenerators G) := by
  unfold graphMonomialIdeal finiteSublatticeIdeal
  apply congrArg Ideal.span
  ext f
  constructor
  · rintro ⟨a,ha,rfl⟩
    obtain ⟨hij,hijG⟩ := (mem_graphEdgeLattice G a).mp ha
    refine ⟨a 0,a 1,hij,hijG,?_⟩
    rw [finiteRowMonomial_eq_monomial,graphPairExponent_eq_row,graphTuple_eta]
  · rintro ⟨i,j,hij,hijG,rfl⟩
    refine ⟨graphTuple i j,?_,?_⟩
    · exact (mem_graphEdgeLattice G _).mpr (by
        simpa only [graphTuple_zero,graphTuple_one] using And.intro hij hijG)
    · rw [finiteRowMonomial_eq_monomial,←graphPairExponent_eq_row]

/-- Sorting components carries the exact original binomial generator set
onto the generator set in interval labels. Edge orientations are retained. -/
theorem graphBinomialGenerators_component_relabel (G : SimpleGraph (Fin N)) :
    MvPolynomial.rename (graphVariableRelabeling (graphComponentRelabeling G)) ''
      graphBinomialGenerators (k := K) G =
        graphBinomialGenerators (k := K) (graphComponentRelabeled G) := by
  ext f
  constructor
  · rintro ⟨g,⟨i,j,hij,hijG,rfl⟩,rfl⟩
    refine ⟨graphComponentRelabeling G i,graphComponentRelabeling G j,
      (graphComponentRelabeling_edge_lt G hijG).mpr hij,?_,graphBinomial_relabel _ i j⟩
    simpa only [graphComponentRelabeled,SimpleGraph.comap_adj,Equiv.symm_apply_apply] using hijG
  · rintro ⟨i,j,hij,hijG,rfl⟩
    have hOld : G.Adj ((graphComponentRelabeling G).symm i)
        ((graphComponentRelabeling G).symm j) := hijG
    have hlt := (graphComponentRelabeling_edge_lt G hOld).mp (by
      simpa only [Equiv.apply_symm_apply] using hij)
    refine ⟨graphBinomial ((graphComponentRelabeling G).symm i)
      ((graphComponentRelabeling G).symm j),⟨_,_,hlt,hOld,rfl⟩,?_⟩
    rw [graphBinomial_relabel,Equiv.apply_symm_apply,Equiv.apply_symm_apply]

theorem graphMonomialGenerators_component_relabel (G : SimpleGraph (Fin N)) :
    MvPolynomial.rename (graphVariableRelabeling (graphComponentRelabeling G)) ''
      graphMonomialGenerators (K := K) G =
        graphMonomialGenerators (K := K) (graphComponentRelabeled G) := by
  ext f
  constructor
  · rintro ⟨g,⟨i,j,hij,hijG,rfl⟩,rfl⟩
    refine ⟨graphComponentRelabeling G i,graphComponentRelabeling G j,
      (graphComponentRelabeling_edge_lt G hijG).mpr hij,?_,?_⟩
    · simpa only [graphComponentRelabeled,SimpleGraph.comap_adj,Equiv.symm_apply_apply] using hijG
    · rw [MvPolynomial.rename_monomial,graphPairExponent_relabel]
  · rintro ⟨i,j,hij,hijG,rfl⟩
    have hOld : G.Adj ((graphComponentRelabeling G).symm i)
        ((graphComponentRelabeling G).symm j) := hijG
    have hlt := (graphComponentRelabeling_edge_lt G hOld).mp (by
      simpa only [Equiv.apply_symm_apply] using hij)
    refine ⟨monomial (graphPairExponent ((graphComponentRelabeling G).symm i)
      ((graphComponentRelabeling G).symm j)) 1,⟨_,_,hlt,hOld,rfl⟩,?_⟩
    rw [MvPolynomial.rename_monomial,graphPairExponent_relabel,
      Equiv.apply_symm_apply,Equiv.apply_symm_apply]

theorem graphBinomialIdeal_component_relabel (G : SimpleGraph (Fin N)) (s : ℕ) :
    ((graphBinomialIdeal (k := K) G)^s).map
      (MvPolynomial.rename (graphVariableRelabeling (graphComponentRelabeling G))).toRingHom =
        (graphBinomialIdeal (k := K) (graphComponentRelabeled G))^s := by
  rw [Ideal.map_pow, graphBinomialIdeal, Ideal.map_span]
  change (Ideal.span (MvPolynomial.rename
    (graphVariableRelabeling (graphComponentRelabeling G)) '' graphBinomialGenerators G)) ^ s = _
  rw [graphBinomialGenerators_component_relabel]
  rfl

theorem graphMonomialIdeal_component_relabel (G : SimpleGraph (Fin N)) (s : ℕ) :
    ((graphMonomialIdeal (K := K) G)^s).map
      (MvPolynomial.rename (graphVariableRelabeling (graphComponentRelabeling G))).toRingHom =
        (graphMonomialIdeal (K := K) (graphComponentRelabeled G))^s := by
  rw [Ideal.map_pow, graphMonomialIdeal_eq_span, Ideal.map_span]
  change (Ideal.span (MvPolynomial.rename
    (graphVariableRelabeling (graphComponentRelabeling G)) '' graphMonomialGenerators G)) ^ s = _
  rw [graphMonomialGenerators_component_relabel, ← graphMonomialIdeal_eq_span]

theorem graphBinomialPower_homogeneous (G : SimpleGraph (Fin N)) (s : ℕ) :
    ((graphBinomialIdeal (k := K) G)^s).IsHomogeneous
      (weightedHomogeneousSubmodule K (fun _ : FiniteVariable.{u} (GraphRows N) => (1 : ℕ))) := by
  simpa only [graphParameterIdeal_one] using graphParameterPower_ordinary_homogeneous (1 : K) G s

theorem monomialIdeal_ordinary_homogeneous {V : Type u} [Fintype V] [LinearOrder V]
    (B : Family V) : (monomialIdeal K B).IsHomogeneous
      (weightedHomogeneousSubmodule K (fun _ : V => (1 : ℕ))) := by
  apply Ideal.homogeneous_span
  rintro f ⟨a,ha,rfl⟩
  exact ⟨Finsupp.weight (fun _ : V => (1 : ℕ)) a,
    isWeightedHomogeneous_monomial _ a (1 : K) rfl⟩

end Coefficients

section Betti
variable {K : Type u} [Field K]

/-- Genuine coordinate data for the original binomial power; its existence
does not assume any first-power comparison or all-power Gröbner identity. -/
def graphBinomialPowerData (G : SimpleGraph (Fin N)) (s : ℕ) :
    QuotientGroebnerData (FiniteVariable.{u} (GraphRows N)) K :=
  canonicalQuotientGroebnerData graphLexOrder ((graphBinomialIdeal G)^s)

def graphMonomialPowerFamily (G : SimpleGraph (Fin N)) (s : ℕ) :
    Family (FiniteVariable.{u} (GraphRows N)) :=
  exponentPowerFamily (finiteRowFamily (GraphRows N) (graphEdgeLattice G)) s

def graphMonomialPowerData (G : SimpleGraph (Fin N)) (s : ℕ) :
    QuotientGroebnerData (FiniteVariable.{u} (GraphRows N)) K :=
  canonicalQuotientGroebnerData graphLexOrder (monomialIdeal K (graphMonomialPowerFamily G s))

theorem graphMonomialPowerData_ideal (G : SimpleGraph (Fin N)) (s : ℕ) :
    (graphMonomialPowerData (K := K) G s).ideal = (graphMonomialIdeal (K := K) G)^s :=
  finitePowerFamily_ideal (n := GraphRows N) (graphEdgeLattice G) s

/-- The degree-q part of Tor of the original binomial ideal power. -/
def graphBinomialBetti (G : SimpleGraph (Fin N)) (s p q : ℕ) : ℕ :=
  ordinaryIdealBettiNumber (graphBinomialPowerData (K := K) G s)
    (graphBinomialPower_homogeneous G s) p q

/-- The degree-q part of Tor of the original edge-monomial ideal power;
`graphMonomialPowerData_ideal` is the literal ideal-power identification. -/
def graphMonomialBetti (G : SimpleGraph (Fin N)) (s p q : ℕ) : ℕ :=
  ordinaryIdealBettiNumber (graphMonomialPowerData (K := K) G s)
    (monomialIdeal_ordinary_homogeneous (graphMonomialPowerFamily G s)) p q

/-- The interval-label comparison on the actual derived-Tor Betti numbers.
The first-power cycle lifts discharge the input of the general all-power criterion. -/
theorem intervalGraph_betti_eq (G : SimpleGraph (Fin N)) (hG : IntervalLabeling G)
    (s p q : ℕ) : graphBinomialBetti (K := K) G s p q = graphMonomialBetti (K := K) G s p q := by
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
  let Q := graphParameterQuotientData (1 : K) one_ne_zero G (intervalLabeling_closed hG)
  have hfirst : ∀ a b, sublatticePowerBettiNumber (GraphRows N) graphLexOrder
      (graphBinomialIdeal (k := K) G) (graphEdgeLattice G) hE hinit hOrd 1 a b =
        sublatticeMonomialPowerBettiNumber (K := K) (GraphRows N) (graphEdgeLattice G) 1 a b := by
    intro a b
    calc
      _ = ordinaryIdealBettiNumber Q (graphParameterIdeal_total_homogeneous (1 : K) G) a b :=
        ordinaryIdealBettiNumber_rename (P 1) Q
          (homogeneousIdealPower (GraphRows N) (graphBinomialIdeal G) hOrd 1)
          (graphParameterIdeal_total_homogeneous (1 : K) G) (Equiv.refl _)
          (by change ((graphBinomialIdeal G)^1).map (MvPolynomial.rename id).toRingHom =
                graphParameterIdeal (1 : K) G
              rw [MvPolynomial.rename_id]
              change ((graphBinomialIdeal G)^1).map (RingHom.id _) =
                graphParameterIdeal (1 : K) G
              rw [Ideal.map_id, pow_one, graphParameterIdeal_one]) a b
      _ = ordinaryMonomialBettiNumber (k := K)
          (finiteRowFamily (GraphRows N) (graphEdgeLattice G)) b a :=
        intervalGraph_parameter_first_betti_eq hG (1 : K) one_ne_zero a b
      _ = _ := by simp only [sublatticeMonomialPowerBettiNumber, exponentPowerFamily_one]
  calc
    graphBinomialBetti (K := K) G s p q =
        sublatticePowerBettiNumber (GraphRows N) graphLexOrder
          (graphBinomialIdeal (k := K) G) (graphEdgeLattice G) hE hinit hOrd s p q :=
      ordinaryIdealBettiNumber_rename (graphBinomialPowerData G s) (P s)
        (graphBinomialPower_homogeneous G s)
        (homogeneousIdealPower (GraphRows N) (graphBinomialIdeal G) hOrd s) (Equiv.refl _)
        (by change ((graphBinomialIdeal G)^s).map (MvPolynomial.rename id).toRingHom = _
            rw [MvPolynomial.rename_id]
            change ((graphBinomialIdeal G)^s).map (RingHom.id _) = (graphBinomialIdeal G)^s
            rw [Ideal.map_id]) p q
    _ = sublatticeMonomialPowerBettiNumber (K := K) (GraphRows N) (graphEdgeLattice G) s p q :=
      theorem43_ordinary_betti (GraphRows N) graphLexOrder (graphBinomialIdeal G)
        (graphEdgeLattice G) hE hinit hOrd hfirst s p q
    _ = graphMonomialBetti (K := K) G s p q :=
      (canonicalMonomialBettiNumber_eq graphLexOrder (graphMonomialPowerFamily G s)
        (monomialIdeal_ordinary_homogeneous _) q p).symm

/-- Paper Theorem 1.1: every original closed labeling, every field, every
positive power, and every homological and ordinary degree. Both sides are
homogeneous submodules of the genuine derived Tor of the actual ideals. -/
theorem theorem11_bettiEquality (G : SimpleGraph (Fin N)) (hG : ClosedLabeling G)
    (s : ℕ) (_hs : 0 < s) (p q : ℕ) :
    graphBinomialBetti (K := K) G s p q = graphMonomialBetti (K := K) G s p q := by
  let G' := graphComponentRelabeled G
  let e := graphVariableRelabeling (graphComponentRelabeling G)
  have hbin : graphBinomialBetti (K := K) G s p q = graphBinomialBetti (K := K) G' s p q :=
    ordinaryIdealBettiNumber_rename (graphBinomialPowerData G s) (graphBinomialPowerData G' s)
      (graphBinomialPower_homogeneous G s) (graphBinomialPower_homogeneous G' s)
      e (graphBinomialIdeal_component_relabel G s) p q
  have hmon : graphMonomialBetti (K := K) G s p q = graphMonomialBetti (K := K) G' s p q := by
    apply ordinaryIdealBettiNumber_rename (graphMonomialPowerData G s) (graphMonomialPowerData G' s)
      (monomialIdeal_ordinary_homogeneous _) (monomialIdeal_ordinary_homogeneous _) e _ p q
    rw [graphMonomialPowerData_ideal,graphMonomialPowerData_ideal]
    exact graphMonomialIdeal_component_relabel G s
  exact hbin.trans ((intervalGraph_betti_eq G' (graphComponentRelabeled_interval G hG) s p q).trans hmon.symm)

end Betti
end FourPapers.Sublattice

end
end
end


end
