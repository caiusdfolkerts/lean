module
public import graph_results.quotient_diagonal
public import shared_results.part023
public import shared_results.part021
public import graph_foundation.part009
public import graph_results.graph_paper_linear_variables

set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

@[expose] public section

/- BEGIN EXACT BODY: FourPapers.Sublattice.ClosedGraphLinearStrand -/
section

/-! # Corollary 6.4: the explicit linear strand in every graph power -/

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 20000
set_option synthInstance.maxHeartbeats 5000
noncomputable section

namespace FourPapers.Sublattice
open Classical CommAlg CommAlg.Koszul CommAlg.Polymatroid
open FourPapers.MultichainCounting
universe u
variable {k : Type u} [Field k]
variable {d : ℕ} {n : Fin d → ℕ} {E : Finset (FiniteTuple n)}

/-- No predecessor ratio is constant: its first differing row contributes
an actual variable. This proves properness without an extra hypothesis. -/
theorem finitePredecessor_zero_allowed (a : FiniteTuple n) :
    QuotientAllowed (finitePredecessorFamily.{u} n E a) 0 := by
  rintro ⟨c,hc,hc0⟩
  obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hc
  obtain ⟨r,hr,_⟩ := (Finset.mem_filter.mp hb).2
  have hne : a r ≠ b r := Ne.symm hr.ne
  have hh := hc0 ⟨r,ULift.up (b r)⟩
  simp only [Finsupp.tsub_apply, finiteRowExponent_apply, ite_true,
    if_neg hne, Nat.sub_zero, Finsupp.zero_apply] at hh
  omega

theorem strictSupportCoefficient_zero_allowed (s : StrictSupport E) :
    QuotientAllowed (strictSupportCoefficientFamily.{u} s) 0 := by
  rintro ⟨c,hc,hc0⟩
  obtain ⟨a,_,ha⟩ := Finset.mem_biUnion.mp hc
  exact finitePredecessor_zero_allowed (E := E) a.val ⟨c,ha,hc0⟩

variable {N : ℕ}

/-- The set denoted V_sigma in the paper, defined as the literal union of
the linear-variable sets of the predecessor colons. -/
def graphSupportLinearVariables (G : SimpleGraph (Fin N))
    (s : StrictSupport (graphEdgeLattice G)) : Finset (FiniteVariable.{u} (GraphRows N)) :=
  s.val.biUnion fun a => graphLinearVariables G a.val

/-- The support variables in the sum are exactly the union of the paper's
minimum-neighbor intervals, not just an isomorphic or equally sized set. -/
theorem graphSupportLinearVariables_eq_paper (G : SimpleGraph (Fin N))
    (hG : IntervalLabeling G) (s : StrictSupport (graphEdgeLattice G)) :
    graphSupportLinearVariables.{u} G s =
      s.val.biUnion (fun a => graphPaperLinearVariables G a.val) := by
  apply Finset.biUnion_congr rfl
  intro a _
  exact graphLinearVariables_eq_paper G hG a.property

lemma graphColon_contains_variable (G : SimpleGraph (Fin N))
    (a : FiniteTuple (GraphRows N)) (v : FiniteVariable.{u} (GraphRows N)) :
    Contains (graphColonFamily G a) (Finsupp.single v 1) ↔ v ∈ graphLinearVariables G a := by
  constructor
  · rintro ⟨b,hb,hbv⟩
    rcases Finset.mem_union.mp hb with hb | hb
    · obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hb
      by_cases hwv : w = v
      · exact hwv ▸ hw
      · have hh := hbv w
        simp [Finsupp.single_apply, hwv, Ne.symm hwv] at hh
    · obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hb
      have hh := Finsupp.degree_mono hbv
      simp only [finiteRowExponent_degree, Finsupp.degree_single] at hh
      omega
  · intro hv
    exact ⟨Finsupp.single v 1,
      Finset.mem_union_left _ (Finset.mem_image.mpr ⟨v,hv,rfl⟩),le_rfl⟩

lemma graphPredecessor_contains_variable (G : SimpleGraph (Fin N))
    (hG : IntervalLabeling G) (a : graphEdgeLattice G)
    (v : FiniteVariable.{u} (GraphRows N)) :
    Contains (finitePredecessorFamily (GraphRows N) (graphEdgeLattice G) a.val)
        (Finsupp.single v 1) ↔ v ∈ graphLinearVariables G a.val := by
  rw [← finiteCoordinatePredecessor_contains_iff (graphEdgeLattice_closed hG) a.property,
    graphCoordinateColon_contains_iff hG a.property, graphColon_contains_variable]

lemma graphSupport_quotientLinearVariables (G : SimpleGraph (Fin N))
    (hG : IntervalLabeling G) (s : StrictSupport (graphEdgeLattice G)) :
    quotientLinearVariables (strictSupportCoefficientFamily.{u} s) =
      graphSupportLinearVariables G s := by
  ext v
  simp only [quotientLinearVariables, Finset.mem_filter, Finset.mem_univ, true_and,
    graphSupportLinearVariables, Finset.mem_biUnion]
  constructor
  · rintro ⟨b,hb,hbv⟩
    obtain ⟨a,ha,hb⟩ := Finset.mem_biUnion.mp hb
    exact ⟨a,ha,(graphPredecessor_contains_variable G hG a v).mp ⟨b,hb,hbv⟩⟩
  · rintro ⟨a,ha,hv⟩
    obtain ⟨b,hb,hbv⟩ := (graphPredecessor_contains_variable G hG a v).mpr hv
    exact ⟨b,Finset.mem_biUnion.mpr ⟨a,ha,hb⟩,hbv⟩

/-- **Corollary 6.4 in the interval labeling fixed in Section 6.1.**
The sum runs over every nonempty strict support chain of actual graph edges. -/
theorem corollary64_interval (G : SimpleGraph (Fin N)) (hG : IntervalLabeling G)
    (m : ℕ) (hm : 0 < m) (p : ℕ) :
    graphBinomialBetti (K := k) G m p (2*m+p) =
        graphMonomialBetti (K := k) G m p (2*m+p) ∧
    graphMonomialBetti (K := k) G m p (2*m+p) =
      ∑ s : StrictSupport (graphEdgeLattice G),
        (m-1).choose (s.val.card-1) * (graphSupportLinearVariables.{u} G s).card.choose p := by
  refine ⟨intervalGraph_betti_eq G hG m p (2*m+p),?_⟩
  have hmono : graphMonomialBetti (K := k) G m p (2*m+p) =
      ordinaryMonomialBettiNumber (k := k) (graphMonomialPowerFamily G m) (2*m+p) p :=
    canonicalMonomialBettiNumber_eq graphLexOrder (graphMonomialPowerFamily G m)
      (monomialIdeal_ordinary_homogeneous _) (2*m+p) p
  rw [hmono]
  change ordinaryMonomialBettiNumber (k := k)
    (exponentPowerFamily (finiteRowFamily (GraphRows N) (graphEdgeLattice G)) m)
      (2*m+p) p = _
  rw [show 2*m+p = m*2+p by omega, corollary51 (graphEdgeLattice_closed hG) m hm]
  apply Finset.sum_congr rfl
  intro s _
  rw [ordinaryQuotientBetti_diagonal _ (strictSupportCoefficient_zero_allowed s),
    graphSupport_quotientLinearVariables G hG s]

/-- For arbitrary closed labels, the sum uses the canonical interval relabeling
specified in Section 6.1. The left-hand ideals retain their original labels. -/
theorem corollary64_closed (G : SimpleGraph (Fin N)) (hG : ClosedLabeling G)
    (m : ℕ) (hm : 0 < m) (p : ℕ) :
    graphBinomialBetti (K := k) G m p (2*m+p) =
        graphMonomialBetti (K := k) G m p (2*m+p) ∧
    graphMonomialBetti (K := k) G m p (2*m+p) =
      ∑ s : StrictSupport (graphEdgeLattice (graphComponentRelabeled G)),
        (m-1).choose (s.val.card-1) *
          (graphSupportLinearVariables.{u} (graphComponentRelabeled G) s).card.choose p := by
  have hmono : graphMonomialBetti (K := k) G m p (2*m+p) =
      graphMonomialBetti (K := k) (graphComponentRelabeled G) m p (2*m+p) := by
    apply ordinaryIdealBettiNumber_rename
      (graphMonomialPowerData (K := k) G m)
      (graphMonomialPowerData (K := k) (graphComponentRelabeled G) m)
      (monomialIdeal_ordinary_homogeneous (graphMonomialPowerFamily G m))
      (monomialIdeal_ordinary_homogeneous (graphMonomialPowerFamily (graphComponentRelabeled G) m))
      (graphVariableRelabeling (graphComponentRelabeling G)) _ p (2*m+p)
    rw [graphMonomialPowerData_ideal, graphMonomialPowerData_ideal]
    exact graphMonomialIdeal_component_relabel (K := k) G m
  refine ⟨theorem11_bettiEquality G hG m hm p (2*m+p),?_⟩
  exact hmono.trans (corollary64_interval (graphComponentRelabeled G)
    (graphComponentRelabeled_interval G hG) m hm p).2

end FourPapers.Sublattice

end
end
end


end
