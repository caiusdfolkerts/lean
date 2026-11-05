module
public import mixed_results.initial_column_prefix_graph
public import shared_results.part009
public import shared_results.part024
public import shared_results.part021

set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

@[expose] public section

/- BEGIN EXACT BODY: FourPapers.Sublattice.InitialColumnPrefixGraphTransfer -/
section

/-! # Section 6.3 for interval-graph prefixes

The coefficient ideals are the binomial edge ideals of the actual induced
initial-column subgraphs. Their first-power comparison, nested initial
ideals and characteristic independence are all derived here.
-/

section
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace FourPapers.Sublattice
open Classical CommAlg CommAlg.Polymatroid MvPolynomial
open IntegerFiltered.MultiplicativeFiltration
attribute [local instance] MvPolynomial.weightedGradedAlgebra
universe u
variable {K : Type u} [Field K] {N r : ℕ}
local notation "n" => GraphRows N

def graphPrefixIdeals (G : SimpleGraph (Fin N)) (c : Fin r → ℕ) :
    ULift.{u} (Fin r) → Ideal (MvPolynomial (FiniteVariable.{u} n) K) :=
  fun i => graphBinomialIdeal (initialColumnGraph G (c i.down))

variable (G : SimpleGraph (Fin N)) (hG : IntervalLabeling G)
  (c : Fin r → ℕ) (hc : Monotone c)
local notation "E" => initialColumnPrefixes (graphEdgeLattice G) c
local notation "hE" => initialColumnPrefixes_colored (graphEdgeLattice_unitInterval G hG) c hc
local notation "J" => graphPrefixIdeals (K := K) G c

include hc in
theorem graphPrefixIdeals_mono : Monotone J := by
  intro i j hij
  exact initialColumnGraph_binomial_mono G (hc hij)

theorem graphPrefixIdeals_homogeneous (i : ULift.{u} (Fin r)) :
    (J i).IsHomogeneous (weightedHomogeneousSubmodule K (fun _ : (FiniteVariable.{u} n) => (1 : ℕ))) := by
  simpa only [graphPrefixIdeals, pow_one] using
    graphBinomialPower_homogeneous (K := K) (initialColumnGraph G (c i.down)) 1

include hG in
theorem graphPrefixIdeals_initial (i : ULift.{u} (Fin r)) :
    FourPapers.initialIdeal graphLexOrder (J i)=coloredIdeals (k := K) n E i := by
  have hi := graphParameter_initialIdeal (1 : K) one_ne_zero
    (intervalLabeling_closed (initialColumnGraph_interval G hG (c i.down)))
  simpa only [graphPrefixIdeals, coloredIdeals, initialColumnPrefixes,
    graphParameterIdeal_one, initialColumnGraph_lattice] using hi

include hG hc in
theorem graphPrefixMixed_initial (m : ULift.{u} (Fin r) →₀ ℕ) :
    FourPapers.initialIdeal graphLexOrder (powerProduct J m)=
      powerProduct (coloredIdeals (k := K) n E) m :=
  corollary57_original_initial J E graphLexOrder hE
    (graphPrefixIdeals_mono G c hc) (graphPrefixIdeals_initial G hG c) m

theorem graphPrefixMixed_first_betti (i : ULift.{u} (Fin r)) (p q : ℕ) :
    mixedPowerBettiNumber n E graphLexOrder J (graphPrefixMixed_initial G hG c hc)
      (graphPrefixIdeals_homogeneous G c) (Finsupp.single i 1) p q=
      mixedMonomialBettiNumber (K := K) n E (Finsupp.single i 1) p q := by
  let H := initialColumnGraph G (c i.down)
  let B := mixedRowPowerFamily n E (Finsupp.single i 1)
  let C := graphMonomialPowerFamily H 1
  let l₀ : LinearOrder (FiniteVariable.{u} n) := finiteVariableLinearOrder n
  have hI : monomialIdeal K C=monomialIdeal K B := by
    change monomialIdeal K (exponentPowerFamily (finiteRowFamily n (graphEdgeLattice H)) 1)=_
    rw [finitePowerFamily_ideal,pow_one,mixedRowPowerFamily_ideal,powerProduct_unit]
    rw [initialColumnGraph_lattice]
    rfl
  calc
    _ = (haveI := l₀; graphBinomialBetti (K := K) H 1 p q) := by
      apply ordinaryIdealBettiNumber_presentation (finiteVariableLinearOrder n) l₀
      change powerProduct J (Finsupp.single i 1)=(graphBinomialIdeal H)^1
      rw [powerProduct_unit,pow_one]
      rfl
    _ = (haveI := l₀; graphMonomialBetti (K := K) H 1 p q) := by
      letI := l₀
      exact intervalGraph_betti_eq H (initialColumnGraph_interval G hG (c i.down)) 1 p q
    _ = (haveI := l₀; ordinaryMonomialBettiNumber (k := K) C q p) := by
      letI := l₀
      exact canonicalMonomialBettiNumber_eq graphLexOrder C
        (monomialIdeal_ordinary_homogeneous C) q p
    _ = _ := ordinaryMonomialBettiNumber_presentation l₀
      (finiteVariableLinearOrder n) graphLexOrder C B hI q p

/-- Integer-graded Betti numbers of the literal product of graph-prefix
binomial ideals, defined through its actual derived Tor. -/
def graphPrefixMixedBettiNumber (m : ULift.{u} (Fin r) →₀ ℕ) (p : ℕ) (q : ℤ) : ℕ :=
  mixedIntegerPowerBettiNumber n E graphLexOrder J (graphPrefixMixed_initial G hG c hc)
    (graphPrefixIdeals_homogeneous G c) m p q

theorem initialColumnPrefix_graph_mixed_betti
    (m : ULift.{u} (Fin r) →₀ ℕ) (p : ℕ) (q : ℤ) :
    graphPrefixMixedBettiNumber (K := K) G hG c hc m p q=
      mixedIntegerMonomialBettiNumber (K := K) n E graphLexOrder m p q :=
  corollary57_betti n E hE J (graphPrefixIdeals_homogeneous G c) graphLexOrder
    (graphPrefixIdeals_mono G c hc) (graphPrefixIdeals_initial G hG c)
    (graphPrefixMixed_first_betti G hG c hc) m p q

theorem initialColumnPrefix_graph_mixed_field_independent
    (L : Type u) [Field L] (m : ULift.{u} (Fin r) →₀ ℕ) (p : ℕ) (q : ℤ) :
    graphPrefixMixedBettiNumber (K := K) G hG c hc m p q=
      graphPrefixMixedBettiNumber (K := L) G hG c hc m p q := by
  rw [initialColumnPrefix_graph_mixed_betti G hG c hc,
    initialColumnPrefix_graph_mixed_betti G hG c hc]
  exact initialColumnPrefix_mixed_integer_monomial_field_independent
    (graphEdgeLattice_unitInterval G hG) c hc graphLexOrder L m p q

include hG hc in
theorem initialColumnPrefix_graph_ideal_identities (m : ULift.{u} (Fin r) →₀ ℕ) :
    powerProduct J m=(⨅ i,(J i)^prefixExponent m i) ∧
    powerProduct (coloredIdeals (k := K) n E) m=
      (⨅ i,(coloredIdeals (k := K) n E i)^prefixExponent m i) ∧
    FourPapers.initialIdeal graphLexOrder (powerProduct J m)=
      powerProduct (coloredIdeals (k := K) n E) m :=
  corollary57_ideal_identities J E graphLexOrder hE
    (graphPrefixIdeals_mono G c hc) (graphPrefixIdeals_initial G hG c) m

include hG hc in
theorem initialColumnPrefix_graph_generation :
    Algebra.adjoin K (selectedHomologyClasses (MixedTransfer.idealReesKoszulDGA J)
      (MixedTransfer.Auxiliary.selectedPiece graphLexOrder J (canonicalMixedGenerators n J)
        (canonicalMixedGroebner n graphLexOrder J) (canonicalMixedUnitLeading n graphLexOrder J)
        (coordinateUnitDegrees (r := r))))=⊤ :=
  corollary57_generation n E hE J (graphPrefixIdeals_homogeneous G c) graphLexOrder
    (graphPrefixIdeals_mono G c hc) (graphPrefixIdeals_initial G hG c)
    (graphPrefixMixed_first_betti G hG c hc)

end FourPapers.Sublattice

#print axioms FourPapers.Sublattice.initialColumnPrefix_graph_mixed_betti
#print axioms FourPapers.Sublattice.initialColumnPrefix_graph_mixed_field_independent
#print axioms FourPapers.Sublattice.initialColumnPrefix_graph_ideal_identities

end
end
end

end
