module
public import shared_results.part011
public import graph_results.closed_graph_ideal_leading
public import graph_results.closed_graph_rees_generation
public import shared_results.part019_finite_rees_koszul_equiv
public import graph_results.ideal_power_filtered_coordinate_transport

set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

@[expose] public section

/- BEGIN EXACT BODY: FourPapers.Sublattice.ClosedGraphMultiplicativeLifting -/
section

/-! # Actual parameter-ideal cycle lifting in every power

All inputs have already been proved for the literal parameter ideal: its
monic product Gröbner bases, their diagonal-weight tails, the first-power
coordinate lifts, and integral monomial Rees homology generation.
-/

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 20000
set_option synthInstance.maxHeartbeats 5000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace FourPapers.Sublattice

open Classical CommAlg CommAlg.Polymatroid MvPolynomial FilteredHomology
open scoped Pointwise

universe u
variable {k : Type u} [CommRing k] [IsDomain k]
  {N : ℕ} {G : SimpleGraph (Fin N)}

/-- Every leading coordinate cycle in every power of the actual graph
parameter ideal lifts over its original domain. This includes ℤ[z]. -/
theorem intervalGraph_parameter_power_coordinate_lifts (hG : IntervalLabeling G)
    (t : k) (ht : t≠0) (s p : ℕ) :
    let P := graphParameterPowerQuotientData t ht hG s
    LiftsCycles (actualIdealCoordinateFiltration P graphDiagonalWeight p)
      (actualIdealCoordinateFiltration P graphDiagonalWeight p.pred)
      (actualIdealPreviousDifferential P.ideal p) := by
  let J := graphParameterIdeal t G
  let I := finiteSublatticeIdeal (GraphRows N) (k:=k) (graphEdgeLattice G)
  let B := fun r : ℕ => graphParameterGenerators t G ^ r
  have hB : ∀ r, graphLexOrder.IsGroebnerBasis (B r) (J^r) :=
    closedGraph_parameter_power_groebner t ht hG
  have hu : ∀ r f, f∈B r → f≠0 → IsUnit (graphLexOrder.leadingCoeff f) :=
    graphParameterProducts_unit_leading t ht G
  have hi : ∀ r, initialIdealForBasis graphLexOrder (J^r)=I^r :=
    closedGraph_parameter_power_initial t ht hG
  have htails : ∀ r f, f∈B r → f≠0 →
      ∀ a∈(monomial (graphLexOrder.degree f) 1-f).support,
        Finsupp.weight graphDiagonalWeight a <
          Finsupp.weight graphDiagonalWeight (graphLexOrder.degree f) :=
    graphParameterProducts_weight_tails t ht G
  have hgen := initialReesKoszulHomology_generated_of_finite_generation (K:=k)
    (graphEdgeLattice G) graphLexOrder J hi B hB hu (graphEdgeLattice_closed hG)
      (closedGraph_reesKoszulHomology_generated_in_degree_one (k:=k) hG)
  have hfirst : ∀ r, LiftsCycles
      (powerCoordinateFiltration graphLexOrder J B hB hu graphDiagonalWeight 1 r)
      (powerCoordinateFiltration graphLexOrder J B hB hu graphDiagonalWeight 1 r.pred)
      (powerPreviousDifferential J 1 r) := by
    intro r
    have hP : graphParameterPowerQuotientData t ht hG 1 =
        graphParameterQuotientData t ht G (intervalLabeling_closed hG) := by
      unfold graphParameterPowerQuotientData graphParameterQuotientData
      simp only [pow_one, exponentPowerFamily_one]
    have hf := intervalGraph_parameter_ideal_coordinate_lifts hG t ht r
    rw [← hP] at hf
    apply (nativePowerCoordinateLifts_iff graphLexOrder J B hB hu
      graphDiagonalWeight 1 r).mp
    simpa only [nativePowerCoordinateFiltration, nativePowerCoefficientBasis,
      actualIdealCoordinateFiltration, actualIdealCoefficientBasis, actualIdealDegree,
      graphParameterPowerQuotientData, J, B] using! hf
  have hh := all_power_coordinate_lifts graphLexOrder J B hB hu I hi graphDiagonalWeight
    htails hgen hfirst s p
  have hnative := (nativePowerCoordinateLifts_iff graphLexOrder J B hB hu
    graphDiagonalWeight s p).mpr hh
  simpa only [nativePowerCoordinateFiltration, nativePowerCoefficientBasis,
    actualIdealCoordinateFiltration, actualIdealCoefficientBasis, actualIdealDegree,
    graphParameterPowerQuotientData, J, B] using! hnative

end FourPapers.Sublattice

end
end
end


end
