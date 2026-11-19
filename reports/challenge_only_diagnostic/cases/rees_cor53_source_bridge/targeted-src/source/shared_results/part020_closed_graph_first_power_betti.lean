module
public import graph_foundation.part014
public import shared_results.part020_actual_ideal_ordinary_monomial_homology

set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

@[expose] public section

/- BEGIN EXACT BODY: FourPapers.Sublattice.ClosedGraphFirstPowerBetti -/
section

/-! # The first-power graph comparison from actual cycle lifts

This field comparison uses only the established first-power parameter lifts.
The all-power criterion may then propagate it without invoking the separate
integral all-power freeness argument used for Theorem 9.1.
-/

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
noncomputable section

namespace FourPapers.Sublattice

open Classical CommAlg MvPolynomial
attribute [local instance] MvPolynomial.weightedGradedAlgebra
attribute [local instance] ordinaryPieceAddCommGroup ordinaryPieceModule
universe u
variable {K : Type u} [Field K] {N : ℕ} {G : SimpleGraph (Fin N)}

/-- All ordinary first-power Betti numbers, with the original ideal and
its genuine monomial Koszul model as coefficients. -/
theorem intervalGraph_parameter_first_betti_eq (hG : IntervalLabeling G)
    (t : K) (ht : t ≠ 0) (p q : ℕ) :
    let P := graphParameterQuotientData t ht G (intervalLabeling_closed hG)
    ordinaryIdealBettiNumber P (graphParameterIdeal_total_homogeneous t G) p q =
      ordinaryMonomialBettiNumber (k := K) P.family q p := by
  let P := graphParameterQuotientData t ht G (intervalLabeling_closed hG)
  change ordinaryIdealBettiNumber P (graphParameterIdeal_total_homogeneous t G) p q =
    ordinaryMonomialBettiNumber (k := K) P.family q p
  rw [ordinaryIdealBettiNumber_eq_finrank]
  exact (actualIdealOrdinaryHomology_finrank_eq_initial P
    (graphParameterIdeal_total_homogeneous t G) graphDiagonalWeight
    (graphParameterGenerators_weight_tails t ht G)
    (actualIdealPrevious_strictly_lowers_of_tails P graphDiagonalWeight
      (graphParameterGenerators_weight_tails t ht G))
    N graphDiagonalWeight_le (intervalGraph_parameter_ideal_coordinate_lifts hG t ht) q p).trans
      (initialActualIdealOrdinaryHomologyEquiv P q p).finrank_eq

end FourPapers.Sublattice

end
end
end


end
