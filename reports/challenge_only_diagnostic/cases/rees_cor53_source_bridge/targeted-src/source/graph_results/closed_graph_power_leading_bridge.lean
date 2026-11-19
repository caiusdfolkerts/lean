module
public import shared_results.part020
public import graph_results.closed_graph_multiplicative_lifting

set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

@[expose] public section

/- BEGIN EXACT BODY: FourPapers.Sublattice.ClosedGraphPowerLeadingBridge -/
section

/-! # The associated differential for every actual graph parameter power -/

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 20000
set_option synthInstance.maxHeartbeats 5000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace FourPapers.Sublattice

open Classical MvPolynomial

universe u
variable {k : Type u} [CommRing k] [IsDomain k]
  {N : ℕ} {G : SimpleGraph (Fin N)}

theorem intervalGraph_parameter_power_previous_strictly_lowers
    (hG : IntervalLabeling G) (t : k) (ht : t≠0) (s p : ℕ)
    (a : ActualIdealIndex (graphParameterPowerQuotientData t ht hG s) p)
    (b : ActualIdealIndex (graphParameterPowerQuotientData t ht hG s) p.pred)
    (hweight : Finsupp.weight graphDiagonalWeight (actualIdealDegree a) ≤
      Finsupp.weight graphDiagonalWeight (actualIdealDegree b)) :
    (actualIdealCoefficientBasis (graphParameterPowerQuotientData t ht hG s) p.pred).repr
      (actualIdealPreviousDifferential (graphParameterPowerQuotientData t ht hG s).ideal p
        (actualIdealCoefficientBasis (graphParameterPowerQuotientData t ht hG s) p a) -
        initialActualIdealPrevious (graphParameterPowerQuotientData t ht hG s) p
          (actualIdealCoefficientBasis (graphParameterPowerQuotientData t ht hG s) p a)) b = 0 :=
  actualIdealPrevious_strictly_lowers_of_tails (graphParameterPowerQuotientData t ht hG s)
    graphDiagonalWeight (graphParameterProducts_weight_tails t ht G s) p a b hweight

end FourPapers.Sublattice

end
end
end


end
