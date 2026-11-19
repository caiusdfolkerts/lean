module
public import graph_foundation.part014
public import shared_results.part018_closed_graph_parameter_powers

set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

@[expose] public section

/- BEGIN EXACT BODY: FourPapers.Sublattice.ClosedGraphIdealLeading -/
section

/-! # The original graph-power Gröbner data

The generic ideal-to-initial coordinate comparison is re-exported from
`ActualIdealLeading`; this file supplies only the graph specialization.
-/

section
set_option autoImplicit false
set_option maxHeartbeats 20000
set_option synthInstance.maxHeartbeats 5000
noncomputable section
namespace FourPapers.Sublattice
open Classical CategoryTheory CommAlg CommAlg.Koszul CommAlg.Polymatroid MvPolynomial
open scoped Pointwise
universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [CommRing k] [Nontrivial k]

section GraphPowers
variable [IsDomain k] {N : ℕ} {G : SimpleGraph (Fin N)}

/-- The stored data concern the literal power, with its proved monic
product Gröbner basis and literal monomial-power complement. -/
def graphParameterPowerQuotientData (t : k) (ht : t ≠ 0)
    (hG : IntervalLabeling G) (s : ℕ) :
    QuotientGroebnerData (FiniteVariable.{u} (GraphRows N)) k where
  order := graphLexOrder
  ideal := graphParameterIdeal t G ^ s
  generators := graphParameterGenerators t G ^ s
  groebner := closedGraph_parameter_power_groebner t ht hG s
  unitLeading := graphParameterProducts_unit_leading t ht G s
  family := exponentPowerFamily (finiteRowFamily (GraphRows N) (graphEdgeLattice G)) s
  standard := graphParameterPower_standardMonomials t ht hG s

end GraphPowers
end FourPapers.Sublattice

end
end
end


end
