module
public import graph_results.closed_graph_power_cycle_generation
public import shared_results.part010

set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

@[expose] public section

/- BEGIN EXACT BODY: FourPapers.Sublattice.ClosedGraphReesGeneration -/
section

/-! # Integral first-degree generation in the actual graph Rees algebra

The polynomial Rees algebra is the actual image inside `S[t]`. Its tensor
Koszul differential is the ordinary differential, as identified by
`reesKoszulTensorDGA_d`. The result below transports the proved all-power
product-cycle identity into that homology algebra over a coefficient domain.
-/

section
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 20000
set_option synthInstance.maxHeartbeats 20000
noncomputable section

namespace FourPapers.Sublattice
open Classical CommAlg CommAlg.Koszul CommAlg.Polymatroid
universe u
variable {k : Type u} [CommRing k] [IsDomain k]
  {N : ℕ} {G : SimpleGraph (Fin N)}

theorem closedGraph_reesCoordinateHomology_generated_in_degree_one (hG : IntervalLabeling G) :
    Algebra.adjoin k (firstReesClasses (k := k) (graphEdgeLattice_closed hG)) = ⊤ :=
  reesCoordinateHomology_generated_of_cycle_spanning (graphEdgeLattice_closed hG)
    (fun m hm α => closedGraph_powerFaceCycles_generated (k := k) hG m hm α)

/-- The integral graph version of the Rees homology generation theorem.
Every algebra generator is represented by an actual ordinary Koszul cycle
in literal Rees degree one. -/
theorem closedGraph_reesKoszulHomology_generated_in_degree_one (hG : IntervalLabeling G) :
    Algebra.adjoin k (actualFirstReesClasses (k := k) (graphEdgeLattice_closed hG)) = ⊤ :=
  reesKoszulHomology_generated_of_coordinate_generation (graphEdgeLattice_closed hG)
    (closedGraph_reesCoordinateHomology_generated_in_degree_one (k := k) hG)

end FourPapers.Sublattice

end
end
end


end
