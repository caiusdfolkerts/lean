module
public import graph_foundation.part014
public import shared_results.part020_monomial_ordinary_homology

set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

@[expose] public section

/- BEGIN EXACT BODY: FourPapers.Common.ThreeTermHomologyEquiv -/
section

/-!
# Homology under three actual commuting linear equivalences

The common three-term equivalence has a single implementation in
`ClosedGraphHomologyDecomposition`. This compatibility module keeps the
historical name for its boundary-range lemma without redeclaring either
of the equivalences.
-/

section
namespace FourPapers.FilteredHomology

alias threeTermCyclesEquiv_range := threeTermCyclesEquiv_boundaries

end FourPapers.FilteredHomology

end
end


end
