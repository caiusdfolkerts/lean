module
public import graph_foundation.part013
public import shared_results.part018_tensor_koszul_coefficient_equiv

set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

@[expose] public section

/- BEGIN EXACT BODY: FourPapers.Sublattice.ReesHomologyComplete -/
section

/-!
# Complete Rees homology generation

Compatibility entry point for the modular proof of the multiplicative assertion
of Theorem 1.2. The imported modules define the actual Rees image, identify its
Koszul differential and multiplication, and prove generation in Rees degree one.
Keeping one source for each declaration ensures all callers use the same proof.
-/

end


end
