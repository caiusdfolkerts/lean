module
public import shared_results.part003
public import shared_results.part002

set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

@[expose] public section

/- BEGIN EXACT BODY: FourPapers.Common.DeformationRetractTransport -/
section

/-!
# Coordinate transport and scalar restriction of actual retracts

The source and target transport maps are defined in `DeformationTransport`.
This module re-exports them together with scalar restriction, so augmented
Koszul families use the same literal maps as the Čech-complex constructions.
-/

end


end
