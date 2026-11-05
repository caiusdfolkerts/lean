module
prelude
import GraphInputsRow31Part00151Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0939
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 2
 (.branch 1
 (.leaf ⟨(31, 30839549198336), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00151.record000_result⟩)
 (.leaf ⟨(31, 30839611097088), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00151.record001_result⟩))
 (.branch 3
 (.leaf ⟨(31, 30842965991424), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00151.record002_result⟩)
 (.leaf ⟨(31, 30857478283520), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00151.record003_result⟩)))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (26631 + i))) 0 4 :=
  interval_of_check _ 0 4 (by decide +kernel)

public theorem complete : Block 26631 26635 :=
  block_of_table results 26631 4 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0939
