module
prelude
import GraphInputsRow31Part00050Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0838
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 2
 (.branch 1
 (.leaf ⟨(31, 10492642918656), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00050.record000_result⟩)
 (.leaf ⟨(31, 10493411000320), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00050.record001_result⟩))
 (.branch 3
 (.leaf ⟨(31, 10601399058432), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00050.record002_result⟩)
 (.leaf ⟨(31, 10639439299072), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00050.record003_result⟩)))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (25897 + i))) 0 4 :=
  interval_of_check _ 0 4 (by decide +kernel)

public theorem complete : Block 25897 25901 :=
  block_of_table results 25897 4 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0838
