module
prelude
import GraphInputsRow31Part00093Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0881
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 1
 (.leaf ⟨(31, 18580834893824), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00093.record000_result⟩)
 (.branch 2
 (.leaf ⟨(31, 18697649397824), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00093.record001_result⟩)
 (.leaf ⟨(31, 18701942267968), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00093.record002_result⟩)))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (26276 + i))) 0 3 :=
  interval_of_check _ 0 3 (by decide +kernel)

public theorem complete : Block 26276 26279 :=
  block_of_table results 26276 3 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0881
