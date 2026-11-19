module
prelude
import GraphInputsRow29Part00288Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0722
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 1
 (.leaf ⟨(29, 34674621546496), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00288.record000_result⟩)
 (.branch 2
 (.leaf ⟨(29, 34675150028800), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00288.record001_result⟩)
 (.leaf ⟨(29, 34681902858240), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00288.record002_result⟩)))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (23532 + i))) 0 3 :=
  interval_of_check _ 0 3 (by decide +kernel)

public theorem complete : Block 23532 23535 :=
  block_of_table results 23532 3 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0722
