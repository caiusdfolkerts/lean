module
prelude
import GraphInputsRow31Part00116Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0904
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 1
 (.leaf ⟨(31, 26432919060480), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00116.record000_result⟩)
 (.branch 2
 (.leaf ⟨(31, 26462708105216), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00116.record001_result⟩)
 (.leaf ⟨(31, 26466868854784), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00116.record002_result⟩)))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (26458 + i))) 0 3 :=
  interval_of_check _ 0 3 (by decide +kernel)

public theorem complete : Block 26458 26461 :=
  block_of_table results 26458 3 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0904
