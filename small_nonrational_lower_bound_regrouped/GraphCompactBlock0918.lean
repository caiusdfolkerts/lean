module
prelude
import GraphInputsRow31Part00130Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0918
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 2
 (.branch 1
 (.leaf ⟨(31, 29181756833792), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00130.record000_result⟩)
 (.leaf ⟨(31, 29185108606976), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00130.record001_result⟩))
 (.branch 3
 (.leaf ⟨(31, 29189809930240), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00130.record002_result⟩)
 (.branch 4
 (.leaf ⟨(31, 29190078332928), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00130.record003_result⟩)
 (.leaf ⟨(31, 29197223362560), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00130.record004_result⟩))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (26547 + i))) 0 5 :=
  interval_of_check _ 0 5 (by decide +kernel)

public theorem complete : Block 26547 26552 :=
  block_of_table results 26547 5 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0918
