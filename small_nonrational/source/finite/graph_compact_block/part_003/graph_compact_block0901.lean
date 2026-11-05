module
prelude
import GraphInputsRow31Part00113Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0901
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 2
 (.branch 1
 (.leaf ⟨(31, 25917451665408), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00113.record000_result⟩)
 (.leaf ⟨(31, 25925773164544), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00113.record001_result⟩))
 (.branch 3
 (.leaf ⟨(31, 25926301646848), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00113.record002_result⟩)
 (.leaf ⟨(31, 25933054476288), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00113.record003_result⟩)))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (26439 + i))) 0 4 :=
  interval_of_check _ 0 4 (by decide +kernel)

public theorem complete : Block 26439 26443 :=
  block_of_table results 26439 4 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0901
