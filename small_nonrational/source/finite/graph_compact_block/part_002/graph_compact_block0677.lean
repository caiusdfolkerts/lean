module
prelude
import GraphInputsRow29Part00243Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0677
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 1
 (.leaf ⟨(29, 31819336581120), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00243.record000_result⟩)
 (.branch 2
 (.leaf ⟨(29, 31827930644480), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00243.record001_result⟩)
 (.leaf ⟨(29, 31828459126784), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00243.record002_result⟩)))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (23338 + i))) 0 3 :=
  interval_of_check _ 0 3 (by decide +kernel)

public theorem complete : Block 23338 23341 :=
  block_of_table results 23338 3 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0677
