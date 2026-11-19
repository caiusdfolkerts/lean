module
prelude
import GraphInputsRow29Part00269Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0703
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 2
 (.branch 1
 (.leaf ⟨(29, 33719788437504), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00269.record000_result⟩)
 (.leaf ⟨(29, 33751530733568), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00269.record001_result⟩))
 (.branch 3
 (.leaf ⟨(29, 34088117371136), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00269.record002_result⟩)
 (.leaf ⟨(29, 34088253718528), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00269.record003_result⟩)))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (23453 + i))) 0 4 :=
  interval_of_check _ 0 4 (by decide +kernel)

public theorem complete : Block 23453 23457 :=
  block_of_table results 23453 4 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0703
