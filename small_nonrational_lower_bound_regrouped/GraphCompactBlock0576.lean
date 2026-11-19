module
prelude
import GraphInputsRow29Part00142Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0576
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 3
 (.branch 1
 (.leaf ⟨(29, 24242081005568), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00142.record000_result⟩)
 (.branch 2
 (.leaf ⟨(29, 24262832824448), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00142.record001_result⟩)
 (.leaf ⟨(29, 24263957446656), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00142.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(29, 24265022275840), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00142.record003_result⟩)
 (.branch 5
 (.leaf ⟨(29, 24268322643968), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00142.record004_result⟩)
 (.leaf ⟨(29, 24276439695360), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00142.record005_result⟩))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (22545 + i))) 0 6 :=
  interval_of_check _ 0 6 (by decide +kernel)

public theorem complete : Block 22545 22551 :=
  block_of_table results 22545 6 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0576
