module
prelude
import GraphInputsRow31Part00007Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0795
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 3
 (.branch 1
 (.leaf ⟨(31, 1255887872064), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00007.record000_result⟩)
 (.branch 2
 (.leaf ⟨(31, 1289050145024), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00007.record001_result⟩)
 (.leaf ⟨(31, 1289050210304), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00007.record002_result⟩)))
 (.branch 5
 (.branch 4
 (.leaf ⟨(31, 1289056436288), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00007.record003_result⟩)
 (.leaf ⟨(31, 1293468827649), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00007.record004_result⟩))
 (.branch 6
 (.leaf ⟨(31, 1325681147904), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00007.record005_result⟩)
 (.leaf ⟨(31, 1327817064704), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00007.record006_result⟩))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (25516 + i))) 0 7 :=
  interval_of_check _ 0 7 (by decide +kernel)

public theorem complete : Block 25516 25523 :=
  block_of_table results 25516 7 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0795
