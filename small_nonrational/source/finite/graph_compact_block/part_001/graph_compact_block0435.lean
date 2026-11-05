module
prelude
import GraphInputsRow29Part00001Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0435
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf ⟨(29, 819139182592), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00001.record000_result⟩)
 (.leaf ⟨(29, 872562065664), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00001.record001_result⟩))
 (.branch 3
 (.leaf ⟨(29, 872562130944), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00001.record002_result⟩)
 (.branch 4
 (.leaf ⟨(29, 881286201472), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00001.record003_result⟩)
 (.leaf ⟨(29, 915645931648), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00001.record004_result⟩))))
 (.branch 8
 (.branch 6
 (.leaf ⟨(29, 938857267456), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00001.record005_result⟩)
 (.branch 7
 (.leaf ⟨(29, 938865655808), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00001.record006_result⟩)
 (.leaf ⟨(29, 1003281776896), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00001.record007_result⟩)))
 (.branch 9
 (.leaf ⟨(29, 1003290165248), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00001.record008_result⟩)
 (.branch 10
 (.leaf ⟨(29, 1003682300160), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00001.record009_result⟩)
 (.leaf ⟨(29, 1007583035392), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00001.record010_result⟩)))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (20491 + i))) 0 11 :=
  interval_of_check _ 0 11 (by decide +kernel)

public theorem complete : Block 20491 20502 :=
  block_of_table results 20491 11 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0435
