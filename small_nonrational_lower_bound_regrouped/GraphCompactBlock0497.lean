module
prelude
import GraphInputsRow29Part00063Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0497
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(29, 11961085493248), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00063.record000_result⟩)
 (.branch 2
 (.leaf ⟨(29, 11961217613824), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00063.record001_result⟩)
 (.leaf ⟨(29, 11963937652736), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00063.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(29, 11963945975808), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00063.record003_result⟩)
 (.branch 5
 (.leaf ⟨(29, 11966921867520), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00063.record004_result⟩)
 (.leaf ⟨(29, 11967198658560), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00063.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(29, 11967458738176), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00063.record006_result⟩)
 (.branch 8
 (.leaf ⟨(29, 11975511801984), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00063.record007_result⟩)
 (.leaf ⟨(29, 11982993375360), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00063.record008_result⟩)))
 (.branch 11
 (.branch 10
 (.leaf ⟨(29, 11984101736448), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00063.record009_result⟩)
 (.leaf ⟨(29, 11984238018560), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00063.record010_result⟩))
 (.branch 12
 (.leaf ⟨(29, 11995864662272), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00063.record011_result⟩)
 (.leaf ⟨(29, 11996133130240), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00063.record012_result⟩)))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (21398 + i))) 0 13 :=
  interval_of_check _ 0 13 (by decide +kernel)

public theorem complete : Block 21398 21411 :=
  block_of_table results 21398 13 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0497
