module
prelude
import GraphInputsRow29Part00087Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0521
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 8
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨(29, 14768916135936), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00087.record000_result⟩)
 (.leaf ⟨(29, 14972532883456), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00087.record001_result⟩))
 (.branch 3
 (.leaf ⟨(29, 14973069688832), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00087.record002_result⟩)
 (.leaf ⟨(29, 15037494198272), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00087.record003_result⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨(29, 15075335405824), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00087.record004_result⟩)
 (.leaf ⟨(29, 15075410771968), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00087.record005_result⟩))
 (.branch 7
 (.leaf ⟨(29, 15110240206848), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00087.record006_result⟩)
 (.leaf ⟨(29, 15166343217152), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00087.record007_result⟩))))
 (.branch 12
 (.branch 10
 (.branch 9
 (.leaf ⟨(29, 15178552901632), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00087.record008_result⟩)
 (.leaf ⟨(29, 15212845531136), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00087.record009_result⟩))
 (.branch 11
 (.leaf ⟨(29, 15213580517376), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00087.record010_result⟩)
 (.leaf ⟨(29, 15247410724864), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00087.record011_result⟩)))
 (.branch 14
 (.branch 13
 (.leaf ⟨(29, 15258009796864), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00087.record012_result⟩)
 (.leaf ⟨(29, 15294655430656), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00087.record013_result⟩))
 (.branch 15
 (.leaf ⟨(29, 15303513735168), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00087.record014_result⟩)
 (.leaf ⟨(29, 15311835234304), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00087.record015_result⟩)))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (21726 + i))) 0 16 :=
  interval_of_check _ 0 16 (by decide +kernel)

public theorem complete : Block 21726 21742 :=
  block_of_table results 21726 16 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0521
