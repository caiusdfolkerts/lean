module
prelude
import GraphInputsRow23Part00032Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0110
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 8
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨(23, 33099576508416), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00032.record000_result⟩)
 (.leaf ⟨(23, 33167417278464), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00032.record001_result⟩))
 (.branch 3
 (.leaf ⟨(23, 33204460388352), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00032.record002_result⟩)
 (.leaf ⟨(23, 33238827401216), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00032.record003_result⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨(23, 33241436258304), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00032.record004_result⟩)
 (.leaf ⟨(23, 33260382195744), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00032.record005_result⟩))
 (.branch 7
 (.leaf ⟨(23, 33262458650752), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00032.record006_result⟩)
 (.leaf ⟨(23, 33263550758912), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00032.record007_result⟩))))
 (.branch 12
 (.branch 10
 (.branch 9
 (.leaf ⟨(23, 33295746236416), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00032.record008_result⟩)
 (.leaf ⟨(23, 33295750397952), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00032.record009_result⟩))
 (.branch 11
 (.leaf ⟨(23, 33297807851648), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00032.record010_result⟩)
 (.leaf ⟨(23, 33298210357760), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00032.record011_result⟩)))
 (.branch 14
 (.branch 13
 (.leaf ⟨(23, 33579539103744), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00032.record012_result⟩)
 (.leaf ⟨(23, 33613831733248), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00032.record013_result⟩))
 (.branch 15
 (.leaf ⟨(23, 33682416992256), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00032.record014_result⟩)
 (.leaf ⟨(23, 33685463171072), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00032.record015_result⟩)))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (7685 + i))) 0 16 :=
  interval_of_check _ 0 16 (by decide +kernel)

public theorem complete : Block 7685 7701 :=
  block_of_table results 7685 16 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0110
