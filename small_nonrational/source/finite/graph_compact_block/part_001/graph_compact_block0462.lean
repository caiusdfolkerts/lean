module
prelude
import GraphInputsRow29Part00028Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0462
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf ⟨(29, 6807055532288), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00028.record000_result⟩)
 (.leaf ⟨(29, 6823834877952), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00028.record001_result⟩))
 (.branch 3
 (.leaf ⟨(29, 6825520930816), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00028.record002_result⟩)
 (.branch 4
 (.leaf ⟨(29, 6839890673920), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00028.record003_result⟩)
 (.leaf ⟨(29, 6839899062272), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00028.record004_result⟩))))
 (.branch 7
 (.branch 6
 (.leaf ⟨(29, 6840138400000), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00028.record005_result⟩)
 (.leaf ⟨(29, 6840291197184), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00028.record006_result⟩))
 (.branch 8
 (.leaf ⟨(29, 6840295424000), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00028.record007_result⟩)
 (.branch 9
 (.leaf ⟨(29, 6840406802688), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00028.record008_result⟩)
 (.leaf ⟨(29, 6840419092480), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00028.record009_result⟩)))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (20921 + i))) 0 10 :=
  interval_of_check _ 0 10 (by decide +kernel)

public theorem complete : Block 20921 20931 :=
  block_of_table results 20921 10 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0462
