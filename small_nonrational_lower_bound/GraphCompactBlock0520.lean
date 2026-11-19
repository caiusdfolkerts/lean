module
prelude
import GraphInputsRow29Part00086Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0520
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf ⟨(29, 14616457379840), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00086.record000_result⟩)
 (.leaf ⟨(29, 14616579015424), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00086.record001_result⟩))
 (.branch 3
 (.leaf ⟨(29, 14621748527104), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00086.record002_result⟩)
 (.branch 4
 (.leaf ⟨(29, 14623428378624), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00086.record003_result⟩)
 (.leaf ⟨(29, 14623700942848), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00086.record004_result⟩))))
 (.branch 8
 (.branch 6
 (.leaf ⟨(29, 14623965184000), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00086.record005_result⟩)
 (.branch 7
 (.leaf ⟨(29, 14663823655456), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00086.record006_result⟩)
 (.leaf ⟨(29, 14751207849984), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00086.record007_result⟩)))
 (.branch 9
 (.leaf ⟨(29, 14759793590272), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00086.record008_result⟩)
 (.branch 10
 (.leaf ⟨(29, 14760462516224), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00086.record009_result⟩)
 (.leaf ⟨(29, 14768387653632), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00086.record010_result⟩)))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (21715 + i))) 0 11 :=
  interval_of_check _ 0 11 (by decide +kernel)

public theorem complete : Block 21715 21726 :=
  block_of_table results 21715 11 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0520
