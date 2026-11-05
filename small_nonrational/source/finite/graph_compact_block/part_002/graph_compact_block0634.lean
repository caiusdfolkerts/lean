module
prelude
import GraphInputsRow29Part00200Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0634
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf ⟨(29, 28830523752448), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00200.record000_result⟩)
 (.leaf ⟨(29, 28830527913984), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00200.record001_result⟩))
 (.branch 3
 (.leaf ⟨(29, 28830639357952), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00200.record002_result⟩)
 (.branch 4
 (.leaf ⟨(29, 28838968950784), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00200.record003_result⟩)
 (.leaf ⟨(29, 28845018202240), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00200.record004_result⟩))))
 (.branch 7
 (.branch 6
 (.leaf ⟨(29, 28845201981440), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00200.record005_result⟩)
 (.leaf ⟨(29, 28866766704672), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00200.record006_result⟩))
 (.branch 8
 (.leaf ⟨(29, 28868824563840), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00200.record007_result⟩)
 (.branch 9
 (.leaf ⟨(29, 28868958765184), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00200.record008_result⟩)
 (.leaf ⟨(29, 28868964519936), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00200.record009_result⟩)))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (23004 + i))) 0 10 :=
  interval_of_check _ 0 10 (by decide +kernel)

public theorem complete : Block 23004 23014 :=
  block_of_table results 23004 10 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0634
