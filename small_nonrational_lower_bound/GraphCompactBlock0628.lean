module
prelude
import GraphInputsRow29Part00194Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0628
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf ⟨(29, 28082377392128), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00194.record000_result⟩)
 (.leaf ⟨(29, 28154324320256), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00194.record001_result⟩))
 (.branch 3
 (.leaf ⟨(29, 28193576779776), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00194.record002_result⟩)
 (.branch 4
 (.leaf ⟨(29, 28193585102848), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00194.record003_result⟩)
 (.leaf ⟨(29, 28195118661632), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00194.record004_result⟩))))
 (.branch 7
 (.branch 6
 (.leaf ⟨(29, 28231625343488), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00194.record005_result⟩)
 (.leaf ⟨(29, 28299816337408), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00194.record006_result⟩))
 (.branch 8
 (.leaf ⟨(29, 28300344819712), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00194.record007_result⟩)
 (.branch 9
 (.leaf ⟨(29, 28308666318848), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00194.record008_result⟩)
 (.leaf ⟨(29, 28315126087808), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00194.record009_result⟩)))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (22956 + i))) 0 10 :=
  interval_of_check _ 0 10 (by decide +kernel)

public theorem complete : Block 22956 22966 :=
  block_of_table results 22956 10 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0628
