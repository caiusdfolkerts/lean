module
prelude
import GraphInputsRow31Part00102Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0890
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf ⟨(31, 22875134296064), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00102.record000_result⟩)
 (.leaf ⟨(31, 22875803222016), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00102.record001_result⟩))
 (.branch 3
 (.leaf ⟨(31, 22910161911808), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00102.record002_result⟩)
 (.branch 4
 (.leaf ⟨(31, 22978144305152), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00102.record003_result⟩)
 (.leaf ⟨(31, 23091380494400), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00102.record004_result⟩))))
 (.branch 7
 (.branch 6
 (.leaf ⟨(31, 23108569284864), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00102.record005_result⟩)
 (.leaf ⟨(31, 23382356140096), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00102.record006_result⟩))
 (.branch 8
 (.leaf ⟨(31, 23383682072576), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00102.record007_result⟩)
 (.branch 9
 (.leaf ⟨(31, 23390426513664), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00102.record008_result⟩)
 (.leaf ⟨(31, 23421264068608), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00102.record009_result⟩)))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (26352 + i))) 0 10 :=
  interval_of_check _ 0 10 (by decide +kernel)

public theorem complete : Block 26352 26362 :=
  block_of_table results 26352 10 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0890
