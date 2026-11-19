module
prelude
import GraphInputsRow29Part00145Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0579
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨(29, 24381189275648), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00145.record000_result⟩)
 (.leaf ⟨(29, 24414810833152), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00145.record001_result⟩))
 (.branch 3
 (.leaf ⟨(29, 24417694384672), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00145.record002_result⟩)
 (.leaf ⟨(29, 24436493320192), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00145.record003_result⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨(29, 24437030125568), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00145.record004_result⟩)
 (.leaf ⟨(29, 24441190875136), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00145.record005_result⟩))
 (.branch 7
 (.leaf ⟨(29, 24443271249920), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00145.record006_result⟩)
 (.branch 8
 (.leaf ⟨(29, 24449239810048), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00145.record007_result⟩)
 (.leaf ⟨(29, 24449908736000), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00145.record008_result⟩)))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (22570 + i))) 0 9 :=
  interval_of_check _ 0 9 (by decide +kernel)

public theorem complete : Block 22570 22579 :=
  block_of_table results 22570 9 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0579
