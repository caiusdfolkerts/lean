module
prelude
import GraphInputsRow29Part00015Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0449
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨(29, 3853839794432), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00015.record000_result⟩)
 (.leaf ⟨(29, 3853967753472), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00015.record001_result⟩))
 (.branch 3
 (.leaf ⟨(29, 3853971915008), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00015.record002_result⟩)
 (.leaf ⟨(29, 3853971980288), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00015.record003_result⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨(29, 3854074646784), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00015.record004_result⟩)
 (.leaf ⟨(29, 3861859274768), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00015.record005_result⟩))
 (.branch 7
 (.leaf ⟨(29, 3866953257216), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00015.record006_result⟩)
 (.branch 8
 (.leaf ⟨(29, 3921595138304), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00015.record007_result⟩)
 (.leaf ⟨(29, 3921599299840), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00015.record008_result⟩)))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (20718 + i))) 0 9 :=
  interval_of_check _ 0 9 (by decide +kernel)

public theorem complete : Block 20718 20727 :=
  block_of_table results 20718 9 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0449
