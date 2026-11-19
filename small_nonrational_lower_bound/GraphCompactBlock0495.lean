module
prelude
import GraphInputsRow29Part00061Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0495
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨(29, 11453203513344), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00061.record000_result⟩)
 (.leaf ⟨(29, 11454747017472), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00061.record001_result⟩))
 (.branch 3
 (.leaf ⟨(29, 11455089868800), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00061.record002_result⟩)
 (.leaf ⟨(29, 11455283888128), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00061.record003_result⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨(29, 11461256577152), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00061.record004_result⟩)
 (.leaf ⟨(29, 11463336951936), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00061.record005_result⟩))
 (.branch 7
 (.leaf ⟨(29, 11471926886400), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00061.record006_result⟩)
 (.leaf ⟨(29, 11472063168512), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00061.record007_result⟩))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (21360 + i))) 0 8 :=
  interval_of_check _ 0 8 (by decide +kernel)

public theorem complete : Block 21360 21368 :=
  block_of_table results 21360 8 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0495
