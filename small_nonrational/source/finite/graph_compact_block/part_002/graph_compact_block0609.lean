module
prelude
import GraphInputsRow29Part00175Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0609
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨(29, 25844697858048), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00175.record000_result⟩)
 (.leaf ⟨(29, 25848222646528), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00175.record001_result⟩))
 (.branch 3
 (.leaf ⟨(29, 25848759517184), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00175.record002_result⟩)
 (.leaf ⟨(29, 25848767840256), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00175.record003_result⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨(29, 25848858607616), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00175.record004_result⟩)
 (.leaf ⟨(29, 25851442299136), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00175.record005_result⟩))
 (.branch 7
 (.leaf ⟨(29, 25856812548352), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00175.record006_result⟩)
 (.branch 8
 (.leaf ⟨(29, 25857180106752), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00175.record007_result⟩)
 (.leaf ⟨(29, 25857353580544), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00175.record008_result⟩)))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (22790 + i))) 0 9 :=
  interval_of_check _ 0 9 (by decide +kernel)

public theorem complete : Block 22790 22799 :=
  block_of_table results 22790 9 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0609
