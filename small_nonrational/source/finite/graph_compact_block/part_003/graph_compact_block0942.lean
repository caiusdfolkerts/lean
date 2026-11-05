module
prelude
import GraphInputsRow31Part00154Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0942
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨(31, 30875178246144), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00154.record000_result⟩)
 (.leaf ⟨(31, 30880849469696), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00154.record001_result⟩))
 (.branch 3
 (.leaf ⟨(31, 30900142407936), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00154.record002_result⟩)
 (.leaf ⟨(31, 30900687601664), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00154.record003_result⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨(31, 30900955906048), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00154.record004_result⟩)
 (.leaf ⟨(31, 30907139391488), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00154.record005_result⟩))
 (.branch 7
 (.leaf ⟨(31, 30908732309760), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00154.record006_result⟩)
 (.leaf ⟨(31, 30909537452544), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00154.record007_result⟩))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (26648 + i))) 0 8 :=
  interval_of_check _ 0 8 (by decide +kernel)

public theorem complete : Block 26648 26656 :=
  block_of_table results 26648 8 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0942
