module
prelude
import GraphInputsRow31Part00069Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0857
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 2
 (.branch 1
 (.leaf ⟨(31, 13350046015488), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00069.record000_result⟩)
 (.leaf ⟨(31, 13350178136064), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00069.record001_result⟩))
 (.branch 3
 (.leaf ⟨(31, 13350235808000), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00069.record002_result⟩)
 (.branch 4
 (.leaf ⟨(31, 13351309025536), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00069.record003_result⟩)
 (.leaf ⟨(31, 13353859162144), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00069.record004_result⟩))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (26016 + i))) 0 5 :=
  interval_of_check _ 0 5 (by decide +kernel)

public theorem complete : Block 26016 26021 :=
  block_of_table results 26016 5 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0857
