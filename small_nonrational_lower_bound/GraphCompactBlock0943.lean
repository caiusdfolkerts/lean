module
prelude
import GraphInputsRow31Part00155Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0943
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 3
 (.branch 1
 (.leaf ⟨(31, 30915174736128), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00155.record000_result⟩)
 (.branch 2
 (.leaf ⟨(31, 30915245965312), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00155.record001_result⟩)
 (.leaf ⟨(31, 30915980951552), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00155.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(31, 30969004359680), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00155.record003_result⟩)
 (.branch 5
 (.leaf ⟨(31, 30969541165056), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00155.record004_result⟩)
 (.leaf ⟨(31, 30977590099968), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00155.record005_result⟩))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (26656 + i))) 0 6 :=
  interval_of_check _ 0 6 (by decide +kernel)

public theorem complete : Block 26656 26662 :=
  block_of_table results 26656 6 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0943
