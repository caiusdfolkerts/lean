module
prelude
import GraphInputsRow31Part00056Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0844
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 1
 (.leaf ⟨(31, 12017456906240), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00056.record000_result⟩)
 (.branch 2
 (.leaf ⟨(31, 12021881896960), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00056.record001_result⟩)
 (.leaf ⟨(31, 12142275788800), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00056.record002_result⟩)))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (25931 + i))) 0 3 :=
  interval_of_check _ 0 3 (by decide +kernel)

public theorem complete : Block 25931 25934 :=
  block_of_table results 25931 3 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0844
