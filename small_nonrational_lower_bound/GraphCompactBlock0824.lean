module
prelude
import GraphInputsRow31Part00036Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0824
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 1
 (.leaf ⟨(31, 7562502144000), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00036.record000_result⟩)
 (.branch 2
 (.leaf ⟨(31, 7562774708224), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00036.record001_result⟩)
 (.leaf ⟨(31, 7564855083008), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00036.record002_result⟩)))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (25786 + i))) 0 3 :=
  interval_of_check _ 0 3 (by decide +kernel)

public theorem complete : Block 25786 25789 :=
  block_of_table results 25786 3 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0824
