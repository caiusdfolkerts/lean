module
prelude
import GraphInputsRow31Part00053Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0841
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 1
 (.leaf ⟨(31, 11738955120640), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00053.record000_result⟩)
 (.leaf ⟨(31, 11742579064832), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00053.record001_result⟩))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (25919 + i))) 0 2 :=
  interval_of_check _ 0 2 (by decide +kernel)

public theorem complete : Block 25919 25921 :=
  block_of_table results 25919 2 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0841
