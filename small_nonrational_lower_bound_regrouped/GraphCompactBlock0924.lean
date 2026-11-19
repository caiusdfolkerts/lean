module
prelude
import GraphInputsRow31Part00136Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0924
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 1
 (.leaf ⟨(31, 29588314914816), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00136.record000_result⟩)
 (.branch 2
 (.leaf ⟨(31, 29596619767808), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00136.record001_result⟩)
 (.leaf ⟨(31, 29727217680384), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00136.record002_result⟩)))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (26573 + i))) 0 3 :=
  interval_of_check _ 0 3 (by decide +kernel)

public theorem complete : Block 26573 26576 :=
  block_of_table results 26573 3 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0924
