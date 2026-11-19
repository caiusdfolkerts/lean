module
prelude
import GraphInputsRow31Part00163Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0951
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 1
 (.leaf ⟨(31, 32042135846912), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00163.record000_result⟩)
 (.branch 2
 (.leaf ⟨(31, 32042201907200), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00163.record001_result⟩)
 (.leaf ⟨(31, 32044785664000), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00163.record002_result⟩)))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (26718 + i))) 0 3 :=
  interval_of_check _ 0 3 (by decide +kernel)

public theorem complete : Block 26718 26721 :=
  block_of_table results 26718 3 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0951
