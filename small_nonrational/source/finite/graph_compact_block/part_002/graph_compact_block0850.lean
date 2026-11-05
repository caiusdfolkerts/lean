module
prelude
import GraphInputsRow31Part00062Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0850
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 1
 (.leaf ⟨(31, 12800751566848), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00062.record000_result⟩)
 (.branch 2
 (.leaf ⟨(31, 12803335323648), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00062.record001_result⟩)
 (.leaf ⟨(31, 12804103340032), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00062.record002_result⟩)))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (25966 + i))) 0 3 :=
  interval_of_check _ 0 3 (by decide +kernel)

public theorem complete : Block 25966 25969 :=
  block_of_table results 25966 3 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0850
