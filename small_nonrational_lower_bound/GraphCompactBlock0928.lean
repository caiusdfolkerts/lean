module
prelude
import GraphInputsRow31Part00140Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0928
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.leaf ⟨(31, 30242744303616), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00140.record000_result⟩)

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (26585 + i))) 0 1 :=
  interval_of_check _ 0 1 (by decide +kernel)

public theorem complete : Block 26585 26586 :=
  block_of_table results 26585 1 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0928
