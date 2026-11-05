module
prelude
import GraphInputsRow29Part00255Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0689
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 1
 (.leaf ⟨(29, 32522910040064), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00255.record000_result⟩)
 (.leaf ⟨(29, 32523372462080), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00255.record001_result⟩))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (23393 + i))) 0 2 :=
  interval_of_check _ 0 2 (by decide +kernel)

public theorem complete : Block 23393 23395 :=
  block_of_table results 23393 2 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0689
