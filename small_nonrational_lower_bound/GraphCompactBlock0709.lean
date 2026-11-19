module
prelude
import GraphInputsRow29Part00275Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0709
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 1
 (.leaf ⟨(29, 34124320739328), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00275.record000_result⟩)
 (.branch 2
 (.leaf ⟨(29, 34124589072640), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00275.record001_result⟩)
 (.leaf ⟨(29, 34124865863680), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00275.record002_result⟩)))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (23475 + i))) 0 3 :=
  interval_of_check _ 0 3 (by decide +kernel)

public theorem complete : Block 23475 23478 :=
  block_of_table results 23475 3 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0709
