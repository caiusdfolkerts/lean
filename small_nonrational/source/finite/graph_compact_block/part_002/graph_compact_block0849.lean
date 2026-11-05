module
prelude
import GraphInputsRow31Part00061Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0849
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 2
 (.branch 1
 (.leaf ⟨(31, 12792165826560), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00061.record000_result⟩)
 (.leaf ⟨(31, 12794707710208), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00061.record001_result⟩))
 (.branch 3
 (.leaf ⟨(31, 12794749583360), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00061.record002_result⟩)
 (.branch 4
 (.leaf ⟨(31, 12800214761472), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00061.record003_result⟩)
 (.leaf ⟨(31, 12800487325696), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00061.record004_result⟩))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (25961 + i))) 0 5 :=
  interval_of_check _ 0 5 (by decide +kernel)

public theorem complete : Block 25961 25966 :=
  block_of_table results 25961 5 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0849
