module
prelude
import GraphInputsRow29Part00038Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0472
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 2
 (.branch 1
 (.leaf ⟨(29, 7560306425856), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00038.record000_result⟩)
 (.leaf ⟨(29, 7560417804544), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00038.record001_result⟩))
 (.branch 3
 (.leaf ⟨(29, 7560430094336), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00038.record002_result⟩)
 (.leaf ⟨(29, 7560562214912), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00038.record003_result⟩)))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (21036 + i))) 0 4 :=
  interval_of_check _ 0 4 (by decide +kernel)

public theorem complete : Block 21036 21040 :=
  block_of_table results 21036 4 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0472
