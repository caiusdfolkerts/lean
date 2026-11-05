module
prelude
import GraphInputsRow29Part00241Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0675
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 2
 (.branch 1
 (.leaf ⟨(29, 31611253166112), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00241.record000_result⟩)
 (.leaf ⟨(29, 31619834978560), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00241.record001_result⟩))
 (.branch 3
 (.leaf ⟨(29, 31750614974720), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00241.record002_result⟩)
 (.leaf ⟨(29, 31785043951616), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00241.record003_result⟩)))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (23330 + i))) 0 4 :=
  interval_of_check _ 0 4 (by decide +kernel)

public theorem complete : Block 23330 23334 :=
  block_of_table results 23330 4 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0675
