module
prelude
import GraphInputsRow29Part00234Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0668
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 1
 (.leaf ⟨(29, 31346328084480), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00234.record000_result⟩)
 (.branch 2
 (.leaf ⟨(29, 31414535913728), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00234.record001_result⟩)
 (.leaf ⟨(29, 31414808543232), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00234.record002_result⟩)))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (23286 + i))) 0 3 :=
  interval_of_check _ 0 3 (by decide +kernel)

public theorem complete : Block 23286 23289 :=
  block_of_table results 23286 3 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0668
