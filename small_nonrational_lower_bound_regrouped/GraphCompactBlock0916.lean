module
prelude
import GraphInputsRow31Part00128Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0916
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 2
 (.branch 1
 (.leaf ⟨(31, 28971974524928), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00128.record000_result⟩)
 (.leaf ⟨(31, 28976135274496), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00128.record001_result⟩))
 (.branch 3
 (.leaf ⟨(31, 28976399515648), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00128.record002_result⟩)
 (.leaf ⟨(31, 29177596084224), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00128.record003_result⟩)))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (26541 + i))) 0 4 :=
  interval_of_check _ 0 4 (by decide +kernel)

public theorem complete : Block 26541 26545 :=
  block_of_table results 26541 4 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0916
