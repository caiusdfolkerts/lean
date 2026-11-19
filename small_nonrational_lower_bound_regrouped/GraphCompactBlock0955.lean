module
prelude
import GraphInputsRow31Part00167Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0955
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 2
 (.branch 1
 (.leaf ⟨(31, 32847910013184), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00167.record000_result⟩)
 (.leaf ⟨(31, 32919313711104), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00167.record001_result⟩))
 (.branch 3
 (.leaf ⟨(31, 32991020646400), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00167.record002_result⟩)
 (.leaf ⟨(31, 32991289049088), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00167.record003_result⟩)))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (26738 + i))) 0 4 :=
  interval_of_check _ 0 4 (by decide +kernel)

public theorem complete : Block 26738 26742 :=
  block_of_table results 26738 4 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0955
