module
prelude
import GraphInputsRow29Part00030Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0464
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 1
 (.leaf ⟨(29, 6986166960896), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00030.record000_result⟩)
 (.branch 2
 (.leaf ⟨(29, 6986447978496), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00030.record001_result⟩)
 (.leaf ⟨(29, 6988528353280), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00030.record002_result⟩)))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (20944 + i))) 0 3 :=
  interval_of_check _ 0 3 (by decide +kernel)

public theorem complete : Block 20944 20947 :=
  block_of_table results 20944 3 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0464
