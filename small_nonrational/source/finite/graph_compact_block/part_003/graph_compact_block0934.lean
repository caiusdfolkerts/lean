module
prelude
import GraphInputsRow31Part00146Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0934
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 2
 (.branch 1
 (.leaf ⟨(31, 30789727166464), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00146.record000_result⟩)
 (.leaf ⟨(31, 30789949989120), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00146.record001_result⟩))
 (.branch 3
 (.leaf ⟨(31, 30791997333760), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00146.record002_result⟩)
 (.leaf ⟨(31, 30792005722112), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00146.record003_result⟩)))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (26610 + i))) 0 4 :=
  interval_of_check _ 0 4 (by decide +kernel)

public theorem complete : Block 26610 26614 :=
  block_of_table results 26610 4 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0934
