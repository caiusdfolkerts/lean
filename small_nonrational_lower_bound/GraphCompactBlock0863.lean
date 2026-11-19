module
prelude
import GraphInputsRow31Part00075Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0863
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 1
 (.leaf ⟨(31, 14299602886656), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00075.record000_result⟩)
 (.branch 2
 (.leaf ⟨(31, 14303895756800), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00075.record001_result⟩)
 (.leaf ⟨(31, 14347373936896), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00075.record002_result⟩)))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (26067 + i))) 0 3 :=
  interval_of_check _ 0 3 (by decide +kernel)

public theorem complete : Block 26067 26070 :=
  block_of_table results 26067 3 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0863
