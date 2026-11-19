module
prelude
import GraphInputsRow31Part00144Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0932
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 2
 (.branch 1
 (.leaf ⟨(31, 30383815000064), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00144.record000_result⟩)
 (.leaf ⟨(31, 30386935562240), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00144.record001_result⟩))
 (.branch 3
 (.leaf ⟨(31, 30442728327424), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00144.record002_result⟩)
 (.branch 4
 (.leaf ⟨(31, 30511464988800), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00144.record003_result⟩)
 (.leaf ⟨(31, 30516028375040), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00144.record004_result⟩))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (26597 + i))) 0 5 :=
  interval_of_check _ 0 5 (by decide +kernel)

public theorem complete : Block 26597 26602 :=
  block_of_table results 26597 5 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0932
