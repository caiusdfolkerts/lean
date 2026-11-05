module
prelude
import GraphInputsRow31Part00145Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0933
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨(31, 30524332707840), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00145.record000_result⟩)
 (.leaf ⟨(31, 30580167280768), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00145.record001_result⟩))
 (.branch 3
 (.leaf ⟨(31, 30717606234112), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00145.record002_result⟩)
 (.leaf ⟨(31, 30717623140352), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00145.record003_result⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨(31, 30789649596672), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00145.record004_result⟩)
 (.leaf ⟨(31, 30789653823488), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00145.record005_result⟩))
 (.branch 7
 (.leaf ⟨(31, 30789715656960), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00145.record006_result⟩)
 (.leaf ⟨(31, 30789719883776), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00145.record007_result⟩))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (26602 + i))) 0 8 :=
  interval_of_check _ 0 8 (by decide +kernel)

public theorem complete : Block 26602 26610 :=
  block_of_table results 26602 8 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0933
