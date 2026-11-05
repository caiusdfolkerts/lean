module
prelude
import GraphInputsRow29Part00102Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0536
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 1
 (.leaf ⟨(29, 17502528602112), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00102.record000_result⟩)
 (.branch 2
 (.leaf ⟨(29, 17523487604736), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00102.record001_result⟩)
 (.leaf ⟨(29, 17532081668096), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00102.record002_result⟩)))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (21958 + i))) 0 3 :=
  interval_of_check _ 0 3 (by decide +kernel)

public theorem complete : Block 21958 21961 :=
  block_of_table results 21958 3 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0536
