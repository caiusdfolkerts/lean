module
prelude
import GraphInputsRow29Part00150Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0584
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 2
 (.branch 1
 (.leaf ⟨(29, 24646806208512), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00150.record000_result⟩)
 (.leaf ⟨(29, 24647343013888), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00150.record001_result⟩))
 (.branch 3
 (.leaf ⟨(29, 24648886583296), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00150.record002_result⟩)
 (.leaf ⟨(29, 24655664513024), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00150.record003_result⟩)))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (22605 + i))) 0 4 :=
  interval_of_check _ 0 4 (by decide +kernel)

public theorem complete : Block 22605 22609 :=
  block_of_table results 22605 4 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0584
