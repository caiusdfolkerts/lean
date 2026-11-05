module
prelude
import GraphInputsRow24Part00155Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0271
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 2
 (.branch 1
 (.leaf ⟨(24, 32780360613888), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00155.record000_result⟩)
 (.leaf ⟨(24, 32780550471680), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00155.record001_result⟩))
 (.branch 3
 (.leaf ⟨(24, 32780558794752), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00155.record002_result⟩)
 (.leaf ⟨(24, 32780600016896), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00155.record003_result⟩)))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (11943 + i))) 0 4 :=
  interval_of_check _ 0 4 (by decide +kernel)

public theorem complete : Block 11943 11947 :=
  block_of_table results 11943 4 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0271
