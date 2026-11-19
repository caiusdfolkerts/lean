module
prelude
import GraphInputsRow24Part00142Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0258
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 3
 (.branch 1
 (.leaf ⟨(24, 32025986732096), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00142.record000_result⟩)
 (.branch 2
 (.leaf ⟨(24, 32026600210688), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00142.record001_result⟩)
 (.leaf ⟨(24, 32027077263360), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00142.record002_result⟩)))
 (.branch 5
 (.branch 4
 (.leaf ⟨(24, 32043780079616), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00142.record003_result⟩)
 (.leaf ⟨(24, 32044316884992), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00142.record004_result⟩))
 (.branch 6
 (.leaf ⟨(24, 32058795688192), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00142.record005_result⟩)
 (.leaf ⟨(24, 32059272740864), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00142.record006_result⟩))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (11799 + i))) 0 7 :=
  interval_of_check _ 0 7 (by decide +kernel)

public theorem complete : Block 11799 11806 :=
  block_of_table results 11799 7 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0258
