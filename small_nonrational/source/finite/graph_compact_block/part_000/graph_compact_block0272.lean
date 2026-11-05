module
prelude
import GraphInputsRow24Part00156Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0272
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 2
 (.branch 1
 (.leaf ⟨(24, 32781069721600), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00156.record000_result⟩)
 (.leaf ⟨(24, 32782411792640), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00156.record001_result⟩))
 (.branch 3
 (.leaf ⟨(24, 32783216935424), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00156.record002_result⟩)
 (.branch 4
 (.leaf ⟨(24, 32787797647616), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00156.record003_result⟩)
 (.leaf ⟨(24, 32787881328640), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00156.record004_result⟩))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (11947 + i))) 0 5 :=
  interval_of_check _ 0 5 (by decide +kernel)

public theorem complete : Block 11947 11952 :=
  block_of_table results 11947 5 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0272
