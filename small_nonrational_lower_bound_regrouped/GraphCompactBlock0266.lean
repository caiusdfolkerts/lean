module
prelude
import GraphInputsRow24Part00150Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0266
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 3
 (.branch 1
 (.leaf ⟨(24, 32513456611584), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00150.record000_result⟩)
 (.branch 2
 (.leaf ⟨(24, 32513464999936), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00150.record001_result⟩)
 (.leaf ⟨(24, 32513465520128), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00150.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(24, 32513506676992), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00150.record003_result⟩)
 (.branch 5
 (.leaf ⟨(24, 32514521571328), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00150.record004_result⟩)
 (.leaf ⟨(24, 32514547712000), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00150.record005_result⟩))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (11895 + i))) 0 6 :=
  interval_of_check _ 0 6 (by decide +kernel)

public theorem complete : Block 11895 11901 :=
  block_of_table results 11895 6 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0266
