module
prelude
import GraphInputsRow24Part00153Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0269
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 3
 (.branch 1
 (.leaf ⟨(24, 32712769962240), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00153.record000_result⟩)
 (.branch 2
 (.leaf ⟨(24, 32712781991936), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00153.record001_result⟩)
 (.leaf ⟨(24, 32713178353664), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00153.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(24, 32715051639040), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00153.record003_result⟩)
 (.branch 5
 (.leaf ⟨(24, 32715060547584), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00153.record004_result⟩)
 (.leaf ⟨(24, 32715324788736), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00153.record005_result⟩))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (11928 + i))) 0 6 :=
  interval_of_check _ 0 6 (by decide +kernel)

public theorem complete : Block 11928 11934 :=
  block_of_table results 11928 6 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0269
