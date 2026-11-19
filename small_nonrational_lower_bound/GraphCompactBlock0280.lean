module
prelude
import GraphInputsRow24Part00164Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0280
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 3
 (.branch 1
 (.leaf ⟨(24, 33613790904320), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00164.record000_result⟩)
 (.branch 2
 (.leaf ⟨(24, 33613823345408), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00164.record001_result⟩)
 (.leaf ⟨(24, 33677124313344), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00164.record002_result⟩)))
 (.branch 5
 (.branch 4
 (.leaf ⟨(24, 33678215413760), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00164.record003_result⟩)
 (.leaf ⟨(24, 33681335128320), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00164.record004_result⟩))
 (.branch 6
 (.leaf ⟨(24, 33682408604416), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00164.record005_result⟩)
 (.leaf ⟨(24, 33687073718272), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00164.record006_result⟩))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (12022 + i))) 0 7 :=
  interval_of_check _ 0 7 (by decide +kernel)

public theorem complete : Block 12022 12029 :=
  block_of_table results 12022 7 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0280
