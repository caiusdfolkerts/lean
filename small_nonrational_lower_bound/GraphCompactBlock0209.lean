module
prelude
import GraphInputsRow24Part00093Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0209
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 3
 (.branch 1
 (.leaf ⟨(24, 25153207803968), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00093.record000_result⟩)
 (.branch 2
 (.leaf ⟨(24, 25153631748096), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00093.record001_result⟩)
 (.leaf ⟨(24, 25153644036352), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00093.record002_result⟩)))
 (.branch 5
 (.branch 4
 (.leaf ⟨(24, 25153656326144), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00093.record003_result⟩)
 (.leaf ⟨(24, 25153763868672), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00093.record004_result⟩))
 (.branch 6
 (.leaf ⟨(24, 25153770110976), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00093.record005_result⟩)
 (.leaf ⟨(24, 25153778237696), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00093.record006_result⟩))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (10813 + i))) 0 7 :=
  interval_of_check _ 0 7 (by decide +kernel)

public theorem complete : Block 10813 10820 :=
  block_of_table results 10813 7 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0209
