module
prelude
import GraphInputsRow24Part00165Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0281
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 3
 (.branch 1
 (.leaf ⟨(24, 33742623145984), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00165.record000_result⟩)
 (.branch 2
 (.leaf ⟨(24, 33742631469056), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00165.record001_result⟩)
 (.leaf ⟨(24, 33742672691200), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00165.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(24, 33750423707648), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00165.record003_result⟩)
 (.branch 5
 (.leaf ⟨(24, 33750926893312), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00165.record004_result⟩)
 (.leaf ⟨(24, 33751530734080), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00165.record005_result⟩))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (12029 + i))) 0 6 :=
  interval_of_check _ 0 6 (by decide +kernel)

public theorem complete : Block 12029 12035 :=
  block_of_table results 12029 6 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0281
