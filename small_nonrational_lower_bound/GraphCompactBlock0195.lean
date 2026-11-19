module
prelude
import GraphInputsRow24Part00079Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0195
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 3
 (.branch 1
 (.leaf ⟨(24, 24423434354688), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00079.record000_result⟩)
 (.branch 2
 (.leaf ⟨(24, 24423442677760), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00079.record001_result⟩)
 (.leaf ⟨(24, 24432076718336), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00079.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(24, 24432085106688), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00079.record003_result⟩)
 (.branch 5
 (.leaf ⟨(24, 24432208838912), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00079.record004_result⟩)
 (.leaf ⟨(24, 24432217227264), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00079.record005_result⟩))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (10600 + i))) 0 6 :=
  interval_of_check _ 0 6 (by decide +kernel)

public theorem complete : Block 10600 10606 :=
  block_of_table results 10600 6 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0195
