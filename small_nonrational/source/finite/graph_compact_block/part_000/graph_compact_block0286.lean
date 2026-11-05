module
prelude
import GraphInputsRow24Part00170Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0286
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 3
 (.branch 1
 (.leaf ⟨(24, 34673556783104), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00170.record000_result⟩)
 (.branch 2
 (.leaf ⟨(24, 34673565106176), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00170.record001_result⟩)
 (.leaf ⟨(24, 34674076553216), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00170.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(24, 34674344886528), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00170.record003_result⟩)
 (.branch 5
 (.leaf ⟨(24, 34674382536704), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00170.record004_result⟩)
 (.leaf ⟨(24, 34674655100928), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00170.record005_result⟩))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (12095 + i))) 0 6 :=
  interval_of_check _ 0 6 (by decide +kernel)

public theorem complete : Block 12095 12101 :=
  block_of_table results 12095 6 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0286
