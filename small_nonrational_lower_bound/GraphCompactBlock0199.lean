module
prelude
import GraphInputsRow24Part00083Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0199
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 2
 (.branch 1
 (.leaf ⟨(24, 24512798130176), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00083.record000_result⟩)
 (.leaf ⟨(24, 24513258471424), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00083.record001_result⟩))
 (.branch 3
 (.leaf ⟨(24, 24513326612480), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00083.record002_result⟩)
 (.branch 4
 (.leaf ⟨(24, 24515844245632), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00083.record003_result⟩)
 (.leaf ⟨(24, 24520021803008), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00083.record004_result⟩))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (10648 + i))) 0 5 :=
  interval_of_check _ 0 5 (by decide +kernel)

public theorem complete : Block 10648 10653 :=
  block_of_table results 10648 5 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0199
