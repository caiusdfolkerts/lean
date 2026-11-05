module
prelude
import GraphInputsRow24Part00069Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0185
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 2
 (.branch 1
 (.leaf ⟨(24, 23437179371520), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00069.record000_result⟩)
 (.leaf ⟨(24, 23443618676736), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00069.record001_result⟩))
 (.branch 3
 (.leaf ⟨(24, 23451940175872), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00069.record002_result⟩)
 (.leaf ⟨(24, 23461361680384), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00069.record003_result⟩)))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (10340 + i))) 0 4 :=
  interval_of_check _ 0 4 (by decide +kernel)

public theorem complete : Block 10340 10344 :=
  block_of_table results 10340 4 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0185
