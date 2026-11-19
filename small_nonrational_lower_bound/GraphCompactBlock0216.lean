module
prelude
import GraphInputsRow24Part00100Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0216
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 2
 (.branch 1
 (.leaf ⟨(24, 25581032835088), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00100.record000_result⟩)
 (.leaf ⟨(24, 25590657728512), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00100.record001_result⟩))
 (.branch 3
 (.leaf ⟨(24, 25633724842240), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00100.record002_result⟩)
 (.leaf ⟨(24, 25634244141120), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00100.record003_result⟩)))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (10967 + i))) 0 4 :=
  interval_of_check _ 0 4 (by decide +kernel)

public theorem complete : Block 10967 10971 :=
  block_of_table results 10967 4 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0216
