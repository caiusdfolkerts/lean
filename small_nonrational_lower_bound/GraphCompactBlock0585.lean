module
prelude
import GraphInputsRow29Part00151Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0585
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 2
 (.branch 1
 (.leaf ⟨(29, 24661771436032), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00151.record000_result⟩)
 (.leaf ⟨(29, 24663986012160), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00151.record001_result⟩))
 (.branch 3
 (.leaf ⟨(29, 24666066386944), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00151.record002_result⟩)
 (.leaf ⟨(29, 24666198507520), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00151.record003_result⟩)))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (22609 + i))) 0 4 :=
  interval_of_check _ 0 4 (by decide +kernel)

public theorem complete : Block 22609 22613 :=
  block_of_table results 22609 4 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0585
