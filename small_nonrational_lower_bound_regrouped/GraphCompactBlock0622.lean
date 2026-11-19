module
prelude
import GraphInputsRow29Part00188Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0622
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 2
 (.branch 1
 (.leaf ⟨(29, 27267812065280), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00188.record000_result⟩)
 (.leaf ⟨(29, 27268080467968), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00188.record001_result⟩))
 (.branch 3
 (.leaf ⟨(29, 27354179076096), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00188.record002_result⟩)
 (.branch 4
 (.leaf ⟨(29, 27386877870336), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00188.record003_result⟩)
 (.leaf ⟨(29, 27387414740992), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00188.record004_result⟩))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (22925 + i))) 0 5 :=
  interval_of_check _ 0 5 (by decide +kernel)

public theorem complete : Block 22925 22930 :=
  block_of_table results 22925 5 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0622
