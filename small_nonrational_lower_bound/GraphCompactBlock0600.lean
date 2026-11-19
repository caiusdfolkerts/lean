module
prelude
import GraphInputsRow29Part00166Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0600
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 2
 (.branch 1
 (.leaf ⟨(29, 25445066096640), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00166.record000_result⟩)
 (.leaf ⟨(29, 25445132156928), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00166.record001_result⟩))
 (.branch 3
 (.leaf ⟨(29, 25445569413376), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00166.record002_result⟩)
 (.leaf ⟨(29, 25446205374464), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00166.record003_result⟩)))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (22738 + i))) 0 4 :=
  interval_of_check _ 0 4 (by decide +kernel)

public theorem complete : Block 22738 22742 :=
  block_of_table results 22738 4 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0600
