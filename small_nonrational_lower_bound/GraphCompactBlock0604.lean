module
prelude
import GraphInputsRow29Part00170Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0604
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 1
 (.leaf ⟨(29, 25707059085312), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00170.record000_result⟩)
 (.branch 2
 (.leaf ⟨(29, 25719407132672), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00170.record001_result⟩)
 (.leaf ⟨(29, 25722593755136), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00170.record002_result⟩)))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (22767 + i))) 0 3 :=
  interval_of_check _ 0 3 (by decide +kernel)

public theorem complete : Block 22767 22770 :=
  block_of_table results 22767 3 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0604
