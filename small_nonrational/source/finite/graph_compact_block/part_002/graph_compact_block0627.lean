module
prelude
import GraphInputsRow29Part00193Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0627
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 2
 (.branch 1
 (.leaf ⟨(29, 28072061702400), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00193.record000_result⟩)
 (.leaf ⟨(29, 28076495339521), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00193.record001_result⟩))
 (.branch 3
 (.leaf ⟨(29, 28082245271552), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00193.record002_result⟩)
 (.leaf ⟨(29, 28082253594624), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00193.record003_result⟩)))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (22952 + i))) 0 4 :=
  interval_of_check _ 0 4 (by decide +kernel)

public theorem complete : Block 22952 22956 :=
  block_of_table results 22952 4 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0627
