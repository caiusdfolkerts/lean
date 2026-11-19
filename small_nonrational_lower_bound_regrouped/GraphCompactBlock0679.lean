module
prelude
import GraphInputsRow29Part00245Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0679
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 1
 (.leaf ⟨(29, 31896081801216), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00245.record000_result⟩)
 (.branch 2
 (.leaf ⟨(29, 31924225638400), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00245.record001_result⟩)
 (.leaf ⟨(29, 31930466762752), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00245.record002_result⟩)))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (23346 + i))) 0 3 :=
  interval_of_check _ 0 3 (by decide +kernel)

public theorem complete : Block 23346 23349 :=
  block_of_table results 23346 3 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0679
