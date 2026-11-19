module
prelude
import GraphInputsRow29Part00064Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0498
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 2
 (.branch 1
 (.leaf ⟨(29, 11996141453312), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00064.record000_result⟩)
 (.leaf ⟨(29, 11996401532928), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00064.record001_result⟩))
 (.branch 3
 (.leaf ⟨(29, 11996649259008), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00064.record002_result⟩)
 (.branch 4
 (.leaf ⟨(29, 12000157532416), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00064.record003_result⟩)
 (.leaf ⟨(29, 12000434323456), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00064.record004_result⟩))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (21411 + i))) 0 5 :=
  interval_of_check _ 0 5 (by decide +kernel)

public theorem complete : Block 21411 21416 :=
  block_of_table results 21411 5 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0498
