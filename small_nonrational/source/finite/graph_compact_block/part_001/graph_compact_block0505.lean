module
prelude
import GraphInputsRow29Part00071Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0505
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 3
 (.branch 1
 (.leaf ⟨(29, 12388163141760), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00071.record000_result⟩)
 (.branch 2
 (.leaf ⟨(29, 12447958204672), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00071.record001_result⟩)
 (.leaf ⟨(29, 12448495075328), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00071.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(29, 12456548139136), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00071.record003_result⟩)
 (.branch 5
 (.leaf ⟨(29, 12465138073600), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00071.record004_result⟩)
 (.leaf ⟨(29, 12465274355712), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00071.record005_result⟩))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (21491 + i))) 0 6 :=
  interval_of_check _ 0 6 (by decide +kernel)

public theorem complete : Block 21491 21497 :=
  block_of_table results 21491 6 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0505
