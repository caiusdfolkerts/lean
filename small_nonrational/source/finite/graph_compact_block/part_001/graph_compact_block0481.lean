module
prelude
import GraphInputsRow29Part00047Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0481
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 3
 (.branch 1
 (.leaf ⟨(29, 8252288925697), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00047.record000_result⟩)
 (.branch 2
 (.leaf ⟨(29, 8252288991232), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00047.record001_result⟩)
 (.leaf ⟨(29, 8263697434640), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00047.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(29, 8264073383936), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00047.record003_result⟩)
 (.branch 5
 (.leaf ⟨(29, 8264093796368), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00047.record004_result⟩)
 (.leaf ⟨(29, 8265167536129), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00047.record005_result⟩))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (21128 + i))) 0 6 :=
  interval_of_check _ 0 6 (by decide +kernel)

public theorem complete : Block 21128 21134 :=
  block_of_table results 21128 6 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0481
