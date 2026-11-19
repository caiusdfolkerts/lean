module
prelude
import GraphInputsRow29Part00179Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0613
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 3
 (.branch 1
 (.leaf ⟨(29, 25994215964928), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00179.record000_result⟩)
 (.branch 2
 (.leaf ⟨(29, 25994886906368), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00179.record001_result⟩)
 (.leaf ⟨(29, 25997437178112), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00179.record002_result⟩)))
 (.branch 5
 (.branch 4
 (.leaf ⟨(29, 26117981929472), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00179.record003_result⟩)
 (.leaf ⟨(29, 26122545283072), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00179.record004_result⟩))
 (.branch 6
 (.leaf ⟨(29, 26126286196992), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00179.record005_result⟩)
 (.leaf ⟨(29, 26130983948288), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00179.record006_result⟩))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (22820 + i))) 0 7 :=
  interval_of_check _ 0 7 (by decide +kernel)

public theorem complete : Block 22820 22827 :=
  block_of_table results 22820 7 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0613
