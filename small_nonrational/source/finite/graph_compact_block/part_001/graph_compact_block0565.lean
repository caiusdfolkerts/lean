module
prelude
import GraphInputsRow29Part00131Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0565
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 3
 (.branch 1
 (.leaf ⟨(29, 21930658758656), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00131.record000_result⟩)
 (.branch 2
 (.leaf ⟨(29, 21930774364160), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00131.record001_result⟩)
 (.leaf ⟨(29, 21934398177280), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00131.record002_result⟩)))
 (.branch 5
 (.branch 4
 (.leaf ⟨(29, 21947283030016), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00131.record003_result⟩)
 (.leaf ⟨(29, 21951577980928), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00131.record004_result⟩))
 (.branch 6
 (.leaf ⟨(29, 21994033741888), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00131.record005_result⟩)
 (.leaf ⟨(29, 22000476168256), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00131.record006_result⟩))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (22343 + i))) 0 7 :=
  interval_of_check _ 0 7 (by decide +kernel)

public theorem complete : Block 22343 22350 :=
  block_of_table results 22343 7 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0565
