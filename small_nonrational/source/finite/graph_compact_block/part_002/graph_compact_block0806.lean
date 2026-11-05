module
prelude
import GraphInputsRow31Part00018Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0806
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 3
 (.branch 1
 (.leaf ⟨(31, 4520868380672), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00018.record000_result⟩)
 (.branch 2
 (.leaf ⟨(31, 4523406950656), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00018.record001_result⟩)
 (.leaf ⟨(31, 4523418460160), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00018.record002_result⟩)))
 (.branch 5
 (.branch 4
 (.leaf ⟨(31, 4545762574592), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00018.record003_result⟩)
 (.leaf ⟨(31, 4554084073728), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00018.record004_result⟩))
 (.branch 6
 (.leaf ⟨(31, 4591992209664), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00018.record005_result⟩)
 (.leaf ⟨(31, 4626486141184), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00018.record006_result⟩))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (25632 + i))) 0 7 :=
  interval_of_check _ 0 7 (by decide +kernel)

public theorem complete : Block 25632 25639 :=
  block_of_table results 25632 7 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0806
