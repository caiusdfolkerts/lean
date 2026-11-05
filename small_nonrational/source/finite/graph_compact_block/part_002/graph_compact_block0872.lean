module
prelude
import GraphInputsRow31Part00084Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0872
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 2
 (.branch 1
 (.leaf ⟨(31, 17044309544960), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00084.record000_result⟩)
 (.leaf ⟨(31, 17051037470976), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00084.record001_result⟩))
 (.branch 3
 (.leaf ⟨(31, 17051574341632), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00084.record002_result⟩)
 (.branch 4
 (.leaf ⟨(31, 17051590856704), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00084.record003_result⟩)
 (.leaf ⟨(31, 17052094042368), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00084.record004_result⟩))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (26174 + i))) 0 5 :=
  interval_of_check _ 0 5 (by decide +kernel)

public theorem complete : Block 26174 26179 :=
  block_of_table results 26174 5 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0872
