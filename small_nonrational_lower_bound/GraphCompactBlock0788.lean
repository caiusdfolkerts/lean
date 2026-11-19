module
prelude
import GraphInputsRow31Part00000Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0788
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 3
 (.branch 1
 (.leaf ⟨(31, 3328262528), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00000.record000_result⟩)
 (.branch 2
 (.leaf ⟨(31, 3394322816), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00000.record001_result⟩)
 (.leaf ⟨(31, 37994201344), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00000.record002_result⟩)))
 (.branch 5
 (.branch 4
 (.leaf ⟨(31, 38262636672), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00000.record003_result⟩)
 (.leaf ⟨(31, 39934034816), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00000.record004_result⟩))
 (.branch 6
 (.leaf ⟨(31, 40074576128), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00000.record005_result⟩)
 (.leaf ⟨(31, 40343011456), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00000.record006_result⟩))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (25442 + i))) 0 7 :=
  interval_of_check _ 0 7 (by decide +kernel)

public theorem complete : Block 25442 25449 :=
  block_of_table results 25442 7 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0788
