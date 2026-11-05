module
prelude
import GraphInputsRow31Part00052Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0840
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf ⟨(31, 11151615213696), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00052.record000_result⟩)
 (.leaf ⟨(31, 11214966030336), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00052.record001_result⟩))
 (.branch 3
 (.leaf ⟨(31, 11223555932160), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00052.record002_result⟩)
 (.branch 4
 (.leaf ⟨(31, 11246782906368), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00052.record003_result⟩)
 (.leaf ⟨(31, 11317654061056), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00052.record004_result⟩))))
 (.branch 7
 (.branch 6
 (.leaf ⟨(31, 11364552704128), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00052.record005_result⟩)
 (.leaf ⟨(31, 11673993805824), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00052.record006_result⟩))
 (.branch 8
 (.leaf ⟨(31, 11674530611200), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00052.record007_result⟩)
 (.branch 9
 (.leaf ⟨(31, 11693451706368), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00052.record008_result⟩)
 (.leaf ⟨(31, 11730369380352), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00052.record009_result⟩)))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (25909 + i))) 0 10 :=
  interval_of_check _ 0 10 (by decide +kernel)

public theorem complete : Block 25909 25919 :=
  block_of_table results 25909 10 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0840
