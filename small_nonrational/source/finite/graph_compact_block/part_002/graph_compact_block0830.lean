module
prelude
import GraphInputsRow31Part00042Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0830
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨(31, 8267846156544), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00042.record000_result⟩)
 (.leaf ⟨(31, 8268617879552), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00042.record001_result⟩))
 (.branch 3
 (.leaf ⟨(31, 8323663986944), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00042.record002_result⟩)
 (.leaf ⟨(31, 8324200857600), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00042.record003_result⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨(31, 8324209180672), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00042.record004_result⟩)
 (.leaf ⟨(31, 8324720558336), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00042.record005_result⟩))
 (.branch 7
 (.leaf ⟨(31, 8325265752064), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00042.record006_result⟩)
 (.leaf ⟨(31, 8332253888768), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00042.record007_result⟩))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (25820 + i))) 0 8 :=
  interval_of_check _ 0 8 (by decide +kernel)

public theorem complete : Block 25820 25828 :=
  block_of_table results 25820 8 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0830
