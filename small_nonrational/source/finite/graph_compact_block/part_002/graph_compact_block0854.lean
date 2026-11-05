module
prelude
import GraphInputsRow31Part00066Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0854
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 2
 (.branch 1
 (.leaf ⟨(31, 13272867733504), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00066.record000_result⟩)
 (.leaf ⟨(31, 13273127747840), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00066.record001_result⟩))
 (.branch 3
 (.leaf ⟨(31, 13273139257344), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00066.record002_result⟩)
 (.branch 4
 (.leaf ⟨(31, 13273329049856), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00066.record003_result⟩)
 (.leaf ⟨(31, 13274402267392), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00066.record004_result⟩))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (25996 + i))) 0 5 :=
  interval_of_check _ 0 5 (by decide +kernel)

public theorem complete : Block 25996 26001 :=
  block_of_table results 25996 5 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0854
