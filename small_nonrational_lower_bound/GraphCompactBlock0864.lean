module
prelude
import GraphInputsRow31Part00076Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0864
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 2
 (.branch 1
 (.leaf ⟨(31, 14371523141632), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00076.record000_result⟩)
 (.leaf ⟨(31, 14372646748160), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00076.record001_result⟩))
 (.branch 3
 (.leaf ⟨(31, 14380108881920), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00076.record002_result⟩)
 (.branch 4
 (.leaf ⟨(31, 14381429555744), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00076.record003_result⟩)
 (.leaf ⟨(31, 14435939262720), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00076.record004_result⟩))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (26070 + i))) 0 5 :=
  interval_of_check _ 0 5 (by decide +kernel)

public theorem complete : Block 26070 26075 :=
  block_of_table results 26070 5 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0864
