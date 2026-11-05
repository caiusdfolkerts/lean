module
prelude
import GraphInputsRow31Part00132Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0920
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 3
 (.branch 1
 (.leaf ⟨(31, 29284370481152), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00132.record000_result⟩)
 (.branch 2
 (.leaf ⟨(31, 29285906120704), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00132.record001_result⟩)
 (.leaf ⟨(31, 29292819939328), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00132.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(31, 29292956221440), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00132.record003_result⟩)
 (.branch 5
 (.leaf ⟨(31, 29293860126720), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00132.record004_result⟩)
 (.leaf ⟨(31, 29413079023744), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00132.record005_result⟩))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (26556 + i))) 0 6 :=
  interval_of_check _ 0 6 (by decide +kernel)

public theorem complete : Block 26556 26562 :=
  block_of_table results 26556 6 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0920
