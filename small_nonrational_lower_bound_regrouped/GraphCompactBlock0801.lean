module
prelude
import GraphInputsRow31Part00013Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0801
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 3
 (.branch 1
 (.leaf ⟨(31, 3415174348800), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00013.record000_result⟩)
 (.branch 2
 (.leaf ⟨(31, 3736757895424), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00013.record001_result⟩)
 (.leaf ⟨(31, 3922651578624), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00013.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(31, 3923188449280), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00013.record003_result⟩)
 (.branch 5
 (.leaf ⟨(31, 3923196772352), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00013.record004_result⟩)
 (.leaf ⟨(31, 3926812328192), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00013.record005_result⟩))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (25588 + i))) 0 6 :=
  interval_of_check _ 0 6 (by decide +kernel)

public theorem complete : Block 25588 25594 :=
  block_of_table results 25588 6 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0801
