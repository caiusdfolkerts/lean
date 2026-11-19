module
prelude
import GraphInputsRow31Part00170Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0958
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 1
 (.leaf ⟨(31, 34124865732608), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00170.record000_result⟩)
 (.branch 2
 (.leaf ⟨(31, 34125394214912), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00170.record001_result⟩)
 (.leaf ⟨(31, 34129026482176), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00170.record002_result⟩)))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (26757 + i))) 0 3 :=
  interval_of_check _ 0 3 (by decide +kernel)

public theorem complete : Block 26757 26760 :=
  block_of_table results 26757 3 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0958
