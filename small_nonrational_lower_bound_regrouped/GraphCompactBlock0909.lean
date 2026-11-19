module
prelude
import GraphInputsRow31Part00121Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0909
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 3
 (.branch 1
 (.leaf ⟨(31, 27094333554688), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00121.record000_result⟩)
 (.branch 2
 (.leaf ⟨(31, 27094337716224), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00121.record001_result⟩)
 (.leaf ⟨(31, 27097754509312), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00121.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(31, 27123532169216), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00121.record003_result⟩)
 (.branch 5
 (.leaf ⟨(31, 27127569219584), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00121.record004_result⟩)
 (.leaf ⟨(31, 27127573381120), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00121.record005_result⟩))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (26492 + i))) 0 6 :=
  interval_of_check _ 0 6 (by decide +kernel)

public theorem complete : Block 26492 26498 :=
  block_of_table results 26492 6 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0909
