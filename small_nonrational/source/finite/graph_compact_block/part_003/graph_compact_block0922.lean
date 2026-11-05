module
prelude
import GraphInputsRow31Part00134Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0922
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 3
 (.branch 1
 (.leaf ⟨(31, 29423076638720), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00134.record000_result⟩)
 (.branch 2
 (.leaf ⟨(31, 29523626164224), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00134.record001_result⟩)
 (.leaf ⟨(31, 29523890405376), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00134.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(31, 29549392838784), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00134.record003_result⟩)
 (.branch 5
 (.leaf ⟨(31, 29550517977088), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00134.record004_result⟩)
 (.leaf ⟨(31, 29552734633984), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00134.record005_result⟩))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (26564 + i))) 0 6 :=
  interval_of_check _ 0 6 (by decide +kernel)

public theorem complete : Block 26564 26570 :=
  block_of_table results 26564 6 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0922
