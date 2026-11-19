module
prelude
import GraphInputsRow31Part00072Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0860
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 3
 (.branch 1
 (.leaf ⟨(31, 13891543375872), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00072.record000_result⟩)
 (.branch 2
 (.leaf ⟨(31, 13891601957632), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00072.record001_result⟩)
 (.leaf ⟨(31, 13892642145024), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00072.record002_result⟩)))
 (.branch 5
 (.branch 4
 (.leaf ⟨(31, 13899319742496), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00072.record003_result⟩)
 (.leaf ⟨(31, 13899659280640), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00072.record004_result⟩))
 (.branch 6
 (.leaf ⟨(31, 13900196151296), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00072.record005_result⟩)
 (.leaf ⟨(31, 13900204474368), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00072.record006_result⟩))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (26043 + i))) 0 7 :=
  interval_of_check _ 0 7 (by decide +kernel)

public theorem complete : Block 26043 26050 :=
  block_of_table results 26043 7 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0860
