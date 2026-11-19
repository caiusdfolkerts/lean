module
prelude
import GraphInputsRow31Part00077Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0865
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨(31, 14448941338656), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00077.record000_result⟩)
 (.leaf ⟨(31, 14449958191104), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00077.record001_result⟩))
 (.branch 3
 (.leaf ⟨(31, 14450014814752), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00077.record002_result⟩)
 (.leaf ⟨(31, 14450015928320), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00077.record003_result⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨(31, 14452599619840), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00077.record004_result⟩)
 (.leaf ⟨(31, 14483193856000), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00077.record005_result⟩))
 (.branch 7
 (.leaf ⟨(31, 14487738384384), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00077.record006_result⟩)
 (.branch 8
 (.leaf ⟨(31, 14573109780736), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00077.record007_result⟩)
 (.leaf ⟨(31, 14587388788736), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00077.record008_result⟩)))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (26075 + i))) 0 9 :=
  interval_of_check _ 0 9 (by decide +kernel)

public theorem complete : Block 26075 26084 :=
  block_of_table results 26075 9 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0865
