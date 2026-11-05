module
prelude
import GraphInputsRow31Part00168Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0956
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf ⟨(31, 33023068274688), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00168.record000_result⟩)
 (.leaf ⟨(31, 33039071608832), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00168.record001_result⟩))
 (.branch 3
 (.leaf ⟨(31, 33063732125952), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00168.record002_result⟩)
 (.branch 4
 (.leaf ⟨(31, 33072322060416), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00168.record003_result⟩)
 (.leaf ⟨(31, 33132520734720), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00168.record004_result⟩))))
 (.branch 8
 (.branch 6
 (.leaf ⟨(31, 33133123600384), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00168.record005_result⟩)
 (.branch 7
 (.leaf ⟨(31, 33168027549696), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00168.record006_result⟩)
 (.leaf ⟨(31, 33204467662848), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00168.record007_result⟩)))
 (.branch 9
 (.leaf ⟨(31, 33264807452672), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00168.record008_result⟩)
 (.branch 10
 (.leaf ⟨(31, 33273111777312), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00168.record009_result⟩)
 (.leaf ⟨(31, 33297946116096), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00168.record010_result⟩)))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (26742 + i))) 0 11 :=
  interval_of_check _ 0 11 (by decide +kernel)

public theorem complete : Block 26742 26753 :=
  block_of_table results 26742 11 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0956
