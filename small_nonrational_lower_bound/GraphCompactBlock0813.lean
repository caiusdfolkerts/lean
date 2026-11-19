module
prelude
import GraphInputsRow31Part00025Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0813
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨(31, 6340514709760), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00025.record000_result⟩)
 (.leaf ⟨(31, 6340651057152), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00025.record001_result⟩))
 (.branch 3
 (.leaf ⟨(31, 6340659380224), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00025.record002_result⟩)
 (.leaf ⟨(31, 6341263360000), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00025.record003_result⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨(31, 6341554897152), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00025.record004_result⟩)
 (.leaf ⟨(31, 6378026598656), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00025.record005_result⟩))
 (.branch 7
 (.leaf ⟨(31, 6378831741440), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00025.record006_result⟩)
 (.branch 8
 (.leaf ⟨(31, 6378840129536), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00025.record007_result⟩)
 (.leaf ⟨(31, 6379377000448), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00025.record008_result⟩)))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (25703 + i))) 0 9 :=
  interval_of_check _ 0 9 (by decide +kernel)

public theorem complete : Block 25703 25712 :=
  block_of_table results 25703 9 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0813
