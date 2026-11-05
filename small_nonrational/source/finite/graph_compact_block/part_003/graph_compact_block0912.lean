module
prelude
import GraphInputsRow31Part00124Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0912
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨(31, 28084791283968), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00124.record000_result⟩)
 (.leaf ⟨(31, 28090298335232), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00124.record001_result⟩))
 (.branch 3
 (.leaf ⟨(31, 28231625342976), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00124.record002_result⟩)
 (.leaf ⟨(31, 28235257610240), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00124.record003_result⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨(31, 28331787452416), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00124.record004_result⟩)
 (.leaf ⟨(31, 28406913696260), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00124.record005_result⟩))
 (.branch 7
 (.leaf ⟨(31, 28597269053696), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00124.record006_result⟩)
 (.leaf ⟨(31, 28597537489024), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00124.record007_result⟩))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (26510 + i))) 0 8 :=
  interval_of_check _ 0 8 (by decide +kernel)

public theorem complete : Block 26510 26518 :=
  block_of_table results 26510 8 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0912
