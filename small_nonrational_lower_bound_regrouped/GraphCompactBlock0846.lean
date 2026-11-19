module
prelude
import GraphInputsRow31Part00058Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0846
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨(31, 12279990976512), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00058.record000_result⟩)
 (.leaf ⟨(31, 12288039911424), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00058.record001_result⟩))
 (.branch 3
 (.leaf ⟨(31, 12288576716800), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00058.record002_result⟩)
 (.leaf ⟨(31, 12314283606016), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00058.record003_result⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨(31, 12320788971520), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00058.record004_result⟩)
 (.leaf ⟨(31, 12425478832128), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00058.record005_result⟩))
 (.branch 7
 (.leaf ⟨(31, 12440511217920), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00058.record006_result⟩)
 (.leaf ⟨(31, 12464064331776), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00058.record007_result⟩))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (25938 + i))) 0 8 :=
  interval_of_check _ 0 8 (by decide +kernel)

public theorem complete : Block 25938 25946 :=
  block_of_table results 25938 8 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0846
