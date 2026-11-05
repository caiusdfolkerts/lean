module
prelude
import GraphInputsRow31Part00004Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0792
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf ⟨(31, 705794441472), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00004.record000_result⟩)
 (.leaf ⟨(31, 705794506752), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00004.record001_result⟩))
 (.branch 3
 (.leaf ⟨(31, 705796522240), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00004.record002_result⟩)
 (.branch 4
 (.leaf ⟨(31, 706062876928), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00004.record003_result⟩)
 (.leaf ⟨(31, 706062942208), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00004.record004_result⟩))))
 (.branch 7
 (.branch 6
 (.leaf ⟨(31, 706266275904), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00004.record005_result⟩)
 (.leaf ⟨(31, 735114756352), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00004.record006_result⟩))
 (.branch 8
 (.leaf ⟨(31, 735123144704), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00004.record007_result⟩)
 (.branch 9
 (.leaf ⟨(31, 739298607104), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00004.record008_result⟩)
 (.leaf ⟨(31, 743836778752), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00004.record009_result⟩)))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (25486 + i))) 0 10 :=
  interval_of_check _ 0 10 (by decide +kernel)

public theorem complete : Block 25486 25496 :=
  block_of_table results 25486 10 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0792
