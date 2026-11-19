module
prelude
import GraphInputsRow31Part00047Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0835
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf ⟨(31, 9496978530560), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00047.record000_result⟩)
 (.leaf ⟨(31, 9528523424000), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00047.record001_result⟩))
 (.branch 3
 (.leaf ⟨(31, 9531337736960), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00047.record002_result⟩)
 (.branch 4
 (.leaf ⟨(31, 9539931930624), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00047.record003_result⟩)
 (.leaf ⟨(31, 9539940253696), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00047.record004_result⟩))))
 (.branch 8
 (.branch 6
 (.leaf ⟨(31, 9578583490560), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00047.record005_result⟩)
 (.branch 7
 (.leaf ⟨(31, 9668789272576), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00047.record006_result⟩)
 (.leaf ⟨(31, 9677370851328), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00047.record007_result⟩)))
 (.branch 9
 (.leaf ⟨(31, 9715287359744), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00047.record008_result⟩)
 (.branch 10
 (.leaf ⟨(31, 9716022411264), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00047.record009_result⟩)
 (.leaf ⟨(31, 10010104954880), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00047.record010_result⟩)))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (25871 + i))) 0 11 :=
  interval_of_check _ 0 11 (by decide +kernel)

public theorem complete : Block 25871 25882 :=
  block_of_table results 25871 11 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0835
