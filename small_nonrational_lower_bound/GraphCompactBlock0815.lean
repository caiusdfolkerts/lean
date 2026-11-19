module
prelude
import GraphInputsRow31Part00027Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0815
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf ⟨(31, 6706864128256), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00027.record000_result⟩)
 (.leaf ⟨(31, 6707400998912), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00027.record001_result⟩))
 (.branch 3
 (.leaf ⟨(31, 6707409321984), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00027.record002_result⟩)
 (.branch 4
 (.leaf ⟨(31, 6711561748480), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00027.record003_result⟩)
 (.leaf ⟨(31, 6711570071552), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00027.record004_result⟩))))
 (.branch 7
 (.branch 6
 (.leaf ⟨(31, 6713642123264), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00027.record005_result⟩)
 (.leaf ⟨(31, 6743661224000), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00027.record006_result⟩))
 (.branch 8
 (.leaf ⟨(31, 6744717795392), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00027.record007_result⟩)
 (.branch 9
 (.leaf ⟨(31, 6825508340256), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00027.record008_result⟩)
 (.leaf ⟨(31, 6844307275776), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00027.record009_result⟩)))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (25726 + i))) 0 10 :=
  interval_of_check _ 0 10 (by decide +kernel)

public theorem complete : Block 25726 25736 :=
  block_of_table results 25726 10 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0815
