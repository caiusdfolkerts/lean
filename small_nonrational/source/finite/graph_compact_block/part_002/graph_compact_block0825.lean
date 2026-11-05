module
prelude
import GraphInputsRow31Part00037Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0825
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨(31, 7584912408832), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00037.record000_result⟩)
 (.leaf ⟨(31, 7585717551616), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00037.record001_result⟩))
 (.branch 3
 (.leaf ⟨(31, 7585719648256), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00037.record002_result⟩)
 (.leaf ⟨(31, 7593521086720), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00037.record003_result⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨(31, 7597818183680), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00037.record004_result⟩)
 (.leaf ⟨(31, 7598074036224), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00037.record005_result⟩))
 (.branch 7
 (.leaf ⟨(31, 7598090747904), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00037.record006_result⟩)
 (.leaf ⟨(31, 7598602715136), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00037.record007_result⟩))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (25789 + i))) 0 8 :=
  interval_of_check _ 0 8 (by decide +kernel)

public theorem complete : Block 25789 25797 :=
  block_of_table results 25789 8 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0825
