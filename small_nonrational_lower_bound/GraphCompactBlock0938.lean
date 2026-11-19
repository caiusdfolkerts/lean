module
prelude
import GraphInputsRow31Part00150Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0938
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨(31, 30826398023680), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00150.record000_result⟩)
 (.leaf ⟨(31, 30826662264832), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00150.record001_result⟩))
 (.branch 3
 (.leaf ⟨(31, 30826670587904), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00150.record002_result⟩)
 (.leaf ⟨(31, 30826859332128), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00150.record003_result⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨(31, 30826860445696), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00150.record004_result⟩)
 (.leaf ⟨(31, 30839008166144), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00150.record005_result⟩))
 (.branch 7
 (.leaf ⟨(31, 30839342694400), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00150.record006_result⟩)
 (.leaf ⟨(31, 30839545036800), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00150.record007_result⟩))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (26623 + i))) 0 8 :=
  interval_of_check _ 0 8 (by decide +kernel)

public theorem complete : Block 26623 26631 :=
  block_of_table results 26623 8 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0938
