module
prelude
import GraphInputsRow31Part00161Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0949
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 3
 (.branch 1
 (.leaf ⟨(31, 31620103413760), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00161.record000_result⟩)
 (.branch 2
 (.leaf ⟨(31, 31628156477568), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00161.record001_result⟩)
 (.leaf ⟨(31, 31629213048960), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00161.record002_result⟩)))
 (.branch 5
 (.branch 4
 (.leaf ⟨(31, 31636729237536), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00161.record003_result⟩)
 (.leaf ⟨(31, 31671088841220), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00161.record004_result⟩))
 (.branch 6
 (.leaf ⟨(31, 31748416110848), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00161.record005_result⟩)
 (.leaf ⟨(31, 31750684213248), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00161.record006_result⟩))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (26705 + i))) 0 7 :=
  interval_of_check _ 0 7 (by decide +kernel)

public theorem complete : Block 26705 26712 :=
  block_of_table results 26705 7 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0949
