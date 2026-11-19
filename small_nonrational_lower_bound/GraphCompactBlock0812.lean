module
prelude
import GraphInputsRow31Part00024Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0812
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 2
 (.branch 1
 (.leaf ⟨(31, 6103186342144), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00024.record000_result⟩)
 (.leaf ⟨(31, 6103954423808), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00024.record001_result⟩))
 (.branch 3
 (.leaf ⟨(31, 6176163168512), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00024.record002_result⟩)
 (.branch 4
 (.leaf ⟨(31, 6305574027264), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00024.record003_result⟩)
 (.leaf ⟨(31, 6329440206848), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00024.record004_result⟩))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (25698 + i))) 0 5 :=
  interval_of_check _ 0 5 (by decide +kernel)

public theorem complete : Block 25698 25703 :=
  block_of_table results 25698 5 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0812
