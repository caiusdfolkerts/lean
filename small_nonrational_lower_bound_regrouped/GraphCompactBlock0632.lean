module
prelude
import GraphInputsRow29Part00198Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0632
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 2
 (.branch 1
 (.leaf ⟨(29, 28640319389824), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00198.record000_result⟩)
 (.leaf ⟨(29, 28660606705920), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00198.record001_result⟩))
 (.branch 3
 (.leaf ⟨(29, 28660610900096), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00198.record002_result⟩)
 (.branch 4
 (.leaf ⟨(29, 28667363737728), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00198.record003_result⟩)
 (.leaf ⟨(29, 28700114452736), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00198.record004_result⟩))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (22989 + i))) 0 5 :=
  interval_of_check _ 0 5 (by decide +kernel)

public theorem complete : Block 22989 22994 :=
  block_of_table results 22989 5 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0632
