module
prelude
import GraphInputsRow29Part00210Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0644
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 3
 (.branch 1
 (.leaf ⟨(29, 29185108083216), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00210.record000_result⟩)
 (.branch 2
 (.leaf ⟨(29, 29189000663168), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00210.record001_result⟩)
 (.leaf ⟨(29, 29190074139264), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00210.record002_result⟩)))
 (.branch 5
 (.branch 4
 (.leaf ⟨(29, 29276796125440), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00210.record003_result⟩)
 (.leaf ⟨(29, 29276804513792), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00210.record004_result⟩))
 (.branch 6
 (.leaf ⟨(29, 29276808155136), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00210.record005_result⟩)
 (.leaf ⟨(29, 29276940275712), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00210.record006_result⟩))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (23075 + i))) 0 7 :=
  interval_of_check _ 0 7 (by decide +kernel)

public theorem complete : Block 23075 23082 :=
  block_of_table results 23075 7 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0644
