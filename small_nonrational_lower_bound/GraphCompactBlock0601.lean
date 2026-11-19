module
prelude
import GraphInputsRow29Part00167Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0601
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 2
 (.branch 1
 (.leaf ⟨(29, 25447715848448), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00167.record000_result⟩)
 (.leaf ⟨(29, 25513248751616), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00167.record001_result⟩))
 (.branch 3
 (.leaf ⟨(29, 25570123481344), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00167.record002_result⟩)
 (.branch 4
 (.leaf ⟨(29, 25570491039744), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00167.record003_result⟩)
 (.leaf ⟨(29, 25570893643776), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00167.record004_result⟩))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (22742 + i))) 0 5 :=
  interval_of_check _ 0 5 (by decide +kernel)

public theorem complete : Block 22742 22747 :=
  block_of_table results 22742 5 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0601
