module
prelude
import GraphInputsRow29Part00213Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0647
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf ⟨(29, 29420814340096), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00213.record000_result⟩)
 (.leaf ⟨(29, 29423076114960), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00213.record001_result⟩))
 (.branch 3
 (.leaf ⟨(29, 29515032330368), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00213.record002_result⟩)
 (.branch 4
 (.leaf ⟨(29, 29515300765696), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00213.record003_result⟩)
 (.leaf ⟨(29, 29515304927232), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00213.record004_result⟩))))
 (.branch 7
 (.branch 6
 (.leaf ⟨(29, 29523605325952), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00213.record005_result⟩)
 (.leaf ⟨(29, 29523873761280), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00213.record006_result⟩))
 (.branch 8
 (.leaf ⟨(29, 29523890405888), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00213.record007_result⟩)
 (.branch 9
 (.leaf ⟨(29, 29550466580608), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00213.record008_result⟩)
 (.leaf ⟨(29, 29550534754304), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00213.record009_result⟩)))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (23095 + i))) 0 10 :=
  interval_of_check _ 0 10 (by decide +kernel)

public theorem complete : Block 23095 23105 :=
  block_of_table results 23095 10 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0647
