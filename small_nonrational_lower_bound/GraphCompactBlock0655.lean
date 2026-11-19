module
prelude
import GraphInputsRow29Part00221Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0655
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 3
 (.branch 1
 (.leaf ⟨(29, 30031686696960), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00221.record000_result⟩)
 (.branch 2
 (.leaf ⟨(29, 30237704355840), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00221.record001_result⟩)
 (.leaf ⟨(29, 30237795057920), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00221.record002_result⟩)))
 (.branch 5
 (.branch 4
 (.leaf ⟨(29, 30237799284736), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00221.record003_result⟩)
 (.leaf ⟨(29, 30237803446272), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00221.record004_result⟩))
 (.branch 6
 (.leaf ⟨(29, 30237807087616), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00221.record005_result⟩)
 (.leaf ⟨(29, 30238197694592), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00221.record006_result⟩))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (23141 + i))) 0 7 :=
  interval_of_check _ 0 7 (by decide +kernel)

public theorem complete : Block 23141 23148 :=
  block_of_table results 23141 7 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0655
