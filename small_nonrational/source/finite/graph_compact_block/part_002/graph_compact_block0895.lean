module
prelude
import GraphInputsRow31Part00107Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0895
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨(31, 24591103688704), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00107.record000_result⟩)
 (.leaf ⟨(31, 24627342614592), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00107.record001_result⟩))
 (.branch 3
 (.leaf ⟨(31, 24742404882432), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00107.record002_result⟩)
 (.leaf ⟨(31, 24742413205504), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00107.record003_result⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨(31, 24745488187648), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00107.record004_result⟩)
 (.leaf ⟨(31, 24746259910656), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00107.record005_result⟩))
 (.branch 7
 (.leaf ⟨(31, 24777683665152), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00107.record006_result⟩)
 (.leaf ⟨(31, 24778471903232), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00107.record007_result⟩))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (26389 + i))) 0 8 :=
  interval_of_check _ 0 8 (by decide +kernel)

public theorem complete : Block 26389 26397 :=
  block_of_table results 26389 8 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0895
