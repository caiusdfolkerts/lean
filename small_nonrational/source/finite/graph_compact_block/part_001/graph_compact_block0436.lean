module
prelude
import GraphInputsRow29Part00002Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0436
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 3
 (.branch 1
 (.leaf ⟨(29, 1007843049728), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00002.record000_result⟩)
 (.branch 2
 (.leaf ⟨(29, 1016168775680), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00002.record001_result⟩)
 (.leaf ⟨(29, 1026566422784), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00002.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(29, 1026702770176), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00002.record003_result⟩)
 (.branch 5
 (.leaf ⟨(29, 1026711093248), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00002.record004_result⟩)
 (.leaf ⟨(29, 1026843213824), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00002.record005_result⟩))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (20502 + i))) 0 6 :=
  interval_of_check _ 0 6 (by decide +kernel)

public theorem complete : Block 20502 20508 :=
  block_of_table results 20502 6 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0436
