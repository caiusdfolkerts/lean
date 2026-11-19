module
prelude
import GraphInputsRow29Part00163Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0597
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 1
 (.leaf ⟨(29, 25368896012288), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00163.record000_result⟩)
 (.branch 2
 (.leaf ⟨(29, 25375809765632), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00163.record001_result⟩)
 (.leaf ⟨(29, 25375946113024), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00163.record002_result⟩)))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (22718 + i))) 0 3 :=
  interval_of_check _ 0 3 (by decide +kernel)

public theorem complete : Block 22718 22721 :=
  block_of_table results 22718 3 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0597
