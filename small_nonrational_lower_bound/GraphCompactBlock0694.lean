module
prelude
import GraphInputsRow29Part00260Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0694
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 1
 (.leaf ⟨(29, 32789458059264), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00260.record000_result⟩)
 (.branch 2
 (.leaf ⟨(29, 32804960207364), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00260.record001_result⟩)
 (.leaf ⟨(29, 32804960346112), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00260.record002_result⟩)))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (23414 + i))) 0 3 :=
  interval_of_check _ 0 3 (by decide +kernel)

public theorem complete : Block 23414 23417 :=
  block_of_table results 23414 3 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0694
