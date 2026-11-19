module
prelude
import GraphInputsRow31Part00040Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0828
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 1
 (.leaf ⟨(31, 8252016361472), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00040.record000_result⟩)
 (.branch 2
 (.leaf ⟨(31, 8252280602624), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00040.record001_result⟩)
 (.leaf ⟨(31, 8252288925696), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00040.record002_result⟩)))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (25812 + i))) 0 3 :=
  interval_of_check _ 0 3 (by decide +kernel)

public theorem complete : Block 25812 25815 :=
  block_of_table results 25812 3 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0828
