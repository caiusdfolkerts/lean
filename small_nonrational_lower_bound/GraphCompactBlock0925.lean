module
prelude
import GraphInputsRow31Part00137Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0925
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 1
 (.leaf ⟨(31, 29761510309888), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00137.record000_result⟩)
 (.branch 2
 (.leaf ⟨(31, 29762013691904), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00137.record001_result⟩)
 (.leaf ⟨(31, 29773992558592), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00137.record002_result⟩)))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (26576 + i))) 0 3 :=
  interval_of_check _ 0 3 (by decide +kernel)

public theorem complete : Block 26576 26579 :=
  block_of_table results 26576 3 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0925
