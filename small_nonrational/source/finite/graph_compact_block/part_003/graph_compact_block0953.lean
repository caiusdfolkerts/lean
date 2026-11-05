module
prelude
import GraphInputsRow31Part00165Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0953
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 2
 (.branch 1
 (.leaf ⟨(31, 32298171908352), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00165.record000_result⟩)
 (.leaf ⟨(31, 32351975374848), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00165.record001_result⟩))
 (.branch 3
 (.leaf ⟨(31, 32474524614656), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00165.record002_result⟩)
 (.branch 4
 (.leaf ⟨(31, 32547807428608), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00165.record003_result⟩)
 (.leaf ⟨(31, 32564978909184), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00165.record004_result⟩))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (26728 + i))) 0 5 :=
  interval_of_check _ 0 5 (by decide +kernel)

public theorem complete : Block 26728 26733 :=
  block_of_table results 26728 5 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0953
