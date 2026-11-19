module
prelude
import GraphInputsRow29Part00172Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0606
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 1
 (.leaf ⟨(29, 25772507004928), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00172.record000_result⟩)
 (.branch 2
 (.leaf ⟨(29, 25772622610432), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00172.record001_result⟩)
 (.leaf ⟨(29, 25774702985216), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00172.record002_result⟩)))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (22779 + i))) 0 3 :=
  interval_of_check _ 0 3 (by decide +kernel)

public theorem complete : Block 22779 22782 :=
  block_of_table results 22779 3 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0606
