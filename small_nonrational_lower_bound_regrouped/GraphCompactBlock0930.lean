module
prelude
import GraphInputsRow31Part00142Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0930
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 1
 (.leaf ⟨(31, 30314433347584), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00142.record000_result⟩)
 (.branch 2
 (.leaf ⟨(31, 30314953113600), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00142.record001_result⟩)
 (.leaf ⟨(31, 30322486444032), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00142.record002_result⟩)))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (26592 + i))) 0 3 :=
  interval_of_check _ 0 3 (by decide +kernel)

public theorem complete : Block 26592 26595 :=
  block_of_table results 26592 3 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0930
