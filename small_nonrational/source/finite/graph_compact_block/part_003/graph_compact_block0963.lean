module
prelude
import GraphInputsRow31Part00175Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0963
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 2
 (.branch 1
 (.leaf ⟨(31, 34651813449728), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00175.record000_result⟩)
 (.leaf ⟨(31, 34652870021120), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00175.record001_result⟩))
 (.branch 3
 (.leaf ⟨(31, 34660420157440), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00175.record002_result⟩)
 (.leaf ⟨(31, 34704686317568), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00175.record003_result⟩)))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (26792 + i))) 0 4 :=
  interval_of_check _ 0 4 (by decide +kernel)

public theorem complete : Block 26792 26796 :=
  block_of_table results 26792 4 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0963
