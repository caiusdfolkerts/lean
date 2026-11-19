module
prelude
import GraphInputsRow29Part00024Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0458
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 2
 (.branch 1
 (.leaf ⟨(29, 6379368808448), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00024.record000_result⟩)
 (.leaf ⟨(29, 6379377131520), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00024.record001_result⟩))
 (.branch 3
 (.leaf ⟨(29, 6379905483264), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00024.record002_result⟩)
 (.leaf ⟨(29, 6379913871360), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00024.record003_result⟩)))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (20878 + i))) 0 4 :=
  interval_of_check _ 0 4 (by decide +kernel)

public theorem complete : Block 20878 20882 :=
  block_of_table results 20878 4 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0458
