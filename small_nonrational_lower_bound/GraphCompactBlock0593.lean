module
prelude
import GraphInputsRow29Part00159Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0593
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 2
 (.branch 1
 (.leaf ⟨(29, 25161598238720), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00159.record000_result⟩)
 (.leaf ⟨(29, 25169919737856), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00159.record001_result⟩))
 (.branch 3
 (.leaf ⟨(29, 25177132908544), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00159.record002_result⟩)
 (.leaf ⟨(29, 25178241236992), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00159.record003_result⟩)))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (22679 + i))) 0 4 :=
  interval_of_check _ 0 4 (by decide +kernel)

public theorem complete : Block 22679 22683 :=
  block_of_table results 22679 4 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0593
