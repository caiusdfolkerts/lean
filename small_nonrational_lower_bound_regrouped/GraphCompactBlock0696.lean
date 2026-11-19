module
prelude
import GraphInputsRow29Part00262Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0696
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 2
 (.branch 1
 (.leaf ⟨(29, 32813571178496), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00262.record000_result⟩)
 (.leaf ⟨(29, 32822165241856), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00262.record001_result⟩))
 (.branch 3
 (.leaf ⟨(29, 32822693724160), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00262.record002_result⟩)
 (.leaf ⟨(29, 32839320076288), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00262.record003_result⟩)))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (23419 + i))) 0 4 :=
  interval_of_check _ 0 4 (by decide +kernel)

public theorem complete : Block 23419 23423 :=
  block_of_table results 23419 4 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0696
