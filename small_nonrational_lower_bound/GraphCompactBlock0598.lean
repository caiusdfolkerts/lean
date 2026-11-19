module
prelude
import GraphInputsRow29Part00164Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0598
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 2
 (.branch 1
 (.leaf ⟨(29, 25375954436096), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00164.record000_result⟩)
 (.leaf ⟨(29, 25376078233600), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00164.record001_result⟩))
 (.branch 3
 (.leaf ⟨(29, 25376086556672), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00164.record002_result⟩)
 (.leaf ⟨(29, 25376350797824), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00164.record003_result⟩)))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (22721 + i))) 0 4 :=
  interval_of_check _ 0 4 (by decide +kernel)

public theorem complete : Block 22721 22725 :=
  block_of_table results 22721 4 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0598
