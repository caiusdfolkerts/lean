module
prelude
import GraphInputsRow29Part00279Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0713
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 2
 (.branch 1
 (.leaf ⟨(29, 34159020015616), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00279.record000_result⟩)
 (.leaf ⟨(29, 34160060203008), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00279.record001_result⟩))
 (.branch 3
 (.leaf ⟨(29, 34213709480452), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00279.record002_result⟩)
 (.leaf ⟨(29, 34224598482944), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00279.record003_result⟩)))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (23486 + i))) 0 4 :=
  interval_of_check _ 0 4 (by decide +kernel)

public theorem complete : Block 23486 23490 :=
  block_of_table results 23486 4 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0713
