module
prelude
import GraphInputsRow29Part00242Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0676
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 2
 (.branch 1
 (.leaf ⟨(29, 31789477265408), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00242.record000_result⟩)
 (.leaf ⟨(29, 31790005747712), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00242.record001_result⟩))
 (.branch 3
 (.leaf ⟨(29, 31795718389760), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00242.record002_result⟩)
 (.leaf ⟨(29, 31812889870336), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00242.record003_result⟩)))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (23334 + i))) 0 4 :=
  interval_of_check _ 0 4 (by decide +kernel)

public theorem complete : Block 23334 23338 :=
  block_of_table results 23334 4 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0676
