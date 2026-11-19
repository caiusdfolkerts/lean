module
prelude
import GraphInputsRow29Part00249Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0683
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 2
 (.branch 1
 (.leaf ⟨(29, 32078708080640), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00249.record000_result⟩)
 (.leaf ⟨(29, 32165295825152), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00249.record001_result⟩))
 (.branch 3
 (.leaf ⟨(29, 32169859227712), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00249.record002_result⟩)
 (.leaf ⟨(29, 32172057051136), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00249.record003_result⟩)))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (23369 + i))) 0 4 :=
  interval_of_check _ 0 4 (by decide +kernel)

public theorem complete : Block 23369 23373 :=
  block_of_table results 23369 4 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0683
