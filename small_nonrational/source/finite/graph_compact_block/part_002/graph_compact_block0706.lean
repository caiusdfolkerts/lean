module
prelude
import GraphInputsRow29Part00272Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0706
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 3
 (.branch 1
 (.leaf ⟨(29, 34088887533568), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00272.record000_result⟩)
 (.branch 2
 (.leaf ⟨(29, 34091337023744), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00272.record001_result⟩)
 (.leaf ⟨(29, 34092108746752), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00272.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(29, 34094558757120), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00272.record003_result⟩)
 (.branch 5
 (.leaf ⟨(29, 34094726053888), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00272.record004_result⟩)
 (.leaf ⟨(29, 34095095627776), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00272.record005_result⟩))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (23461 + i))) 0 6 :=
  interval_of_check _ 0 6 (by decide +kernel)

public theorem complete : Block 23461 23467 :=
  block_of_table results 23461 6 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0706
