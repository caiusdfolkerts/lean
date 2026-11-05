module
prelude
import GraphInputsRow29Part00212Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0646
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 3
 (.branch 1
 (.leaf ⟨(29, 29285637750784), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00212.record000_result⟩)
 (.branch 2
 (.leaf ⟨(29, 29285905596944), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00212.record001_result⟩)
 (.leaf ⟨(29, 29291878551680), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00212.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(29, 29292952027776), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00212.record003_result⟩)
 (.branch 5
 (.leaf ⟨(29, 29414235078784), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00212.record004_result⟩)
 (.leaf ⟨(29, 29414375034880), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00212.record005_result⟩))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (23089 + i))) 0 6 :=
  interval_of_check _ 0 6 (by decide +kernel)

public theorem complete : Block 23089 23095 :=
  block_of_table results 23089 6 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0646
