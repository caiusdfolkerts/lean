module
prelude
import GraphInputsRow29Part00267Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0701
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 3
 (.branch 1
 (.leaf ⟨(29, 33263550758912), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00267.record000_result⟩)
 (.branch 2
 (.leaf ⟨(29, 33295746236416), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00267.record001_result⟩)
 (.leaf ⟨(29, 33295750397952), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00267.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(29, 33297807851648), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00267.record003_result⟩)
 (.branch 5
 (.leaf ⟨(29, 33298210357760), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00267.record004_result⟩)
 (.leaf ⟨(29, 33579539103744), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00267.record005_result⟩))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (23444 + i))) 0 6 :=
  interval_of_check _ 0 6 (by decide +kernel)

public theorem complete : Block 23444 23450 :=
  block_of_table results 23444 6 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0701
