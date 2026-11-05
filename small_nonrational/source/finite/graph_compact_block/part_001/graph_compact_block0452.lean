module
prelude
import GraphInputsRow29Part00018Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0452
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨(29, 4329490614272), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00018.record000_result⟩)
 (.leaf ⟨(29, 4329729952000), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00018.record001_result⟩))
 (.branch 3
 (.leaf ⟨(29, 4333890570496), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00018.record002_result⟩)
 (.leaf ⟨(29, 4333894697216), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00018.record003_result⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨(29, 4333898958848), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00018.record004_result⟩)
 (.leaf ⟨(29, 4333907215104), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00018.record005_result⟩))
 (.branch 7
 (.leaf ⟨(29, 4334179909632), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00018.record006_result⟩)
 (.leaf ⟨(29, 4334188232704), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00018.record007_result⟩))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (20765 + i))) 0 8 :=
  interval_of_check _ 0 8 (by decide +kernel)

public theorem complete : Block 20765 20773 :=
  block_of_table results 20765 8 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0452
