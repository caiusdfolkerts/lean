module
prelude
import GraphInputsRow29Part00286Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0720
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 2
 (.branch 1
 (.leaf ⟨(29, 34640790814720), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00286.record000_result⟩)
 (.leaf ⟨(29, 34643223515392), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00286.record001_result⟩))
 (.branch 3
 (.leaf ⟨(29, 34643760386048), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00286.record002_result⟩)
 (.branch 4
 (.leaf ⟨(29, 34643776901120), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00286.record003_result⟩)
 (.leaf ⟨(29, 34644280086784), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00286.record004_result⟩))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (23523 + i))) 0 5 :=
  interval_of_check _ 0 5 (by decide +kernel)

public theorem complete : Block 23523 23528 :=
  block_of_table results 23523 5 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0720
