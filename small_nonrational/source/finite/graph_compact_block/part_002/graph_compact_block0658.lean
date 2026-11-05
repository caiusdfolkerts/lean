module
prelude
import GraphInputsRow29Part00224Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0658
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 2
 (.branch 1
 (.leaf ⟨(29, 30314164977664), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00224.record000_result⟩)
 (.leaf ⟨(29, 30314416179216), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00224.record001_result⟩))
 (.branch 3
 (.leaf ⟨(29, 30314432823824), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00224.record002_result⟩)
 (.branch 4
 (.leaf ⟨(29, 30315363958784), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00224.record003_result⟩)
 (.leaf ⟨(29, 30378589487104), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00224.record004_result⟩))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (23166 + i))) 0 5 :=
  interval_of_check _ 0 5 (by decide +kernel)

public theorem complete : Block 23166 23171 :=
  block_of_table results 23166 5 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0658
