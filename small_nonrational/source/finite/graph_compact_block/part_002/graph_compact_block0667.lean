module
prelude
import GraphInputsRow29Part00233Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0667
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 2
 (.branch 1
 (.leaf ⟨(29, 31336136249376), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00233.record000_result⟩)
 (.leaf ⟨(29, 31337449267456), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00233.record001_result⟩))
 (.branch 3
 (.leaf ⟨(29, 31337717702784), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00233.record002_result⟩)
 (.branch 4
 (.leaf ⟨(29, 31346048172288), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00233.record003_result⟩)
 (.leaf ⟨(29, 31346316574976), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00233.record004_result⟩))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (23281 + i))) 0 5 :=
  interval_of_check _ 0 5 (by decide +kernel)

public theorem complete : Block 23281 23286 :=
  block_of_table results 23281 5 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0667
