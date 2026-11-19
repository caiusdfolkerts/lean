module
prelude
import GraphInputsRow29Part00083Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0517
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf ⟨(29, 13752779477024), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00083.record000_result⟩)
 (.leaf ⟨(29, 13753043718176), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00083.record001_result⟩))
 (.branch 3
 (.leaf ⟨(29, 13754142040320), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00083.record002_result⟩)
 (.branch 4
 (.leaf ⟨(29, 13762731974784), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00083.record003_result⟩)
 (.leaf ⟨(29, 13890486804736), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00083.record004_result⟩))))
 (.branch 7
 (.branch 6
 (.leaf ⟨(29, 13890486870016), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00083.record005_result⟩)
 (.leaf ⟨(29, 13899076739200), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00083.record006_result⟩))
 (.branch 8
 (.leaf ⟨(29, 13899080405024), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00083.record007_result⟩)
 (.branch 9
 (.leaf ⟨(29, 13899936104448), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00083.record008_result⟩)
 (.leaf ⟨(29, 13900204474369), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00083.record009_result⟩)))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (21667 + i))) 0 10 :=
  interval_of_check _ 0 10 (by decide +kernel)

public theorem complete : Block 21667 21677 :=
  block_of_table results 21667 10 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0517
