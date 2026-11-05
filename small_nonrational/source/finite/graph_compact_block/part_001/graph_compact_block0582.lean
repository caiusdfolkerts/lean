module
prelude
import GraphInputsRow29Part00148Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0582
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 3
 (.branch 1
 (.leaf ⟨(29, 24573655548160), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00148.record000_result⟩)
 (.branch 2
 (.leaf ⟨(29, 24578361393152), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00148.record001_result⟩)
 (.leaf ⟨(29, 24584594423808), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00148.record002_result⟩)))
 (.branch 5
 (.branch 4
 (.leaf ⟨(29, 24590835417088), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00148.record003_result⟩)
 (.leaf ⟨(29, 24591103819776), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00148.record004_result⟩))
 (.branch 6
 (.leaf ⟨(29, 24638216241408), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00148.record005_result⟩)
 (.leaf ⟨(29, 24642513338368), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00148.record006_result⟩))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (22596 + i))) 0 7 :=
  interval_of_check _ 0 7 (by decide +kernel)

public theorem complete : Block 22596 22603 :=
  block_of_table results 22596 7 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0582
