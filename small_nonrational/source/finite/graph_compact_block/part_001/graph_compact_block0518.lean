module
prelude
import GraphInputsRow29Part00084Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0518
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf ⟨(29, 13900394299648), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00084.record000_result⟩)
 (.leaf ⟨(29, 13900405809152), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00084.record001_result⟩))
 (.branch 3
 (.leaf ⟨(29, 13907909943552), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00084.record002_result⟩)
 (.branch 4
 (.leaf ⟨(29, 13929392701440), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00084.record003_result⟩)
 (.leaf ⟨(29, 13933440139265), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00084.record004_result⟩))))
 (.branch 8
 (.branch 6
 (.leaf ⟨(29, 13937978441728), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00084.record005_result⟩)
 (.branch 7
 (.leaf ⟨(29, 13937986764800), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00084.record006_result⟩)
 (.leaf ⟨(29, 13975894950144), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00084.record007_result⟩)))
 (.branch 9
 (.leaf ⟨(29, 13976630001664), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00084.record008_result⟩)
 (.branch 10
 (.leaf ⟨(29, 14027929423904), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00084.record009_result⟩)
 (.leaf ⟨(29, 14294884909088), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00084.record010_result⟩)))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (21677 + i))) 0 11 :=
  interval_of_check _ 0 11 (by decide +kernel)

public theorem complete : Block 21677 21688 :=
  block_of_table results 21677 11 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0518
