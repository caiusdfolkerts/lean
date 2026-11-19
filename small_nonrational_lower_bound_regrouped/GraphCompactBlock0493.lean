module
prelude
import GraphInputsRow29Part00059Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0493
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(29, 11040622383360), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00059.record000_result⟩)
 (.branch 2
 (.leaf ⟨(29, 11070022361216), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00059.record001_result⟩)
 (.leaf ⟨(29, 11074183110784), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00059.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(29, 11082504609920), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00059.record003_result⟩)
 (.branch 5
 (.leaf ⟨(29, 11109616615424), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00059.record004_result⟩)
 (.leaf ⟨(29, 11118330282112), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00059.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(29, 11189196177536), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00059.record006_result⟩)
 (.branch 8
 (.leaf ⟨(29, 11238073499648), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00059.record007_result⟩)
 (.leaf ⟨(29, 11242894786560), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00059.record008_result⟩)))
 (.branch 10
 (.leaf ⟨(29, 11246774518528), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00059.record009_result⟩)
 (.branch 11
 (.leaf ⟨(29, 11247055536128), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00059.record010_result⟩)
 (.leaf ⟨(29, 11255769235456), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00059.record011_result⟩)))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (21334 + i))) 0 12 :=
  interval_of_check _ 0 12 (by decide +kernel)

public theorem complete : Block 21334 21346 :=
  block_of_table results 21334 12 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0493
