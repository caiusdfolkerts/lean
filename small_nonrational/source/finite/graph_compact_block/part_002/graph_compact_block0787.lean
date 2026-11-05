module
prelude
import GraphInputsRow30Part00059Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0787
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(30, 34737716527104), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00059.record000_result⟩)
 (.branch 2
 (.leaf ⟨(30, 34739046055936), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00059.record001_result⟩)
 (.leaf ⟨(30, 34763465424896), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00059.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(30, 34763498848256), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00059.record003_result⟩)
 (.branch 5
 (.leaf ⟨(30, 34789235230736), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00059.record004_result⟩)
 (.leaf ⟨(30, 34790308839940), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00059.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(30, 34840774838528), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00059.record006_result⟩)
 (.branch 8
 (.leaf ⟨(30, 34875159609344), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00059.record007_result⟩)
 (.leaf ⟨(30, 34892331089920), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00059.record008_result⟩)))
 (.branch 10
 (.leaf ⟨(30, 35115652745216), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00059.record009_result⟩)
 (.branch 11
 (.leaf ⟨(30, 35115669651456), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00059.record010_result⟩)
 (.leaf ⟨(30, 35150029127680), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00059.record011_result⟩)))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (25430 + i))) 0 12 :=
  interval_of_check _ 0 12 (by decide +kernel)

public theorem complete : Block 25430 25442 :=
  block_of_table results 25430 12 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0787
