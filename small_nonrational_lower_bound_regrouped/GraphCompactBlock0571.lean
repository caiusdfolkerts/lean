module
prelude
import GraphInputsRow29Part00137Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0571
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(29, 23555884515328), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00137.record000_result⟩)
 (.branch 2
 (.leaf ⟨(29, 23556421320704), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00137.record001_result⟩)
 (.leaf ⟨(29, 23557964890112), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00137.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(29, 23590713950208), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00137.record003_result⟩)
 (.branch 5
 (.leaf ⟨(29, 23679505334528), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00137.record004_result⟩)
 (.leaf ⟨(29, 23680042205184), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00137.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(29, 23683666084096), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00137.record006_result⟩)
 (.branch 8
 (.leaf ⟨(29, 23684202954752), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00137.record007_result⟩)
 (.leaf ⟨(29, 23686786646272), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00137.record008_result⟩)))
 (.branch 11
 (.branch 10
 (.leaf ⟨(29, 23692251824384), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00137.record009_result⟩)
 (.leaf ⟨(29, 23692524453888), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00137.record010_result⟩))
 (.branch 12
 (.leaf ⟨(29, 23692788695040), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00137.record011_result⟩)
 (.leaf ⟨(29, 23692797018112), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00137.record012_result⟩)))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (22481 + i))) 0 13 :=
  interval_of_check _ 0 13 (by decide +kernel)

public theorem complete : Block 22481 22494 :=
  block_of_table results 22481 13 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0571
