module
prelude
import GraphInputsRow29Part00006Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0440
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 7
 (.branch 3
 (.branch 1
 (.leaf ⟨(29, 2004013875200), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00006.record000_result⟩)
 (.branch 2
 (.leaf ⟨(29, 2004174799104), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00006.record001_result⟩)
 (.leaf ⟨(29, 2015157551105), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00006.record002_result⟩)))
 (.branch 5
 (.branch 4
 (.leaf ⟨(29, 2019442065664), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00006.record003_result⟩)
 (.leaf ⟨(29, 2019452518401), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00006.record004_result⟩))
 (.branch 6
 (.leaf ⟨(29, 2019452534784), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00006.record005_result⟩)
 (.leaf ⟨(29, 2019777609984), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00006.record006_result⟩))))
 (.branch 10
 (.branch 8
 (.leaf ⟨(29, 2019913957376), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00006.record007_result⟩)
 (.branch 9
 (.leaf ⟨(29, 2019922280448), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00006.record008_result⟩)
 (.leaf ⟨(29, 2020318642176), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00006.record009_result⟩)))
 (.branch 12
 (.branch 11
 (.leaf ⟨(29, 2031809003776), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00006.record010_result⟩)
 (.leaf ⟨(29, 2031817392128), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00006.record011_result⟩))
 (.branch 13
 (.leaf ⟨(29, 2032325132544), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00006.record012_result⟩)
 (.leaf ⟨(29, 2032337422336), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00006.record013_result⟩)))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (20584 + i))) 0 14 :=
  interval_of_check _ 0 14 (by decide +kernel)

public theorem complete : Block 20584 20598 :=
  block_of_table results 20584 14 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0440
