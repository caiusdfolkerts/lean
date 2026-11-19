module
prelude
import GraphInputsRow29Part00021Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0455
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(29, 5026529477376), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00021.record000_result⟩)
 (.branch 2
 (.leaf ⟨(29, 5026730967072), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00021.record001_result⟩)
 (.leaf ⟨(29, 5089830445312), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00021.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(29, 5104109453312), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00021.record003_result⟩)
 (.branch 5
 (.leaf ⟨(29, 5104178569472), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00021.record004_result⟩)
 (.leaf ⟨(29, 5123505979392), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00021.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(29, 5137345118208), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00021.record006_result⟩)
 (.branch 8
 (.leaf ⟨(29, 5138460737792), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00021.record007_result⟩)
 (.leaf ⟨(29, 5140140589312), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00021.record008_result⟩)))
 (.branch 11
 (.branch 10
 (.leaf ⟨(29, 5140413218816), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00021.record009_result⟩)
 (.leaf ⟨(29, 5140677459968), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00021.record010_result⟩))
 (.branch 12
 (.leaf ⟨(29, 5140685783040), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00021.record011_result⟩)
 (.leaf ⟨(29, 5140950024192), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00021.record012_result⟩)))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (20811 + i))) 0 13 :=
  interval_of_check _ 0 13 (by decide +kernel)

public theorem complete : Block 20811 20824 :=
  block_of_table results 20811 13 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0455
