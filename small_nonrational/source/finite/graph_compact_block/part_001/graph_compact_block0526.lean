module
prelude
import GraphInputsRow29Part00092Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0526
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(29, 16496472424448), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00092.record000_result⟩)
 (.branch 2
 (.leaf ⟨(29, 16496476585984), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00092.record001_result⟩)
 (.leaf ⟨(29, 16496567288064), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00092.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(29, 16496579317760), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00092.record003_result⟩)
 (.branch 5
 (.leaf ⟨(29, 16502952562688), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00092.record004_result⟩)
 (.leaf ⟨(29, 16504083452160), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00092.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(29, 16511274061824), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00092.record006_result⟩)
 (.branch 8
 (.leaf ⟨(29, 16511499518080), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00092.record007_result⟩)
 (.leaf ⟨(29, 16511501631488), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00092.record008_result⟩)))
 (.branch 11
 (.branch 10
 (.leaf ⟨(29, 16511532548224), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00092.record009_result⟩)
 (.leaf ⟨(29, 16512673386624), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00092.record010_result⟩))
 (.branch 12
 (.leaf ⟨(29, 16527189610752), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00092.record011_result⟩)
 (.leaf ⟨(29, 16531606079504), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00092.record012_result⟩)))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (21793 + i))) 0 13 :=
  interval_of_check _ 0 13 (by decide +kernel)

public theorem complete : Block 21793 21806 :=
  block_of_table results 21793 13 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0526
