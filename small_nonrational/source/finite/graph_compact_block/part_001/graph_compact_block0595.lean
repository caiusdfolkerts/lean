module
prelude
import GraphInputsRow29Part00161Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0595
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(29, 25194833903616), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00161.record000_result⟩)
 (.branch 2
 (.leaf ⟨(29, 25194949509120), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00161.record001_result⟩)
 (.leaf ⟨(29, 25198573322240), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00161.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(29, 25211458174976), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00161.record003_result⟩)
 (.branch 5
 (.leaf ⟨(29, 25215753125888), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00161.record004_result⟩)
 (.leaf ⟨(29, 25226767237120), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00161.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(29, 25328634364160), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00161.record006_result⟩)
 (.branch 8
 (.leaf ⟨(29, 25328906993664), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00161.record007_result⟩)
 (.leaf ⟨(29, 25329171234816), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00161.record008_result⟩)))
 (.branch 11
 (.branch 10
 (.leaf ⟨(29, 25329179557888), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00161.record009_result⟩)
 (.leaf ⟨(29, 25329303355392), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00161.record010_result⟩))
 (.branch 12
 (.leaf ⟨(29, 25332927234304), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00161.record011_result⟩)
 (.leaf ⟨(29, 25333464104960), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00161.record012_result⟩)))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (22688 + i))) 0 13 :=
  interval_of_check _ 0 13 (by decide +kernel)

public theorem complete : Block 22688 22701 :=
  block_of_table results 22688 13 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0595
