module
prelude
import GraphInputsRow29Part00070Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0504
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf ⟨(29, 12320784777856), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00070.record000_result⟩)
 (.leaf ⟨(29, 12376351473920), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00070.record001_result⟩))
 (.branch 3
 (.leaf ⟨(29, 12376363503616), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00070.record002_result⟩)
 (.branch 4
 (.leaf ⟨(29, 12376619909248), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00070.record003_result⟩)
 (.leaf ⟨(29, 12376754110592), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00070.record004_result⟩))))
 (.branch 8
 (.branch 6
 (.leaf ⟨(29, 12380656373760), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00070.record005_result⟩)
 (.branch 7
 (.leaf ⟨(29, 12380914860160), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00070.record006_result⟩)
 (.leaf ⟨(29, 12382802808832), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00070.record007_result⟩)))
 (.branch 9
 (.leaf ⟨(29, 12382995234944), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00070.record008_result⟩)
 (.branch 10
 (.leaf ⟨(29, 12387962880128), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00070.record009_result⟩)
 (.leaf ⟨(29, 12387967074304), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00070.record010_result⟩)))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (21480 + i))) 0 11 :=
  interval_of_check _ 0 11 (by decide +kernel)

public theorem complete : Block 21480 21491 :=
  block_of_table results 21480 11 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0504
