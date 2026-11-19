module
prelude
import GraphInputsRow26Part00046Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0362
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 12
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(26, 24447155470592), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00046.record000_result⟩)
 (.branch 2
 (.leaf ⟨(26, 24447167760384), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00046.record001_result⟩)
 (.leaf ⟨(26, 24447299880960), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00046.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(26, 24447365941248), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00046.record003_result⟩)
 (.branch 5
 (.leaf ⟨(26, 24447759425600), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00046.record004_result⟩)
 (.leaf ⟨(26, 24449906639424), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00046.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(26, 24457691414784), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00046.record006_result⟩)
 (.branch 8
 (.leaf ⟨(26, 24457825681408), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00046.record007_result⟩)
 (.leaf ⟨(26, 24457834004480), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00046.record008_result⟩)))
 (.branch 10
 (.leaf ⟨(26, 24458228285440), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00046.record009_result⟩)
 (.branch 11
 (.leaf ⟨(26, 24458362356224), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00046.record010_result⟩)
 (.leaf ⟨(26, 24471761092608), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00046.record011_result⟩)))))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf ⟨(26, 24471827152896), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00046.record012_result⟩)
 (.branch 14
 (.leaf ⟨(26, 24484705763328), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00046.record013_result⟩)
 (.leaf ⟨(26, 24499721371904), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00046.record014_result⟩)))
 (.branch 16
 (.leaf ⟨(26, 24502123692032), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00046.record015_result⟩)
 (.branch 17
 (.leaf ⟨(26, 24502965635200), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00046.record016_result⟩)
 (.leaf ⟨(26, 24504204066816), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00046.record017_result⟩))))
 (.branch 21
 (.branch 19
 (.leaf ⟨(26, 24508560851200), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00046.record018_result⟩)
 (.branch 20
 (.leaf ⟨(26, 24512789807104), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00046.record019_result⟩)
 (.leaf ⟨(26, 24512798130176), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00046.record020_result⟩)))
 (.branch 23
 (.branch 22
 (.leaf ⟨(26, 24513258471424), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00046.record021_result⟩)
 (.leaf ⟨(26, 24513326612480), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00046.record022_result⟩))
 (.branch 24
 (.leaf ⟨(26, 24515844245632), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00046.record023_result⟩)
 (.leaf ⟨(26, 24518229753857), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00046.record024_result⟩))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (16476 + i))) 0 25 :=
  interval_of_check _ 0 25 (by decide +kernel)

public theorem complete : Block 16476 16501 :=
  block_of_table results 16476 25 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0362
