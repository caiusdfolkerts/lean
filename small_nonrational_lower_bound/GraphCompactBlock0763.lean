module
prelude
import GraphInputsRow30Part00035Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0763
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 12
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(30, 20736505053184), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00035.record000_result⟩)
 (.branch 2
 (.leaf ⟨(30, 20744692187264), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00035.record001_result⟩)
 (.leaf ⟨(30, 20748987170816), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00035.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(30, 20749255573504), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00035.record003_result⟩)
 (.branch 5
 (.leaf ⟨(30, 20758856269824), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00035.record004_result⟩)
 (.leaf ⟨(30, 20792608063488), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00035.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(30, 20800937656320), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00035.record006_result⟩)
 (.branch 8
 (.leaf ⟨(30, 20824304189440), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00035.record007_result⟩)
 (.leaf ⟨(30, 20824820318208), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00035.record008_result⟩)))
 (.branch 10
 (.leaf ⟨(30, 20826900692992), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00035.record009_result⟩)
 (.branch 11
 (.leaf ⟨(30, 20839382941696), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00035.record010_result⟩)
 (.leaf ⟨(30, 20896260587776), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00035.record011_result⟩)))))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf ⟨(30, 20929529282816), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00035.record012_result⟩)
 (.branch 14
 (.leaf ⟨(30, 20931130982400), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00035.record013_result⟩)
 (.leaf ⟨(30, 20977905860608), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00035.record014_result⟩)))
 (.branch 16
 (.leaf ⟨(30, 21007368716288), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00035.record015_result⟩)
 (.branch 17
 (.leaf ⟨(30, 21015946068608), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00035.record016_result⟩)
 (.leaf ⟨(30, 21076086095872), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00035.record017_result⟩))))
 (.branch 21
 (.branch 19
 (.leaf ⟨(30, 21119160565760), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00035.record018_result⟩)
 (.branch 20
 (.leaf ⟨(30, 21257072410624), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00035.record019_result⟩)
 (.leaf ⟨(30, 21350955614208), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00035.record020_result⟩)))
 (.branch 22
 (.leaf ⟨(30, 21367598612480), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00035.record021_result⟩)
 (.branch 23
 (.leaf ⟨(30, 21374041096448), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00035.record022_result⟩)
 (.leaf ⟨(30, 21378338193408), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00035.record023_result⟩))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (24697 + i))) 0 24 :=
  interval_of_check _ 0 24 (by decide +kernel)

public theorem complete : Block 24697 24721 :=
  block_of_table results 24697 24 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0763
