module
prelude
import GraphInputsRow30Part00057Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0785
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 13
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(30, 34123800969216), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00057.record000_result⟩)
 (.branch 2
 (.leaf ⟨(30, 34123809292288), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00057.record001_result⟩)
 (.leaf ⟨(30, 34124320739328), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00057.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(30, 34124589072640), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00057.record003_result⟩)
 (.branch 5
 (.leaf ⟨(30, 34124865863680), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00057.record004_result⟩)
 (.leaf ⟨(30, 34125394215424), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00057.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(30, 34127827452160), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00057.record006_result⟩)
 (.branch 8
 (.leaf ⟨(30, 34128364322816), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00057.record007_result⟩)
 (.leaf ⟨(30, 34128481488896), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00057.record008_result⟩)))
 (.branch 11
 (.branch 10
 (.leaf ⟨(30, 34128884023552), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00057.record009_result⟩)
 (.leaf ⟨(30, 34129554964992), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00057.record010_result⟩))
 (.branch 12
 (.leaf ⟨(30, 34132105236736), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00057.record011_result⟩)
 (.leaf ⟨(30, 34144990138432), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00057.record012_result⟩)))))
 (.branch 19
 (.branch 16
 (.branch 14
 (.leaf ⟨(30, 34159020015616), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00057.record013_result⟩)
 (.branch 15
 (.leaf ⟨(30, 34160060203008), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00057.record014_result⟩)
 (.leaf ⟨(30, 34213709480452), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00057.record015_result⟩)))
 (.branch 17
 (.leaf ⟨(30, 34224598482944), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00057.record016_result⟩)
 (.branch 18
 (.leaf ⟨(30, 34225001086976), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00057.record017_result⟩)
 (.leaf ⟨(30, 34228742000896), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00057.record018_result⟩))))
 (.branch 22
 (.branch 20
 (.leaf ⟨(30, 34239496593472), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00057.record019_result⟩)
 (.branch 21
 (.leaf ⟨(30, 34239680876544), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00057.record020_result⟩)
 (.leaf ⟨(30, 34240553164864), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00057.record021_result⟩)))
 (.branch 24
 (.branch 23
 (.leaf ⟨(30, 34240754352640), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00057.record022_result⟩)
 (.leaf ⟨(30, 34241626902592), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00057.record023_result⟩))
 (.branch 25
 (.leaf ⟨(30, 34278133989892), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00057.record024_result⟩)
 (.leaf ⟨(30, 34497194631232), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00057.record025_result⟩))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (25363 + i))) 0 26 :=
  interval_of_check _ 0 26 (by decide +kernel)

public theorem complete : Block 25363 25389 :=
  block_of_table results 25363 26 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0785
