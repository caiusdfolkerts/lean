module
prelude
import GraphInputsRow23Part00034Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0112
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 8
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨(23, 34125394215424), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00034.record000_result⟩)
 (.leaf ⟨(23, 34127827452160), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00034.record001_result⟩))
 (.branch 3
 (.leaf ⟨(23, 34128364322816), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00034.record002_result⟩)
 (.leaf ⟨(23, 34128481488896), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00034.record003_result⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨(23, 34128884023552), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00034.record004_result⟩)
 (.leaf ⟨(23, 34129554964992), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00034.record005_result⟩))
 (.branch 7
 (.leaf ⟨(23, 34159020015616), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00034.record006_result⟩)
 (.leaf ⟨(23, 34160060203008), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00034.record007_result⟩))))
 (.branch 12
 (.branch 10
 (.branch 9
 (.leaf ⟨(23, 34194658951168), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00034.record008_result⟩)
 (.leaf ⟨(23, 34224598482944), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00034.record009_result⟩))
 (.branch 11
 (.leaf ⟨(23, 34225001086976), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00034.record010_result⟩)
 (.leaf ⟨(23, 34239496593472), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00034.record011_result⟩)))
 (.branch 14
 (.branch 13
 (.leaf ⟨(23, 34239680876544), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00034.record012_result⟩)
 (.leaf ⟨(23, 34240553164864), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00034.record013_result⟩))
 (.branch 15
 (.leaf ⟨(23, 34240754352640), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00034.record014_result⟩)
 (.branch 16
 (.leaf ⟨(23, 34241626902592), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00034.record015_result⟩)
 (.leaf ⟨(23, 34497194631232), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00034.record016_result⟩))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (7727 + i))) 0 17 :=
  interval_of_check _ 0 17 (by decide +kernel)

public theorem complete : Block 7727 7744 :=
  block_of_table results 7727 17 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0112
