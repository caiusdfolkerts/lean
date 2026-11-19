module
prelude
import GraphInputsRow25Part00024Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0314
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 26
 (.branch 13
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(25, 34128364322816), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00024.record000_result⟩)
 (.branch 2
 (.leaf ⟨(25, 34128481488896), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00024.record001_result⟩)
 (.leaf ⟨(25, 34128884023552), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00024.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(25, 34129554964992), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00024.record003_result⟩)
 (.branch 5
 (.leaf ⟨(25, 34132105236736), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00024.record004_result⟩)
 (.leaf ⟨(25, 34144990138432), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00024.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(25, 34159020015616), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00024.record006_result⟩)
 (.branch 8
 (.leaf ⟨(25, 34160060203008), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00024.record007_result⟩)
 (.leaf ⟨(25, 34213709480452), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00024.record008_result⟩)))
 (.branch 11
 (.branch 10
 (.leaf ⟨(25, 34224598482944), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00024.record009_result⟩)
 (.leaf ⟨(25, 34225001086976), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00024.record010_result⟩))
 (.branch 12
 (.leaf ⟨(25, 34228742000896), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00024.record011_result⟩)
 (.leaf ⟨(25, 34239496593472), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00024.record012_result⟩)))))
 (.branch 19
 (.branch 16
 (.branch 14
 (.leaf ⟨(25, 34239680876544), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00024.record013_result⟩)
 (.branch 15
 (.leaf ⟨(25, 34240553164864), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00024.record014_result⟩)
 (.leaf ⟨(25, 34240754352640), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00024.record015_result⟩)))
 (.branch 17
 (.leaf ⟨(25, 34241626902592), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00024.record016_result⟩)
 (.branch 18
 (.leaf ⟨(25, 34278133989892), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00024.record017_result⟩)
 (.leaf ⟨(25, 34497194631232), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00024.record018_result⟩))))
 (.branch 22
 (.branch 20
 (.leaf ⟨(25, 34498268905472), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00024.record019_result⟩)
 (.branch 21
 (.leaf ⟨(25, 34498337046528), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00024.record020_result⟩)
 (.leaf ⟨(25, 34498452652032), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00024.record021_result⟩)))
 (.branch 24
 (.branch 23
 (.leaf ⟨(25, 34500398694400), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00024.record022_result⟩)
 (.leaf ⟨(25, 34531537193024), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00024.record023_result⟩))
 (.branch 25
 (.leaf ⟨(25, 34531554115584), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00024.record024_result⟩)
 (.leaf ⟨(25, 34531688316928), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00024.record025_result⟩))))))
 (.branch 39
 (.branch 32
 (.branch 29
 (.branch 27
 (.leaf ⟨(25, 34535832160256), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00024.record026_result⟩)
 (.branch 28
 (.leaf ⟨(25, 34634666873088), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00024.record027_result⟩)
 (.leaf ⟨(25, 34634667458560), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00024.record028_result⟩)))
 (.branch 30
 (.leaf ⟨(25, 34634675261440), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00024.record029_result⟩)
 (.branch 31
 (.leaf ⟨(25, 34635170189328), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00024.record030_result⟩)
 (.leaf ⟨(25, 34635725701376), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00024.record031_result⟩))))
 (.branch 35
 (.branch 33
 (.leaf ⟨(25, 34635752931328), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00024.record032_result⟩)
 (.branch 34
 (.leaf ⟨(25, 34635759255808), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00024.record033_result⟩)
 (.leaf ⟨(25, 34635975819264), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00024.record034_result⟩)))
 (.branch 37
 (.branch 36
 (.leaf ⟨(25, 34635984142336), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00024.record035_result⟩)
 (.leaf ⟨(25, 34636243665424), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00024.record036_result⟩))
 (.branch 38
 (.leaf ⟨(25, 34636495589376), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00024.record037_result⟩)
 (.leaf ⟨(25, 34640022798336), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00024.record038_result⟩)))))
 (.branch 46
 (.branch 42
 (.branch 40
 (.leaf ⟨(25, 34640295362560), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00024.record039_result⟩)
 (.branch 41
 (.leaf ⟨(25, 34640790814720), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00024.record040_result⟩)
 (.leaf ⟨(25, 34643223515392), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00024.record041_result⟩)))
 (.branch 44
 (.branch 43
 (.leaf ⟨(25, 34643760386048), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00024.record042_result⟩)
 (.leaf ⟨(25, 34643776901120), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00024.record043_result⟩))
 (.branch 45
 (.leaf ⟨(25, 34644280086784), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00024.record044_result⟩)
 (.leaf ⟨(25, 34644850377216), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00024.record045_result⟩))))
 (.branch 49
 (.branch 47
 (.leaf ⟨(25, 34647535321088), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00024.record046_result⟩)
 (.branch 48
 (.leaf ⟨(25, 34660386213904), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00024.record047_result⟩)
 (.leaf ⟨(25, 34670188232704), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00024.record048_result⟩)))
 (.branch 51
 (.branch 50
 (.leaf ⟨(25, 34674621546496), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00024.record049_result⟩)
 (.leaf ⟨(25, 34675150028800), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00024.record050_result⟩))
 (.branch 52
 (.leaf ⟨(25, 34681902858240), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00024.record051_result⟩)
 (.leaf ⟨(25, 34703353086208), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00024.record052_result⟩)))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (13946 + i))) 0 53 :=
  interval_of_check _ 0 53 (by decide +kernel)

public theorem complete : Block 13946 13999 :=
  block_of_table results 13946 53 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0314
