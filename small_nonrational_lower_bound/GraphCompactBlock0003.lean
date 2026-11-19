module
prelude
import GraphInputsRow16Part00003Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0003
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 31
 (.branch 15
 (.branch 7
 (.branch 3
 (.branch 1
 (.leaf ⟨(16, 8570481410048), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00003.record000_result⟩)
 (.branch 2
 (.leaf ⟨(16, 8585675309312), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00003.record001_result⟩)
 (.leaf ⟨(16, 8585811656704), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00003.record002_result⟩)))
 (.branch 5
 (.branch 4
 (.leaf ⟨(16, 8585819979776), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00003.record003_result⟩)
 (.leaf ⟨(16, 8586042867712), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00003.record004_result⟩))
 (.branch 6
 (.leaf ⟨(16, 8586216341504), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00003.record005_result⟩)
 (.leaf ⟨(16, 8586579673088), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00003.record006_result⟩))))
 (.branch 11
 (.branch 9
 (.branch 8
 (.leaf ⟨(16, 8593571119104), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00003.record007_result⟩)
 (.leaf ⟨(16, 8593963254016), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00003.record008_result⟩))
 (.branch 10
 (.leaf ⟨(16, 8595651493888), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00003.record009_result⟩)
 (.leaf ⟨(16, 8597194936320), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00003.record010_result⟩)))
 (.branch 13
 (.branch 12
 (.leaf ⟨(16, 8599812243456), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00003.record011_result⟩)
 (.leaf ⟨(16, 8601355685888), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00003.record012_result⟩))
 (.branch 14
 (.leaf ⟨(16, 8605549985792), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00003.record013_result⟩)
 (.leaf ⟨(16, 8605772873728), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00003.record014_result⟩)))))
 (.branch 23
 (.branch 19
 (.branch 17
 (.branch 16
 (.leaf ⟨(16, 8609677185024), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00003.record015_result⟩)
 (.leaf ⟨(16, 8616847376640), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00003.record016_result⟩))
 (.branch 18
 (.leaf ⟨(16, 8616983724032), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00003.record017_result⟩)
 (.leaf ⟨(16, 8616992047104), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00003.record018_result⟩)))
 (.branch 21
 (.branch 20
 (.leaf ⟨(16, 8617256288256), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00003.record019_result⟩)
 (.leaf ⟨(16, 8617388408832), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00003.record020_result⟩))
 (.branch 22
 (.leaf ⟨(16, 8617887564032), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00003.record021_result⟩)
 (.leaf ⟨(16, 8618023911424), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00003.record022_result⟩))))
 (.branch 27
 (.branch 25
 (.branch 24
 (.leaf ⟨(16, 8618032234496), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00003.record023_result⟩)
 (.leaf ⟨(16, 8618255122432), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00003.record024_result⟩))
 (.branch 26
 (.leaf ⟨(16, 8618428596224), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00003.record025_result⟩)
 (.leaf ⟨(16, 8618791927808), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00003.record026_result⟩)))
 (.branch 29
 (.branch 28
 (.leaf ⟨(16, 8628887158784), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00003.record027_result⟩)
 (.leaf ⟨(16, 8629394899200), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00003.record028_result⟩))
 (.branch 30
 (.leaf ⟨(16, 8629407188992), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00003.record029_result⟩)
 (.leaf ⟨(16, 8633567938560), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00003.record030_result⟩))))))
 (.branch 46
 (.branch 38
 (.branch 34
 (.branch 32
 (.leaf ⟨(16, 8641889437696), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00003.record031_result⟩)
 (.branch 33
 (.leaf ⟨(16, 8654359265536), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00003.record032_result⟩)
 (.leaf ⟨(16, 8654627733504), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00003.record033_result⟩)))
 (.branch 36
 (.branch 35
 (.leaf ⟨(16, 8654636056576), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00003.record034_result⟩)
 (.leaf ⟨(16, 8655164408320), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00003.record035_result⟩))
 (.branch 37
 (.leaf ⟨(16, 8665768165632), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00003.record036_result⟩)
 (.leaf ⟨(16, 8682448420864), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00003.record037_result⟩))))
 (.branch 42
 (.branch 40
 (.branch 39
 (.leaf ⟨(16, 8682456743936), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00003.record038_result⟩)
 (.leaf ⟨(16, 8697980158208), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00003.record039_result⟩))
 (.branch 41
 (.leaf ⟨(16, 8727533289472), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00003.record040_result⟩)
 (.leaf ⟨(16, 8729676284160), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00003.record041_result⟩)))
 (.branch 44
 (.branch 43
 (.leaf ⟨(16, 8729684672512), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00003.record042_result⟩)
 (.leaf ⟨(16, 8730076807424), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00003.record043_result⟩))
 (.branch 45
 (.leaf ⟨(16, 8730081034240), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00003.record044_result⟩)
 (.leaf ⟨(16, 8730192412928), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00003.record045_result⟩)))))
 (.branch 54
 (.branch 50
 (.branch 48
 (.branch 47
 (.leaf ⟨(16, 8730204702720), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00003.record046_result⟩)
 (.leaf ⟨(16, 8730733248768), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00003.record047_result⟩))
 (.branch 49
 (.leaf ⟨(16, 8731005878272), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00003.record048_result⟩)
 (.leaf ⟨(16, 8731270119424), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00003.record049_result⟩)))
 (.branch 52
 (.branch 51
 (.leaf ⟨(16, 8731945535488), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00003.record050_result⟩)
 (.leaf ⟨(16, 8731963228160), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00003.record051_result⟩))
 (.branch 53
 (.leaf ⟨(16, 8732004385024), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00003.record052_result⟩)
 (.leaf ⟨(16, 8732227469312), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00003.record053_result⟩))))
 (.branch 58
 (.branch 56
 (.branch 55
 (.leaf ⟨(16, 8732272787712), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00003.record054_result⟩)
 (.leaf ⟨(16, 8732285077504), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00003.record055_result⟩))
 (.branch 57
 (.leaf ⟨(16, 8733086253056), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00003.record056_result⟩)
 (.leaf ⟨(16, 8733350494208), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00003.record057_result⟩)))
 (.branch 60
 (.branch 59
 (.leaf ⟨(16, 8733358817280), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00003.record058_result⟩)
 (.leaf ⟨(16, 8734621303552), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00003.record059_result⟩))
 (.branch 61
 (.leaf ⟨(16, 8735166627840), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00003.record060_result⟩)
 (.leaf ⟨(16, 8735703433216), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00003.record061_result⟩)))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (268 + i))) 0 62 :=
  interval_of_check _ 0 62 (by decide +kernel)

public theorem complete : Block 268 330 :=
  block_of_table results 268 62 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0003
