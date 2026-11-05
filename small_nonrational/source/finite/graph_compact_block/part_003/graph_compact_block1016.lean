module
prelude
import GraphInputsSix0Part00051Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock1016
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 50
 (.branch 25
 (.branch 12
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(32, 19684406607872), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00051.record000_result⟩)
 (.branch 2
 (.leaf ⟨(32, 19692580307200), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00051.record001_result⟩)
 (.leaf ⟨(32, 19692588695552), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00051.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(32, 19692712427776), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00051.record003_result⟩)
 (.branch 5
 (.leaf ⟨(32, 19692720816128), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00051.record004_result⟩)
 (.leaf ⟨(32, 19692828033280), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00051.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(32, 19692980830464), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00051.record006_result⟩)
 (.branch 8
 (.leaf ⟨(32, 19692985057280), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00051.record007_result⟩)
 (.leaf ⟨(32, 19692991299584), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00051.record008_result⟩)))
 (.branch 10
 (.leaf ⟨(32, 19693096435968), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00051.record009_result⟩)
 (.branch 11
 (.leaf ⟨(32, 19693108725760), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00051.record010_result⟩)
 (.leaf ⟨(32, 19693230637312), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00051.record011_result⟩)))))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf ⟨(32, 19697275781376), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00051.record012_result⟩)
 (.branch 14
 (.leaf ⟨(32, 19697284169728), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00051.record013_result⟩)
 (.leaf ⟨(32, 19697391386880), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00051.record014_result⟩)))
 (.branch 16
 (.leaf ⟨(32, 19697401595904), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00051.record015_result⟩)
 (.branch 17
 (.leaf ⟨(32, 19701686076160), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00051.record016_result⟩)
 (.leaf ⟨(32, 19705712886016), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00051.record017_result⟩))))
 (.branch 21
 (.branch 19
 (.leaf ⟨(32, 19705723095040), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00051.record018_result⟩)
 (.branch 20
 (.leaf ⟨(32, 19705869910016), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00051.record019_result⟩)
 (.leaf ⟨(32, 19706115539008), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00051.record020_result⟩)))
 (.branch 23
 (.branch 22
 (.leaf ⟨(32, 19710410228288), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00051.record021_result⟩)
 (.leaf ⟨(32, 19718195003648), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00051.record022_result⟩))
 (.branch 24
 (.leaf ⟨(32, 19718329270272), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00051.record023_result⟩)
 (.leaf ⟨(32, 19718337593344), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00051.record024_result⟩))))))
 (.branch 37
 (.branch 31
 (.branch 28
 (.branch 26
 (.leaf ⟨(32, 19718731874304), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00051.record025_result⟩)
 (.branch 27
 (.leaf ⟨(32, 19718865945088), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00051.record026_result⟩)
 (.leaf ⟨(32, 19724792561920), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00051.record027_result⟩)))
 (.branch 29
 (.leaf ⟨(32, 19724800950272), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00051.record028_result⟩)
 (.branch 30
 (.leaf ⟨(32, 19724924682496), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00051.record029_result⟩)
 (.leaf ⟨(32, 19724933070848), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00051.record030_result⟩))))
 (.branch 34
 (.branch 32
 (.leaf ⟨(32, 19725040288000), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00051.record031_result⟩)
 (.branch 33
 (.leaf ⟨(32, 19725193085184), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00051.record032_result⟩)
 (.leaf ⟨(32, 19725197312000), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00051.record033_result⟩)))
 (.branch 35
 (.leaf ⟨(32, 19725203554304), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00051.record034_result⟩)
 (.branch 36
 (.leaf ⟨(32, 19725308690688), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00051.record035_result⟩)
 (.leaf ⟨(32, 19725320980480), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00051.record036_result⟩)))))
 (.branch 43
 (.branch 40
 (.branch 38
 (.leaf ⟨(32, 19725442892032), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00051.record037_result⟩)
 (.branch 39
 (.leaf ⟨(32, 19727079505920), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00051.record038_result⟩)
 (.leaf ⟨(32, 19727120662784), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00051.record039_result⟩)))
 (.branch 41
 (.leaf ⟨(32, 19727343747072), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00051.record040_result⟩)
 (.branch 42
 (.leaf ⟨(32, 19727389065472), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00051.record041_result⟩)
 (.leaf ⟨(32, 19727401355264), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00051.record042_result⟩))))
 (.branch 46
 (.branch 44
 (.leaf ⟨(32, 19729607622656), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00051.record043_result⟩)
 (.branch 45
 (.leaf ⟨(32, 19729737581312), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00051.record044_result⟩)
 (.leaf ⟨(32, 19731281412352), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00051.record045_result⟩)))
 (.branch 48
 (.branch 47
 (.leaf ⟨(32, 19731634471168), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00051.record046_result⟩)
 (.leaf ⟨(32, 19731636617216), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00051.record047_result⟩))
 (.branch 49
 (.leaf ⟨(32, 19731642859520), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00051.record048_result⟩)
 (.leaf ⟨(32, 19731684016384), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00051.record049_result⟩)))))))
 (.branch 75
 (.branch 62
 (.branch 56
 (.branch 53
 (.branch 51
 (.leaf ⟨(32, 19731694225408), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00051.record050_result⟩)
 (.branch 52
 (.leaf ⟨(32, 19733898330880), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00051.record051_result⟩)
 (.leaf ⟨(32, 19739871314176), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00051.record052_result⟩)))
 (.branch 54
 (.leaf ⟨(32, 19739883603968), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00051.record053_result⟩)
 (.branch 55
 (.leaf ⟨(32, 19740005515520), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00051.record054_result⟩)
 (.leaf ⟨(32, 19740015724544), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00051.record055_result⟩))))
 (.branch 59
 (.branch 57
 (.leaf ⟨(32, 19740228599808), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00051.record056_result⟩)
 (.branch 58
 (.leaf ⟨(32, 19740279965696), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00051.record057_result⟩)
 (.leaf ⟨(32, 19740475269184), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00051.record058_result⟩)))
 (.branch 60
 (.leaf ⟨(32, 19742219830016), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00051.record059_result⟩)
 (.branch 61
 (.leaf ⟨(32, 19742622483008), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00051.record060_result⟩)
 (.leaf ⟨(32, 19829203484800), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00051.record061_result⟩)))))
 (.branch 68
 (.branch 65
 (.branch 63
 (.leaf ⟨(32, 19831149658240), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00051.record062_result⟩)
 (.branch 64
 (.leaf ⟨(32, 19831283859584), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00051.record063_result⟩)
 (.leaf ⟨(32, 19831349919872), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00051.record064_result⟩)))
 (.branch 66
 (.leaf ⟨(32, 19835444609152), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00051.record065_result⟩)
 (.branch 67
 (.leaf ⟨(32, 19844030349440), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00051.record066_result⟩)
 (.leaf ⟨(32, 19865508348032), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00051.record067_result⟩))))
 (.branch 71
 (.branch 69
 (.leaf ⟨(32, 19865642549376), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00051.record068_result⟩)
 (.branch 70
 (.leaf ⟨(32, 19865709650048), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00051.record069_result⟩)
 (.leaf ⟨(32, 19869803298944), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00051.record070_result⟩)))
 (.branch 73
 (.branch 72
 (.leaf ⟨(32, 19878386958464), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00051.record071_result⟩)
 (.leaf ⟨(32, 19878389039232), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00051.record072_result⟩))
 (.branch 74
 (.leaf ⟨(32, 19878390079616), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00051.record073_result⟩)
 (.leaf ⟨(32, 19895518544128), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00051.record074_result⟩))))))
 (.branch 87
 (.branch 81
 (.branch 78
 (.branch 76
 (.leaf ⟨(32, 19905434943744), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00051.record075_result⟩)
 (.branch 77
 (.leaf ⟨(32, 19905441186048), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00051.record076_result⟩)
 (.leaf ⟨(32, 19908452745472), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00051.record077_result⟩)))
 (.branch 79
 (.leaf ⟨(32, 19908861657088), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00051.record078_result⟩)
 (.branch 80
 (.leaf ⟨(32, 19917042647296), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00051.record079_result⟩)
 (.leaf ⟨(32, 19917051035648), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00051.record080_result⟩))))
 (.branch 84
 (.branch 82
 (.leaf ⟨(32, 19917174767872), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00051.record081_result⟩)
 (.branch 83
 (.leaf ⟨(32, 19917178994688), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00051.record082_result⟩)
 (.leaf ⟨(32, 19917183156224), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00051.record083_result⟩)))
 (.branch 85
 (.leaf ⟨(32, 19917249216512), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00051.record084_result⟩)
 (.branch 86
 (.leaf ⟨(32, 19917443203200), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00051.record085_result⟩)
 (.leaf ⟨(32, 19917643464832), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00051.record086_result⟩)))))
 (.branch 93
 (.branch 90
 (.branch 88
 (.leaf ⟨(32, 19921343905792), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00051.record087_result⟩)
 (.branch 89
 (.leaf ⟨(32, 19938725150752), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00051.record088_result⟩)
 (.leaf ⟨(32, 19947106418816), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00051.record089_result⟩)))
 (.branch 91
 (.leaf ⟨(32, 19974158565632), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00051.record090_result⟩)
 (.branch 92
 (.leaf ⟨(32, 19982744305920), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00051.record091_result⟩)
 (.leaf ⟨(32, 19985768415232), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00051.record092_result⟩))))
 (.branch 96
 (.branch 94
 (.leaf ⟨(32, 20000800801024), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00051.record093_result⟩)
 (.branch 95
 (.leaf ⟨(32, 20002947236096), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00051.record094_result⟩)
 (.leaf ⟨(32, 20004020453632), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00051.record095_result⟩)))
 (.branch 98
 (.branch 97
 (.leaf ⟨(32, 20017980669952), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00051.record096_result⟩)
 (.leaf ⟨(32, 20034036465920), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00051.record097_result⟩))
 (.branch 99
 (.leaf ⟨(32, 20034556528768), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00051.record098_result⟩)
 (.leaf ⟨(32, 20036182900992), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00051.record099_result⟩))))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (31850 + i))) 0 100 :=
  interval_of_check _ 0 100 (by decide +kernel)

public theorem complete : Block 31850 31950 :=
  block_of_table results 31850 100 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock1016
