module
prelude
import GraphInputsRow19Part00029Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0069
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 50
 (.branch 25
 (.branch 12
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(19, 31008096264192), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00029.record000_result⟩)
 (.branch 2
 (.leaf ⟨(19, 31008120905984), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00029.record001_result⟩)
 (.leaf ⟨(19, 31016212299776), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00029.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(19, 31016442405120), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00029.record003_result⟩)
 (.branch 5
 (.leaf ⟨(19, 31016979275776), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00029.record004_result⟩)
 (.leaf ⟨(19, 31016980316160), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00029.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(19, 31029151695104), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00029.record006_result⟩)
 (.branch 8
 (.leaf ⟨(19, 31029151760384), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00029.record007_result⟩)
 (.leaf ⟨(19, 31029554364416), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00029.record008_result⟩)))
 (.branch 10
 (.leaf ⟨(19, 31031433371904), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00029.record009_result⟩)
 (.branch 11
 (.leaf ⟨(19, 31031433437184), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00029.record010_result⟩)
 (.leaf ⟨(19, 31031483697408), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00029.record011_result⟩)))))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf ⟨(19, 31031697678336), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00029.record012_result⟩)
 (.branch 14
 (.leaf ⟨(19, 31031755278368), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00029.record013_result⟩)
 (.leaf ⟨(19, 31033902759937), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00029.record014_result⟩)))
 (.branch 16
 (.leaf ⟨(19, 31042422440960), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00029.record015_result⟩)
 (.branch 17
 (.leaf ⟨(19, 31042480112384), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00029.record016_result⟩)
 (.leaf ⟨(19, 31044633888800), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00029.record017_result⟩))))
 (.branch 21
 (.branch 19
 (.leaf ⟨(19, 31046781370369), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00029.record018_result⟩)
 (.branch 20
 (.leaf ⟨(19, 31050533339392), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00029.record019_result⟩)
 (.leaf ⟨(19, 31050537566208), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00029.record020_result⟩)))
 (.branch 23
 (.branch 22
 (.leaf ⟨(19, 31050545759232), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00029.record021_result⟩)
 (.leaf ⟨(19, 31050734641408), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00029.record022_result⟩))
 (.branch 24
 (.leaf ⟨(19, 31050743029760), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00029.record023_result⟩)
 (.leaf ⟨(19, 31050743940096), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00029.record024_result⟩))))))
 (.branch 37
 (.branch 31
 (.branch 28
 (.branch 26
 (.leaf ⟨(19, 31050801611520), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00029.record025_result⟩)
 (.branch 27
 (.leaf ⟨(19, 31051271373344), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00029.record026_result⟩)
 (.leaf ⟨(19, 31051338482176), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00029.record027_result⟩)))
 (.branch 29
 (.leaf ⟨(19, 31056985064448), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00029.record028_result⟩)
 (.branch 30
 (.leaf ⟨(19, 31073393197056), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00029.record029_result⟩)
 (.leaf ⟨(19, 31109728501760), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00029.record030_result⟩))))
 (.branch 34
 (.branch 32
 (.leaf ⟨(19, 31109992742912), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00029.record031_result⟩)
 (.branch 33
 (.leaf ⟨(19, 31110001065984), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00029.record032_result⟩)
 (.leaf ⟨(19, 31110702628864), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00029.record033_result⟩)))
 (.branch 35
 (.leaf ⟨(19, 31110768689152), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00029.record034_result⟩)
 (.branch 36
 (.leaf ⟨(19, 31168868131072), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00029.record035_result⟩)
 (.leaf ⟨(19, 31168918456576), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00029.record036_result⟩)))))
 (.branch 43
 (.branch 40
 (.branch 38
 (.leaf ⟨(19, 31173079206144), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00029.record037_result⟩)
 (.branch 39
 (.leaf ⟨(19, 31210002202624), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00029.record038_result⟩)
 (.leaf ⟨(19, 31341761626144), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00029.record039_result⟩)))
 (.branch 41
 (.leaf ⟨(19, 31346050277632), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00029.record040_result⟩)
 (.branch 42
 (.leaf ⟨(19, 31346056577056), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00029.record041_result⟩)
 (.leaf ⟨(19, 31372744425728), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00029.record042_result⟩))))
 (.branch 46
 (.branch 44
 (.leaf ⟨(19, 31372878627072), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00029.record043_result⟩)
 (.branch 45
 (.leaf ⟨(19, 31372882788608), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00029.record044_result⟩)
 (.leaf ⟨(19, 31375026102528), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00029.record045_result⟩)))
 (.branch 48
 (.branch 47
 (.leaf ⟨(19, 31375030264064), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00029.record046_result⟩)
 (.leaf ⟨(19, 31375030321184), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00029.record047_result⟩))
 (.branch 49
 (.leaf ⟨(19, 31384971280640), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00029.record048_result⟩)
 (.leaf ⟨(19, 31384982790144), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00029.record049_result⟩)))))))
 (.branch 75
 (.branch 62
 (.branch 56
 (.branch 53
 (.branch 51
 (.leaf ⟨(19, 31385239748608), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00029.record050_result⟩)
 (.branch 52
 (.leaf ⟨(19, 31385248071680), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00029.record051_result⟩)
 (.leaf ⟨(19, 31397453529344), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00029.record052_result⟩)))
 (.branch 54
 (.leaf ⟨(19, 31397465038848), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00029.record053_result⟩)
 (.branch 55
 (.leaf ⟨(19, 31400816812032), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00029.record054_result⟩)
 (.leaf ⟨(19, 31407243100176), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00029.record055_result⟩))))
 (.branch 59
 (.branch 57
 (.leaf ⟨(19, 31408329392384), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00029.record056_result⟩)
 (.branch 58
 (.leaf ⟨(19, 31408333553920), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00029.record057_result⟩)
 (.leaf ⟨(19, 31408333619200), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00029.record058_result⟩)))
 (.branch 60
 (.leaf ⟨(19, 31408336675072), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00029.record059_result⟩)
 (.branch 61
 (.leaf ⟨(19, 31408839987232), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00029.record060_result⟩)
 (.leaf ⟨(19, 31413949243424), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00029.record061_result⟩)))))
 (.branch 68
 (.branch 65
 (.branch 63
 (.leaf ⟨(19, 31413949767696), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00029.record062_result⟩)
 (.branch 64
 (.leaf ⟨(19, 31414775980288), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00029.record063_result⟩)
 (.leaf ⟨(19, 31415040221440), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00029.record064_result⟩)))
 (.branch 66
 (.leaf ⟨(19, 31415040286720), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00029.record065_result⟩)
 (.branch 67
 (.leaf ⟨(19, 31415047561248), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00029.record066_result⟩)
 (.leaf ⟨(19, 31415081111584), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00029.record067_result⟩))))
 (.branch 71
 (.branch 69
 (.leaf ⟨(19, 31416716951808), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00029.record068_result⟩)
 (.branch 70
 (.leaf ⟨(19, 31416725340160), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00029.record069_result⟩)
 (.leaf ⟨(19, 31416915132672), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00029.record070_result⟩)))
 (.branch 73
 (.branch 72
 (.leaf ⟨(19, 31416923521024), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00029.record071_result⟩)
 (.leaf ⟨(19, 31417183535360), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00029.record072_result⟩))
 (.branch 74
 (.leaf ⟨(19, 31417195044864), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00029.record073_result⟩)
 (.leaf ⟨(19, 31417253822464), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00029.record074_result⟩))))))
 (.branch 87
 (.branch 81
 (.branch 78
 (.branch 76
 (.leaf ⟨(19, 31417262145536), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00029.record075_result⟩)
 (.branch 77
 (.leaf ⟨(19, 31417417867520), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00029.record076_result⟩)
 (.leaf ⟨(19, 31417452003328), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00029.record077_result⟩)))
 (.branch 79
 (.leaf ⟨(19, 31417460326400), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00029.record078_result⟩)
 (.branch 80
 (.leaf ⟨(19, 31425509261312), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00029.record079_result⟩)
 (.leaf ⟨(19, 31431746158848), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00029.record080_result⟩))))
 (.branch 84
 (.branch 82
 (.leaf ⟨(19, 31431750385664), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00029.record081_result⟩)
 (.branch 83
 (.leaf ⟨(19, 31431757668352), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00029.record082_result⟩)
 (.leaf ⟨(19, 31431947460864), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00029.record083_result⟩)))
 (.branch 85
 (.leaf ⟨(19, 31431955849216), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00029.record084_result⟩)
 (.branch 86
 (.leaf ⟨(19, 31431980491008), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00029.record085_result⟩)
 (.leaf ⟨(19, 31432450252832), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00029.record086_result⟩)))))
 (.branch 93
 (.branch 90
 (.branch 88
 (.leaf ⟨(19, 31432484331520), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00029.record087_result⟩)
 (.branch 89
 (.leaf ⟨(19, 31432517361664), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00029.record088_result⟩)
 (.leaf ⟨(19, 31432518402048), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00029.record089_result⟩)))
 (.branch 91
 (.leaf ⟨(19, 31433029066752), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00029.record090_result⟩)
 (.branch 92
 (.leaf ⟨(19, 31440524869888), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00029.record091_result⟩)
 (.leaf ⟨(19, 31440529031424), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00029.record092_result⟩))))
 (.branch 96
 (.branch 94
 (.leaf ⟨(19, 31440529096704), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00029.record093_result⟩)
 (.branch 95
 (.leaf ⟨(19, 31440532152576), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00029.record094_result⟩)
 (.leaf ⟨(19, 31448044675328), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00029.record095_result⟩)))
 (.branch 98
 (.branch 97
 (.leaf ⟨(19, 31448044740608), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00029.record096_result⟩)
 (.leaf ⟨(19, 31448061970688), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00029.record097_result⟩))
 (.branch 99
 (.leaf ⟨(19, 31448308916480), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00029.record098_result⟩)
 (.leaf ⟨(19, 31448308981760), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00029.record099_result⟩))))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (4915 + i))) 0 100 :=
  interval_of_check _ 0 100 (by decide +kernel)

public theorem complete : Block 4915 5015 :=
  block_of_table results 4915 100 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0069
