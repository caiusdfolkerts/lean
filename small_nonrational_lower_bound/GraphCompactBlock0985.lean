module
prelude
import GraphInputsSix0Part00020Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0985
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 50
 (.branch 25
 (.branch 12
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(32, 7560776196096), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00020.record000_result⟩)
 (.branch 2
 (.leaf ⟨(32, 7560779284608), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00020.record001_result⟩)
 (.leaf ⟨(32, 7560830650496), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00020.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(32, 7562770579712), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00020.record003_result⟩)
 (.branch 5
 (.leaf ⟨(32, 7562778968064), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00020.record004_result⟩)
 (.leaf ⟨(32, 7563047337985), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00020.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(32, 7563171102976), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00020.record006_result⟩)
 (.branch 8
 (.leaf ⟨(32, 7563181572096), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00020.record007_result⟩)
 (.leaf ⟨(32, 7563550656768), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00020.record008_result⟩)))
 (.branch 10
 (.leaf ⟨(32, 7563724259584), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00020.record009_result⟩)
 (.branch 11
 (.leaf ⟨(32, 7563731607552), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00020.record010_result⟩)
 (.leaf ⟨(32, 7563748837632), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00020.record011_result⟩)))))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf ⟨(32, 7563992662272), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00020.record012_result⟩)
 (.branch 14
 (.leaf ⟨(32, 7563992727552), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00020.record013_result⟩)
 (.leaf ⟨(32, 7563995848704), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00020.record014_result⟩)))
 (.branch 16
 (.leaf ⟨(32, 7564017272960), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00020.record015_result⟩)
 (.branch 17
 (.leaf ⟨(32, 7565127712769), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00020.record016_result⟩)
 (.leaf ⟨(32, 7565891141888), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00020.record017_result⟩))))
 (.branch 21
 (.branch 19
 (.leaf ⟨(32, 7565899530240), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00020.record018_result⟩)
 (.branch 20
 (.leaf ⟨(32, 7569143824640), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00020.record019_result⟩)
 (.leaf ⟨(32, 7569152212992), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00020.record020_result⟩)))
 (.branch 23
 (.branch 22
 (.leaf ⟨(32, 7569218273280), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00020.record021_result⟩)
 (.leaf ⟨(32, 7569412227328), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00020.record022_result⟩))
 (.branch 24
 (.leaf ⟨(32, 7569422696448), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00020.record023_result⟩)
 (.leaf ⟨(32, 7569612488960), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00020.record024_result⟩))))))
 (.branch 37
 (.branch 31
 (.branch 28
 (.branch 26
 (.leaf ⟨(32, 7572607205377), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00020.record025_result⟩)
 (.branch 27
 (.leaf ⟨(32, 7576429267200), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00020.record026_result⟩)
 (.leaf ⟨(32, 7576433461376), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00020.record027_result⟩)))
 (.branch 29
 (.leaf ⟨(32, 7576495327488), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00020.record028_result⟩)
 (.branch 30
 (.leaf ⟨(32, 7576499521664), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00020.record029_result⟩)
 (.leaf ⟨(32, 7576877547648), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00020.record030_result⟩))))
 (.branch 34
 (.branch 32
 (.leaf ⟨(32, 7576877580288), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00020.record031_result⟩)
 (.branch 33
 (.leaf ⟨(32, 7576878620672), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00020.record032_result⟩)
 (.leaf ⟨(32, 7577733726464), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00020.record033_result⟩)))
 (.branch 35
 (.leaf ⟨(32, 7577737953280), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00020.record034_result⟩)
 (.branch 36
 (.leaf ⟨(32, 7577744195584), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00020.record035_result⟩)
 (.leaf ⟨(32, 7585718083648), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00020.record036_result⟩)))))
 (.branch 43
 (.branch 40
 (.branch 38
 (.leaf ⟨(32, 7586055225600), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00020.record037_result⟩)
 (.branch 39
 (.leaf ⟨(32, 7586191572992), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00020.record038_result⟩)
 (.leaf ⟨(32, 7586199896064), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00020.record039_result⟩)))
 (.branch 41
 (.leaf ⟨(32, 7586323693568), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00020.record040_result⟩)
 (.branch 42
 (.leaf ⟨(32, 7586332016640), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00020.record041_result⟩)
 (.leaf ⟨(32, 7586792357888), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00020.record042_result⟩))))
 (.branch 46
 (.branch 44
 (.leaf ⟨(32, 7586860498944), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00020.record043_result⟩)
 (.branch 45
 (.leaf ⟨(32, 7593519399168), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00020.record044_result⟩)
 (.leaf ⟨(32, 7593521219840), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00020.record045_result⟩)))
 (.branch 48
 (.branch 47
 (.leaf ⟨(32, 7593521283080), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00020.record046_result⟩)
 (.leaf ⟨(32, 7593640790024), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00020.record047_result⟩))
 (.branch 49
 (.leaf ⟨(32, 7593644951560), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00020.record048_result⟩)
 (.leaf ⟨(32, 7593657696512), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00020.record049_result⟩)))))))
 (.branch 75
 (.branch 62
 (.branch 56
 (.branch 53
 (.branch 51
 (.leaf ⟨(32, 7593661858048), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00020.record050_result⟩)
 (.branch 52
 (.leaf ⟨(32, 7593661923328), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00020.record051_result⟩)
 (.leaf ⟨(32, 7593665759488), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00020.record052_result⟩)))
 (.branch 54
 (.leaf ⟨(32, 7594062121216), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00020.record053_result⟩)
 (.branch 55
 (.leaf ⟨(32, 7594064494720), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00020.record054_result⟩)
 (.leaf ⟨(32, 7594064527360), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00020.record055_result⟩))))
 (.branch 59
 (.branch 57
 (.leaf ⟨(32, 7594066315392), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00020.record056_result⟩)
 (.branch 58
 (.leaf ⟨(32, 7594185852936), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00020.record057_result⟩)
 (.leaf ⟨(32, 7597801538568), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00020.record058_result⟩)))
 (.branch 60
 (.leaf ⟨(32, 7598074104064), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00020.record059_result⟩)
 (.branch 61
 (.leaf ⟨(32, 7598074169344), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00020.record060_result⟩)
 (.leaf ⟨(32, 7598086619392), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00020.record061_result⟩)))))
 (.branch 68
 (.branch 65
 (.branch 63
 (.leaf ⟨(32, 7598090813952), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00020.record062_result⟩)
 (.branch 64
 (.leaf ⟨(32, 7598095007744), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00020.record063_result⟩)
 (.leaf ⟨(32, 7598342539392), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00020.record064_result⟩)))
 (.branch 66
 (.leaf ⟨(32, 7598346601480), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00020.record065_result⟩)
 (.branch 67
 (.leaf ⟨(32, 7598363377665), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00020.record066_result⟩)
 (.leaf ⟨(32, 7598602748160), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00020.record067_result⟩))))
 (.branch 71
 (.branch 69
 (.leaf ⟨(32, 7598615037952), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00020.record068_result⟩)
 (.branch 70
 (.leaf ⟨(32, 7602379489536), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00020.record069_result⟩)
 (.leaf ⟨(32, 7602387877888), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00020.record070_result⟩)))
 (.branch 73
 (.branch 72
 (.leaf ⟨(32, 7602495095040), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00020.record071_result⟩)
 (.leaf ⟨(32, 7602647892224), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00020.record072_result⟩))
 (.branch 74
 (.leaf ⟨(32, 7602652119040), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00020.record073_result⟩)
 (.leaf ⟨(32, 7602658361344), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00020.record074_result⟩))))))
 (.branch 87
 (.branch 81
 (.branch 78
 (.branch 76
 (.leaf ⟨(32, 7602763497728), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00020.record075_result⟩)
 (.branch 77
 (.leaf ⟨(32, 7602775787520), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00020.record076_result⟩)
 (.leaf ⟨(32, 7602897699072), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00020.record077_result⟩)))
 (.branch 79
 (.leaf ⟨(32, 7606525559040), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00020.record078_result⟩)
 (.branch 80
 (.leaf ⟨(32, 7606798188544), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00020.record079_result⟩)
 (.leaf ⟨(32, 7607062429696), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00020.record080_result⟩))))
 (.branch 84
 (.branch 82
 (.leaf ⟨(32, 7607070752768), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00020.record081_result⟩)
 (.branch 83
 (.leaf ⟨(32, 7607192388352), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00020.record082_result⟩)
 (.leaf ⟨(32, 7610820593920), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00020.record083_result⟩)))
 (.branch 85
 (.leaf ⟨(32, 7610824788096), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00020.record084_result⟩)
 (.branch 86
 (.leaf ⟨(32, 7611225211912), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00020.record085_result⟩)
 (.leaf ⟨(32, 7611241988097), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00020.record086_result⟩)))))
 (.branch 93
 (.branch 90
 (.branch 88
 (.leaf ⟨(32, 7620077290048), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00020.record087_result⟩)
 (.branch 89
 (.leaf ⟨(32, 7623567081988), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00020.record088_result⟩)
 (.leaf ⟨(32, 7623567082752), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00020.record089_result⟩)))
 (.branch 91
 (.leaf ⟨(32, 7623567083008), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00020.record090_result⟩)
 (.branch 92
 (.leaf ⟨(32, 7623567114496), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00020.record091_result⟩)
 (.leaf ⟨(32, 7623575471104), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00020.record092_result⟩))))
 (.branch 96
 (.branch 94
 (.leaf ⟨(32, 7623705427968), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00020.record093_result⟩)
 (.branch 95
 (.leaf ⟨(32, 7623835582464), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00020.record094_result⟩)
 (.leaf ⟨(32, 7623843905536), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00020.record095_result⟩)))
 (.branch 98
 (.branch 97
 (.leaf ⟨(32, 7623977992192), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00020.record096_result⟩)
 (.leaf ⟨(32, 7624103821828), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00020.record097_result⟩))
 (.branch 99
 (.leaf ⟨(32, 7624372257280), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00020.record098_result⟩)
 (.leaf ⟨(32, 7624506474496), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00020.record099_result⟩))))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (28786 + i))) 0 100 :=
  interval_of_check _ 0 100 (by decide +kernel)

public theorem complete : Block 28786 28886 :=
  block_of_table results 28786 100 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0985
