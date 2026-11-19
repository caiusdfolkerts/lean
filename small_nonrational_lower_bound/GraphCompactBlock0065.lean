module
prelude
import GraphInputsRow19Part00025Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0065
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 50
 (.branch 25
 (.branch 12
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(19, 27055412543744), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00025.record000_result⟩)
 (.branch 2
 (.leaf ⟨(19, 27055420932096), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00025.record001_result⟩)
 (.leaf ⟨(19, 27068299542528), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00025.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(19, 27071486164992), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00025.record003_result⟩)
 (.branch 5
 (.leaf ⟨(19, 27087398256896), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00025.record004_result⟩)
 (.leaf ⟨(19, 27087656255744), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00025.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(19, 27087664644096), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00025.record006_result⟩)
 (.branch 8
 (.leaf ⟨(19, 27087860678912), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00025.record007_result⟩)
 (.leaf ⟨(19, 27087928885248), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00025.record008_result⟩)))
 (.branch 10
 (.leaf ⟨(19, 27088133308416), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00025.record009_result⟩)
 (.branch 11
 (.leaf ⟨(19, 27113463808256), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00025.record010_result⟩)
 (.leaf ⟨(19, 27115544183040), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00025.record011_result⟩)))))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf ⟨(19, 27121787568128), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00025.record012_result⟩)
 (.branch 14
 (.leaf ⟨(19, 27121921769472), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00025.record013_result⟩)
 (.leaf ⟨(19, 27122190172160), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00025.record014_result⟩)))
 (.branch 16
 (.leaf ⟨(19, 27123997802752), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00025.record015_result⟩)
 (.branch 17
 (.leaf ⟨(19, 27124006191104), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00025.record016_result⟩)
 (.leaf ⟨(19, 27124195983616), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00025.record017_result⟩))))
 (.branch 21
 (.branch 19
 (.leaf ⟨(19, 27124270432256), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00025.record018_result⟩)
 (.branch 20
 (.leaf ⟨(19, 27124402552832), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00025.record019_result⟩)
 (.leaf ⟨(19, 27124464386304), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00025.record020_result⟩)))
 (.branch 23
 (.branch 22
 (.leaf ⟨(19, 27124475895808), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00025.record021_result⟩)
 (.leaf ⟨(19, 27124732854272), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00025.record022_result⟩))
 (.branch 24
 (.leaf ⟨(19, 27124741177344), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00025.record023_result⟩)
 (.leaf ⟨(19, 27128496136448), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00025.record024_result⟩))))))
 (.branch 37
 (.branch 31
 (.branch 28
 (.branch 26
 (.leaf ⟨(19, 27128710038144), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00025.record025_result⟩)
 (.branch 27
 (.leaf ⟨(19, 27128710070784), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00025.record026_result⟩)
 (.leaf ⟨(19, 27128714231809), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00025.record027_result⟩)))
 (.branch 29
 (.leaf ⟨(19, 27130643677184), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00025.record028_result⟩)
 (.branch 30
 (.leaf ⟨(19, 27132724051968), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00025.record029_result⟩)
 (.leaf ⟨(19, 27135658967296), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00025.record030_result⟩))))
 (.branch 34
 (.branch 32
 (.leaf ⟨(19, 27135691997440), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00025.record031_result⟩)
 (.branch 33
 (.leaf ⟨(19, 27136748568832), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00025.record032_result⟩)
 (.leaf ⟨(19, 27140005363712), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00025.record033_result⟩)))
 (.branch 35
 (.leaf ⟨(19, 27140071424000), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00025.record034_result⟩)
 (.branch 36
 (.leaf ⟨(19, 27140301529344), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00025.record035_result⟩)
 (.leaf ⟨(19, 27147756437760), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00025.record036_result⟩)))))
 (.branch 43
 (.branch 40
 (.branch 38
 (.leaf ⟨(19, 27149902872832), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00025.record037_result⟩)
 (.branch 39
 (.leaf ⟨(19, 27154063622400), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00025.record038_result⟩)
 (.leaf ⟨(19, 27154203025664), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00025.record039_result⟩)))
 (.branch 41
 (.leaf ⟨(19, 27158488613120), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00025.record040_result⟩)
 (.branch 42
 (.leaf ⟨(19, 27158497001472), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00025.record041_result⟩)
 (.leaf ⟨(19, 27159025483776), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00025.record042_result⟩))))
 (.branch 46
 (.branch 44
 (.leaf ⟨(19, 27159033806848), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00025.record043_result⟩)
 (.branch 45
 (.leaf ⟨(19, 27159330619648), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00025.record044_result⟩)
 (.leaf ⟨(19, 27159339008000), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00025.record045_result⟩)))
 (.branch 48
 (.branch 47
 (.leaf ⟨(19, 27159528800512), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00025.record046_result⟩)
 (.leaf ⟨(19, 27159537188864), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00025.record047_result⟩))
 (.branch 49
 (.leaf ⟨(19, 27159801430016), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00025.record048_result⟩)
 (.leaf ⟨(19, 27167082741760), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00025.record049_result⟩)))))))
 (.branch 75
 (.branch 62
 (.branch 56
 (.branch 53
 (.branch 51
 (.leaf ⟨(19, 27168122929152), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00025.record050_result⟩)
 (.branch 52
 (.leaf ⟨(19, 27171243491328), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00025.record051_result⟩)
 (.leaf ⟨(19, 27171507732480), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00025.record052_result⟩)))
 (.branch 54
 (.leaf ⟨(19, 27171516055552), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00025.record053_result⟩)
 (.branch 55
 (.leaf ⟨(19, 27172217618432), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00025.record054_result⟩)
 (.leaf ⟨(19, 27172283678720), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00025.record055_result⟩))))
 (.branch 59
 (.branch 57
 (.leaf ⟨(19, 27172415799296), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00025.record056_result⟩)
 (.branch 58
 (.leaf ⟨(19, 27174364053504), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00025.record057_result⟩)
 (.leaf ⟨(19, 27174594158848), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00025.record058_result⟩)))
 (.branch 60
 (.leaf ⟨(19, 27180992102656), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00025.record059_result⟩)
 (.branch 61
 (.leaf ⟨(19, 27183138537728), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00025.record060_result⟩)
 (.leaf ⟨(19, 27183145820416), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00025.record061_result⟩)))))
 (.branch 68
 (.branch 65
 (.branch 63
 (.leaf ⟨(19, 27187431407872), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00025.record062_result⟩)
 (.branch 64
 (.leaf ⟨(19, 27187489016064), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00025.record063_result⟩)
 (.leaf ⟨(19, 27187702931712), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00025.record064_result⟩)))
 (.branch 66
 (.leaf ⟨(19, 27187753257216), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00025.record065_result⟩)
 (.branch 67
 (.leaf ⟨(19, 27193854066944), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00025.record066_result⟩)
 (.leaf ⟨(19, 27193862455296), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00025.record067_result⟩))))
 (.branch 71
 (.branch 69
 (.leaf ⟨(19, 27202448195584), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00025.record068_result⟩)
 (.branch 70
 (.leaf ⟨(19, 27206608945152), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00025.record069_result⟩)
 (.leaf ⟨(19, 27208689319936), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00025.record070_result⟩)))
 (.branch 73
 (.branch 72
 (.leaf ⟨(19, 27208886395136), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00025.record071_result⟩)
 (.leaf ⟨(19, 27216957685888), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00025.record072_result⟩))
 (.branch 74
 (.leaf ⟨(19, 27224238997632), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00025.record073_result⟩)
 (.leaf ⟨(19, 27225099403264), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00025.record074_result⟩))))))
 (.branch 87
 (.branch 81
 (.branch 78
 (.branch 76
 (.leaf ⟨(19, 27261573070848), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00025.record075_result⟩)
 (.branch 77
 (.leaf ⟨(19, 27291637784832), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00025.record076_result⟩)
 (.leaf ⟨(19, 27296971948032), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00025.record077_result⟩)))
 (.branch 79
 (.leaf ⟨(19, 27365491146752), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00025.record078_result⟩)
 (.branch 80
 (.leaf ⟨(19, 27365557207040), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00025.record079_result⟩)
 (.leaf ⟨(19, 27365689327616), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00025.record080_result⟩))))
 (.branch 84
 (.branch 82
 (.leaf ⟨(19, 27365787312384), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00025.record081_result⟩)
 (.branch 83
 (.leaf ⟨(19, 27387267909888), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00025.record082_result⟩)
 (.leaf ⟨(19, 27389348284672), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00025.record083_result⟩)))
 (.branch 85
 (.leaf ⟨(19, 27421560539392), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00025.record084_result⟩)
 (.branch 86
 (.leaf ⟨(19, 27423656648960), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00025.record085_result⟩)
 (.leaf ⟨(19, 27423706974464), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00025.record086_result⟩)))))
 (.branch 93
 (.branch 90
 (.branch 88
 (.leaf ⟨(19, 27536951148544), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00025.record087_result⟩)
 (.branch 89
 (.leaf ⟨(19, 27536957390848), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00025.record088_result⟩)
 (.leaf ⟨(19, 27569169645568), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00025.record089_result⟩)))
 (.branch 91
 (.leaf ⟨(19, 27596580520192), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00025.record090_result⟩)
 (.branch 92
 (.leaf ⟨(19, 27601365123072), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00025.record091_result⟩)
 (.leaf ⟨(19, 27605034139904), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00025.record092_result⟩))))
 (.branch 96
 (.branch 94
 (.leaf ⟨(19, 27605042528256), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00025.record093_result⟩)
 (.branch 95
 (.leaf ⟨(19, 27613760389120), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00025.record094_result⟩)
 (.leaf ⟨(19, 27617784905984), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00025.record095_result⟩)))
 (.branch 98
 (.branch 97
 (.leaf ⟨(19, 27617784971264), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00025.record096_result⟩)
 (.leaf ⟨(19, 27617786856704), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00025.record097_result⟩))
 (.branch 99
 (.leaf ⟨(19, 27617991328832), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00025.record098_result⟩)
 (.leaf ⟨(19, 27621107761152), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00025.record099_result⟩))))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (4539 + i))) 0 100 :=
  interval_of_check _ 0 100 (by decide +kernel)

public theorem complete : Block 4539 4639 :=
  block_of_table results 4539 100 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0065
