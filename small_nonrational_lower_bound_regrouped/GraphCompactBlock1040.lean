module
prelude
import GraphInputsSix0Part00075Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock1040
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 50
 (.branch 25
 (.branch 12
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(32, 28827910670592), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00075.record000_result⟩)
 (.branch 2
 (.leaf ⟨(32, 28827913044096), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00075.record001_result⟩)
 (.leaf ⟨(32, 28827913076736), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00075.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(32, 28827914864768), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00075.record003_result⟩)
 (.branch 5
 (.leaf ⟨(32, 28828034402312), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00075.record004_result⟩)
 (.leaf ⟨(32, 28828377286784), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00075.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(32, 28830106519808), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00075.record006_result⟩)
 (.branch 8
 (.leaf ⟨(32, 28830106585088), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00075.record007_result⟩)
 (.leaf ⟨(32, 28830110713984), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00075.record008_result⟩)))
 (.branch 10
 (.leaf ⟨(32, 28830114776072), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00075.record009_result⟩)
 (.branch 11
 (.leaf ⟨(32, 28830131552257), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00075.record010_result⟩)
 (.leaf ⟨(32, 28830259544064), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00075.record011_result⟩)))))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf ⟨(32, 28830511137800), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00075.record012_result⟩)
 (.branch 14
 (.leaf ⟨(32, 28830527913985), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00075.record013_result⟩)
 (.leaf ⟨(32, 28836696703232), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00075.record014_result⟩)))
 (.branch 16
 (.leaf ⟨(32, 28836698849280), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00075.record015_result⟩)
 (.branch 17
 (.leaf ⟨(32, 28836746248448), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00075.record016_result⟩)
 (.leaf ⟨(32, 28838960562944), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00075.record017_result⟩))))
 (.branch 21
 (.branch 19
 (.leaf ⟨(32, 28841109159936), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00075.record018_result⟩)
 (.branch 20
 (.leaf ⟨(32, 28843263918080), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00075.record019_result⟩)
 (.leaf ⟨(32, 28845069699200), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00075.record020_result⟩)))
 (.branch 23
 (.branch 22
 (.leaf ⟨(32, 28864417939472), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00075.record021_result⟩)
 (.leaf ⟨(32, 28864483999760), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00075.record022_result⟩))
 (.branch 24
 (.leaf ⟨(32, 28865508425856), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00075.record023_result⟩)
 (.leaf ⟨(32, 28865508458496), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00075.record024_result⟩))))))
 (.branch 37
 (.branch 31
 (.branch 28
 (.branch 26
 (.leaf ⟨(32, 28865572405376), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00075.record025_result⟩)
 (.branch 27
 (.leaf ⟨(32, 28865574486144), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00075.record026_result⟩)
 (.leaf ⟨(32, 28865574518784), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00075.record027_result⟩)))
 (.branch 29
 (.leaf ⟨(32, 28869799215232), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00075.record028_result⟩)
 (.branch 30
 (.leaf ⟨(32, 28869803409408), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00075.record029_result⟩)
 (.leaf ⟨(32, 28869999476864), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00075.record030_result⟩))))
 (.branch 34
 (.branch 32
 (.leaf ⟨(32, 28874162339840), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00075.record031_result⟩)
 (.branch 33
 (.leaf ⟨(32, 28897703903360), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00075.record032_result⟩)
 (.leaf ⟨(32, 28897703936000), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00075.record033_result⟩)))
 (.branch 35
 (.leaf ⟨(32, 28897767882880), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00075.record034_result⟩)
 (.branch 36
 (.leaf ⟨(32, 28897769963648), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00075.record035_result⟩)
 (.leaf ⟨(32, 28897769996288), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00075.record036_result⟩)))))
 (.branch 43
 (.branch 40
 (.branch 38
 (.leaf ⟨(32, 28897821329536), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00075.record037_result⟩)
 (.branch 39
 (.leaf ⟨(32, 28900170137601), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00075.record038_result⟩)
 (.leaf ⟨(32, 28900941891712), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00075.record039_result⟩)))
 (.branch 41
 (.leaf ⟨(32, 28900987535488), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00075.record040_result⟩)
 (.branch 42
 (.leaf ⟨(32, 28900990689280), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00075.record041_result⟩)
 (.leaf ⟨(32, 28901007952000), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00075.record042_result⟩))))
 (.branch 46
 (.branch 44
 (.leaf ⟨(32, 28901121736832), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00075.record043_result⟩)
 (.branch 45
 (.leaf ⟨(32, 28901121769472), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00075.record044_result⟩)
 (.leaf ⟨(32, 28901122809856), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00075.record045_result⟩)))
 (.branch 48
 (.branch 47
 (.leaf ⟨(32, 28902250512385), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00075.record046_result⟩)
 (.leaf ⟨(32, 28905300822144), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00075.record047_result⟩))
 (.branch 49
 (.leaf ⟨(32, 28932062593152), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00075.record048_result⟩)
 (.leaf ⟨(32, 28933135810688), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00075.record049_result⟩)))))))
 (.branch 75
 (.branch 62
 (.branch 56
 (.branch 53
 (.branch 51
 (.leaf ⟨(32, 28933333991552), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00075.record050_result⟩)
 (.branch 52
 (.leaf ⟨(32, 28965345722496), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00075.record051_result⟩)
 (.leaf ⟨(32, 28965347803264), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00075.record052_result⟩)))
 (.branch 54
 (.leaf ⟨(32, 28965347835904), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00075.record053_result⟩)
 (.branch 55
 (.leaf ⟨(32, 28965349623936), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00075.record054_result⟩)
 (.leaf ⟨(32, 28965547804800), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00075.record055_result⟩))))
 (.branch 59
 (.branch 57
 (.leaf ⟨(32, 28965549137920), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00075.record056_result⟩)
 (.branch 58
 (.leaf ⟨(32, 28965601282056), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00075.record057_result⟩)
 (.leaf ⟨(32, 28967545473152), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00075.record058_result⟩)))
 (.branch 60
 (.leaf ⟨(32, 28967545505792), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00075.record059_result⟩)
 (.branch 61
 (.leaf ⟨(32, 28967562150400), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00075.record060_result⟩)
 (.leaf ⟨(32, 28967681655816), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00075.record061_result⟩)))))
 (.branch 68
 (.branch 65
 (.branch 63
 (.leaf ⟨(32, 28967698432001), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00075.record062_result⟩)
 (.branch 64
 (.leaf ⟨(32, 28973918718080), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00075.record063_result⟩)
 (.leaf ⟨(32, 28974120961032), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00075.record064_result⟩)))
 (.branch 66
 (.leaf ⟨(32, 28974137737217), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00075.record065_result⟩)
 (.branch 67
 (.leaf ⟨(32, 29000897398912), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00075.record066_result⟩)
 (.leaf ⟨(32, 29001937586304), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00075.record067_result⟩))))
 (.branch 71
 (.branch 69
 (.leaf ⟨(32, 29034133063808), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00075.record068_result⟩)
 (.branch 70
 (.leaf ⟨(32, 29036262852736), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00075.record069_result⟩)
 (.leaf ⟨(32, 29038343227520), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00075.record070_result⟩)))
 (.branch 73
 (.branch 72
 (.leaf ⟨(32, 29068423872640), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00075.record071_result⟩)
 (.leaf ⟨(32, 29138185453696), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00075.record072_result⟩))
 (.branch 74
 (.leaf ⟨(32, 29138187501824), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00075.record073_result⟩)
 (.leaf ⟨(32, 29138187534464), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00075.record074_result⟩))))))
 (.branch 87
 (.branch 81
 (.branch 78
 (.branch 76
 (.leaf ⟨(32, 29138218483840), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00075.record075_result⟩)
 (.branch 77
 (.leaf ⟨(32, 29138220531968), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00075.record076_result⟩)
 (.leaf ⟨(32, 29138220564608), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00075.record077_result⟩)))
 (.branch 79
 (.leaf ⟨(32, 29138222153744), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00075.record078_result⟩)
 (.branch 80
 (.leaf ⟨(32, 29138224726144), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00075.record079_result⟩)
 (.leaf ⟨(32, 29138420334608), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00075.record080_result⟩))))
 (.branch 84
 (.branch 82
 (.leaf ⟨(32, 29138421833984), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00075.record081_result⟩)
 (.branch 83
 (.leaf ⟨(32, 29138422415376), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00075.record082_result⟩)
 (.leaf ⟨(32, 29138426028160), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00075.record083_result⟩)))
 (.branch 85
 (.leaf ⟨(32, 29138690818064), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00075.record084_result⟩)
 (.branch 86
 (.leaf ⟨(32, 29139361370368), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00075.record085_result⟩)
 (.leaf ⟨(32, 29139361403008), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00075.record086_result⟩)))))
 (.branch 93
 (.branch 90
 (.branch 88
 (.leaf ⟨(32, 29139361431568), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00075.record087_result⟩)
 (.branch 89
 (.leaf ⟨(32, 29139378178176), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00075.record088_result⟩)
 (.leaf ⟨(32, 29139493490944), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00075.record089_result⟩)))
 (.branch 91
 (.leaf ⟨(32, 29139493523584), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00075.record090_result⟩)
 (.branch 92
 (.leaf ⟨(32, 29139493552144), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00075.record091_result⟩)
 (.leaf ⟨(32, 29139495632912), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00075.record092_result⟩))))
 (.branch 96
 (.branch 94
 (.leaf ⟨(32, 29139499794448), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00075.record093_result⟩)
 (.branch 95
 (.leaf ⟨(32, 29139516309520), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00075.record094_result⟩)
 (.leaf ⟨(32, 29145751423104), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00075.record095_result⟩)))
 (.branch 98
 (.branch 97
 (.leaf ⟨(32, 29145757433872), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00075.record096_result⟩)
 (.leaf ⟨(32, 29145934876928), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00075.record097_result⟩))
 (.branch 99
 (.leaf ⟨(32, 29145934938128), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00075.record098_result⟩)
 (.leaf ⟨(32, 29145942220816), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00075.record099_result⟩))))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (34113 + i))) 0 100 :=
  interval_of_check _ 0 100 (by decide +kernel)

public theorem complete : Block 34113 34213 :=
  block_of_table results 34113 100 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock1040
