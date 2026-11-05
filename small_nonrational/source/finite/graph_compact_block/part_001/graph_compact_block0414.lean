module
prelude
import GraphInputsRow27Part00011Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0414
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 50
 (.branch 25
 (.branch 12
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(27, 25160473657344), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00011.record000_result⟩)
 (.branch 2
 (.leaf ⟨(27, 25177115598912), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00011.record001_result⟩)
 (.leaf ⟨(27, 25177149685760), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00011.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(27, 25177151766528), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00011.record003_result⟩)
 (.branch 5
 (.leaf ⟨(27, 25177184796672), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00011.record004_result⟩)
 (.leaf ⟨(27, 25178241368064), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00011.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(27, 25194420897792), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00011.record006_result⟩)
 (.branch 8
 (.leaf ⟨(27, 25215752995332), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00011.record007_result⟩)
 (.leaf ⟨(27, 25215753126912), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00011.record008_result⟩)))
 (.branch 10
 (.leaf ⟨(27, 25261126975488), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00011.record009_result⟩)
 (.branch 11
 (.leaf ⟨(27, 25261655457792), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00011.record010_result⟩)
 (.leaf ⟨(27, 25294313455616), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00011.record011_result⟩)))))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf ⟨(27, 25307594670080), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00011.record012_result⟩)
 (.branch 14
 (.leaf ⟨(27, 25307597774912), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00011.record013_result⟩)
 (.leaf ⟨(27, 25327732801792), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00011.record014_result⟩)))
 (.branch 16
 (.leaf ⟨(27, 25327732867072), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00011.record015_result⟩)
 (.branch 17
 (.leaf ⟨(27, 25327984754688), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00011.record016_result⟩)
 (.leaf ⟨(27, 25359794405376), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00011.record017_result⟩))))
 (.branch 21
 (.branch 19
 (.leaf ⟨(27, 25362076082176), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00011.record018_result⟩)
 (.branch 20
 (.leaf ⟨(27, 25362344484864), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00011.record019_result⟩)
 (.leaf ⟨(27, 25362398447632), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00011.record020_result⟩)))
 (.branch 23
 (.branch 22
 (.leaf ⟨(27, 25366639419456), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00011.record021_result⟩)
 (.leaf ⟨(27, 25366639435776), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00011.record022_result⟩))
 (.branch 24
 (.leaf ⟨(27, 25384901951488), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00011.record023_result⟩)
 (.leaf ⟨(27, 25431058157824), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00011.record024_result⟩))))))
 (.branch 37
 (.branch 31
 (.branch 28
 (.branch 26
 (.leaf ⟨(27, 25431064449088), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00011.record025_result⟩)
 (.branch 27
 (.leaf ⟨(27, 25445031493696), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00011.record026_result⟩)
 (.leaf ⟨(27, 25449326460928), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00011.record027_result⟩)))
 (.branch 29
 (.leaf ⟨(27, 25512676433984), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00011.record028_result⟩)
 (.branch 30
 (.leaf ⟨(27, 25566352773184), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00011.record029_result⟩)
 (.leaf ⟨(27, 25578175479808), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00011.record030_result⟩))))
 (.branch 34
 (.branch 32
 (.leaf ⟨(27, 25581032835088), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00011.record031_result⟩)
 (.branch 33
 (.leaf ⟨(27, 25590657728512), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00011.record032_result⟩)
 (.leaf ⟨(27, 25633724842240), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00011.record033_result⟩)))
 (.branch 35
 (.leaf ⟨(27, 25641525452864), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00011.record034_result⟩)
 (.branch 36
 (.leaf ⟨(27, 25658186022912), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00011.record035_result⟩)
 (.leaf ⟨(27, 25659277705216), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00011.record036_result⟩)))))
 (.branch 43
 (.branch 40
 (.branch 38
 (.leaf ⟨(27, 25702312247296), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00011.record037_result⟩)
 (.branch 39
 (.leaf ⟨(27, 25702318489600), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00011.record038_result⟩)
 (.leaf ⟨(27, 25705490417664), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00011.record039_result⟩)))
 (.branch 41
 (.leaf ⟨(27, 25705556477952), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00011.record040_result⟩)
 (.branch 42
 (.leaf ⟨(27, 25705933447232), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00011.record041_result⟩)
 (.leaf ⟨(27, 25705934503936), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00011.record042_result⟩))))
 (.branch 46
 (.branch 44
 (.leaf ⟨(27, 25735597457408), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00011.record043_result⟩)
 (.branch 45
 (.leaf ⟨(27, 25739873356032), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00011.record044_result⟩)
 (.leaf ⟨(27, 25739881744384), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00011.record045_result⟩)))
 (.branch 48
 (.branch 47
 (.leaf ⟨(27, 25769887940864), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00011.record046_result⟩)
 (.leaf ⟨(27, 25769890086912), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00011.record047_result⟩))
 (.branch 49
 (.leaf ⟨(27, 25769896329216), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00011.record048_result⟩)
 (.leaf ⟨(27, 25769898149888), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00011.record049_result⟩)))))))
 (.branch 75
 (.branch 62
 (.branch 56
 (.branch 53
 (.branch 51
 (.leaf ⟨(27, 25769964210176), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00011.record050_result⟩)
 (.branch 52
 (.leaf ⟨(27, 25770005367040), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00011.record051_result⟩)
 (.leaf ⟨(27, 25770357694528), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00011.record052_result⟩)))
 (.branch 54
 (.leaf ⟨(27, 25770360571904), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00011.record053_result⟩)
 (.branch 55
 (.leaf ⟨(27, 25770408020032), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00011.record054_result⟩)
 (.leaf ⟨(27, 25772085610752), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00011.record055_result⟩))))
 (.branch 59
 (.branch 57
 (.leaf ⟨(27, 25772093999104), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00011.record056_result⟩)
 (.branch 58
 (.leaf ⟨(27, 25772102255360), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00011.record057_result⟩)
 (.leaf ⟨(27, 25772488263744), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00011.record058_result⟩)))
 (.branch 60
 (.leaf ⟨(27, 25772504908352), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00011.record059_result⟩)
 (.branch 61
 (.leaf ⟨(27, 25772622348808), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00011.record060_result⟩)
 (.leaf ⟨(27, 25774174373888), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00011.record061_result⟩)))))
 (.branch 68
 (.branch 65
 (.branch 63
 (.leaf ⟨(27, 25774702723592), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00011.record062_result⟩)
 (.branch 64
 (.leaf ⟨(27, 25787052984320), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00011.record063_result⟩)
 (.leaf ⟨(27, 25787184972296), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00011.record064_result⟩)))
 (.branch 66
 (.leaf ⟨(27, 25839757000704), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00011.record065_result⟩)
 (.branch 67
 (.leaf ⟨(27, 25843112415232), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00011.record066_result⟩)
 (.leaf ⟨(27, 25843376656384), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00011.record067_result⟩))))
 (.branch 71
 (.branch 69
 (.leaf ⟨(27, 25843384455184), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00011.record068_result⟩)
 (.branch 70
 (.leaf ⟨(27, 25843401230352), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00011.record069_result⟩)
 (.leaf ⟨(27, 25844474970113), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00011.record070_result⟩)))
 (.branch 73
 (.branch 72
 (.leaf ⟨(27, 25925701926912), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00011.record071_result⟩)
 (.leaf ⟨(27, 25964427870208), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00011.record072_result⟩))
 (.branch 74
 (.leaf ⟨(27, 25964956352512), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00011.record073_result⟩)
 (.leaf ⟨(27, 25976524509248), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00011.record074_result⟩))))))
 (.branch 87
 (.branch 81
 (.branch 78
 (.branch 76
 (.leaf ⟨(27, 25993284814864), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00011.record075_result⟩)
 (.branch 77
 (.leaf ⟨(27, 26113695027264), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00011.record076_result⟩)
 (.leaf ⟨(27, 26130719574032), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00011.record077_result⟩)))
 (.branch 79
 (.leaf ⟨(27, 26188600901632), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00011.record078_result⟩)
 (.branch 80
 (.leaf ⟨(27, 26319584888832), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00011.record079_result⟩)
 (.leaf ⟨(27, 26320096593928), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00011.record080_result⟩))))
 (.branch 84
 (.branch 82
 (.leaf ⟨(27, 26320113238536), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00011.record081_result⟩)
 (.branch 83
 (.leaf ⟨(27, 26461583515936), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00011.record082_result⟩)
 (.leaf ⟨(27, 26512633921536), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00011.record083_result⟩)))
 (.branch 85
 (.leaf ⟨(27, 26512638083072), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00011.record084_result⟩)
 (.branch 86
 (.leaf ⟨(27, 26648747474944), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00011.record085_result⟩)
 (.leaf ⟨(27, 26648751636480), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00011.record086_result⟩)))))
 (.branch 93
 (.branch 90
 (.branch 88
 (.leaf ⟨(27, 26725604950016), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00011.record087_result⟩)
 (.branch 89
 (.leaf ⟨(27, 26794220732544), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00011.record088_result⟩)
 (.leaf ⟨(27, 27096514592768), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00011.record089_result⟩)))
 (.branch 91
 (.leaf ⟨(27, 27096518754304), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00011.record090_result⟩)
 (.branch 92
 (.leaf ⟨(27, 27122328403968), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00011.record091_result⟩)
 (.leaf ⟨(27, 27128710070272), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00011.record092_result⟩))))
 (.branch 96
 (.branch 94
 (.leaf ⟨(27, 27128714231808), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00011.record093_result⟩)
 (.branch 95
 (.leaf ⟨(27, 27130377437184), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00011.record094_result⟩)
 (.leaf ⟨(27, 27130771685504), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00011.record095_result⟩)))
 (.branch 98
 (.branch 97
 (.leaf ⟨(27, 27130777830400), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00011.record096_result⟩)
 (.leaf ⟨(27, 27137014824960), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00011.record097_result⟩))
 (.branch 99
 (.leaf ⟨(27, 27208961753088), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00011.record098_result⟩)
 (.leaf ⟨(27, 27216247275648), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00011.record099_result⟩))))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (18773 + i))) 0 100 :=
  interval_of_check _ 0 100 (by decide +kernel)

public theorem complete : Block 18773 18873 :=
  block_of_table results 18773 100 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0414
