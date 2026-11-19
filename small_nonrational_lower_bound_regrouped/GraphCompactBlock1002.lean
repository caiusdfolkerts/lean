module
prelude
import GraphInputsSix0Part00037Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock1002
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 50
 (.branch 25
 (.branch 12
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(32, 14709795356928), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00037.record000_result⟩)
 (.branch 2
 (.leaf ⟨(32, 14709805826048), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00037.record001_result⟩)
 (.leaf ⟨(32, 14716245131264), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00037.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(32, 14724566630400), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00037.record003_result⟩)
 (.branch 5
 (.leaf ⟨(32, 14733988134912), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00037.record004_result⟩)
 (.leaf ⟨(32, 14742762619136), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00037.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(32, 14743031021824), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00037.record006_result⟩)
 (.branch 8
 (.leaf ⟨(32, 14743041490944), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00037.record007_result⟩)
 (.leaf ⟨(32, 14743280828672), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00037.record008_result⟩)))
 (.branch 10
 (.leaf ⟨(32, 14747445559296), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00037.record009_result⟩)
 (.branch 11
 (.leaf ⟨(32, 14749480796160), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00037.record010_result⟩)
 (.leaf ⟨(32, 14749521953024), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00037.record011_result⟩)))))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf ⟨(32, 14757843452160), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00037.record012_result⟩)
 (.branch 14
 (.leaf ⟨(32, 14758066536448), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00037.record013_result⟩)
 (.leaf ⟨(32, 14760460419648), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00037.record014_result⟩)))
 (.branch 16
 (.leaf ⟨(32, 14768245195008), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00037.record015_result⟩)
 (.branch 17
 (.leaf ⟨(32, 14768379461632), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00037.record016_result⟩)
 (.leaf ⟨(32, 14768387784704), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00037.record017_result⟩))))
 (.branch 21
 (.branch 19
 (.leaf ⟨(32, 14768782065664), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00037.record018_result⟩)
 (.branch 20
 (.leaf ⟨(32, 14768916136448), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00037.record019_result⟩)
 (.leaf ⟨(32, 14781201318144), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00037.record020_result⟩)))
 (.branch 23
 (.branch 22
 (.leaf ⟨(32, 14781473947648), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00037.record021_result⟩)
 (.leaf ⟨(32, 14781738188800), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00037.record022_result⟩))
 (.branch 24
 (.leaf ⟨(32, 14781746511872), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00037.record023_result⟩)
 (.leaf ⟨(32, 14781936369664), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00037.record024_result⟩))))))
 (.branch 37
 (.branch 31
 (.branch 28
 (.branch 26
 (.leaf ⟨(32, 14786039382016), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00037.record025_result⟩)
 (.branch 27
 (.leaf ⟨(32, 14786097119232), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00037.record026_result⟩)
 (.leaf ⟨(32, 14787640623360), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00037.record027_result⟩)))
 (.branch 29
 (.leaf ⟨(32, 14794084090112), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00037.record028_result⟩)
 (.branch 30
 (.leaf ⟨(32, 14794418618368), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00037.record029_result⟩)
 (.leaf ⟨(32, 14794625122304), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00037.record030_result⟩))))
 (.branch 34
 (.branch 32
 (.leaf ⟨(32, 14796230525184), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00037.record031_result⟩)
 (.branch 33
 (.leaf ⟨(32, 14796968697856), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00037.record032_result⟩)
 (.leaf ⟨(32, 14804820492288), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00037.record033_result⟩)))
 (.branch 35
 (.leaf ⟨(32, 14805357297664), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00037.record034_result⟩)
 (.branch 36
 (.leaf ⟨(32, 14883944988928), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00037.record035_result⟩)
 (.leaf ⟨(32, 14883953377280), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00037.record036_result⟩)))))
 (.branch 43
 (.branch 40
 (.branch 38
 (.leaf ⟨(32, 14887841497344), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00037.record037_result⟩)
 (.branch 39
 (.leaf ⟨(32, 14888105738496), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00037.record038_result⟩)
 (.leaf ⟨(32, 14888114126848), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00037.record039_result⟩)))
 (.branch 41
 (.leaf ⟨(32, 14891457511680), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00037.record040_result⟩)
 (.branch 42
 (.leaf ⟨(32, 14896427237632), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00037.record041_result⟩)
 (.leaf ⟨(32, 14896435625984), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00037.record042_result⟩))))
 (.branch 46
 (.branch 44
 (.leaf ⟨(32, 14896827760896), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00037.record043_result⟩)
 (.branch 45
 (.leaf ⟨(32, 14900047413504), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00037.record044_result⟩)
 (.leaf ⟨(32, 14900059443200), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00037.record045_result⟩)))
 (.branch 48
 (.branch 47
 (.leaf ⟨(32, 14922134126848), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00037.record046_result⟩)
 (.leaf ⟨(32, 14922398368000), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00037.record047_result⟩))
 (.branch 49
 (.leaf ⟨(32, 14922406756352), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00037.record048_result⟩)
 (.leaf ⟨(32, 14922596548864), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00037.record049_result⟩)))))))
 (.branch 75
 (.branch 62
 (.branch 56
 (.branch 53
 (.branch 51
 (.leaf ⟨(32, 14923669766400), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00037.record050_result⟩)
 (.branch 52
 (.leaf ⟨(32, 14930719867136), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00037.record051_result⟩)
 (.leaf ⟨(32, 14930728255488), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00037.record052_result⟩)))
 (.branch 54
 (.leaf ⟨(32, 14931186450688), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00037.record053_result⟩)
 (.branch 55
 (.leaf ⟨(32, 14931197960192), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00037.record054_result⟩)
 (.leaf ⟨(32, 14932259668224), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00037.record055_result⟩))))
 (.branch 59
 (.branch 57
 (.leaf ⟨(32, 14932271697920), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00037.record056_result⟩)
 (.branch 58
 (.leaf ⟨(32, 14938702094592), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00037.record057_result⟩)
 (.leaf ⟨(32, 14973061300992), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00037.record058_result⟩)))
 (.branch 60
 (.leaf ⟨(32, 14988094275840), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00037.record059_result⟩)
 (.branch 61
 (.leaf ⟨(32, 14990719385856), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00037.record060_result⟩)
 (.leaf ⟨(32, 14991124135936), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00037.record061_result⟩)))))
 (.branch 68
 (.branch 65
 (.branch 63
 (.leaf ⟨(32, 14991181807872), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00037.record062_result⟩)
 (.branch 64
 (.leaf ⟨(32, 14992255025408), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00037.record063_result⟩)
 (.leaf ⟨(32, 14999305126144), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00037.record064_result⟩)))
 (.branch 66
 (.leaf ⟨(32, 14999313514496), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00037.record065_result⟩)
 (.branch 67
 (.leaf ⟨(32, 14999445635072), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00037.record066_result⟩)
 (.leaf ⟨(32, 14999503307008), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00037.record067_result⟩))))
 (.branch 71
 (.branch 69
 (.leaf ⟨(32, 14999705649408), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00037.record068_result⟩)
 (.branch 70
 (.leaf ⟨(32, 14999709876224), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00037.record069_result⟩)
 (.leaf ⟨(32, 14999771709696), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00037.record070_result⟩)))
 (.branch 73
 (.branch 72
 (.leaf ⟨(32, 14999783219200), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00037.record071_result⟩)
 (.leaf ⟨(32, 15000576524544), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00037.record072_result⟩))
 (.branch 74
 (.leaf ⟨(32, 15000844927232), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00037.record073_result⟩)
 (.leaf ⟨(32, 15000856956928), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00037.record074_result⟩))))))
 (.branch 87
 (.branch 81
 (.branch 78
 (.branch 76
 (.leaf ⟨(32, 15003126604032), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00037.record075_result⟩)
 (.branch 77
 (.leaf ⟨(32, 15034671497472), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00037.record076_result⟩)
 (.leaf ⟨(32, 15037485810432), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00037.record077_result⟩)))
 (.branch 79
 (.leaf ⟨(32, 15053063520512), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00037.record078_result⟩)
 (.branch 80
 (.leaf ⟨(32, 15053600391168), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00037.record079_result⟩)
 (.leaf ⟨(32, 15059304644864), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00037.record080_result⟩))))
 (.branch 84
 (.branch 82
 (.leaf ⟨(32, 15059841515520), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00037.record081_result⟩)
 (.branch 83
 (.leaf ⟨(32, 15067890385152), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00037.record082_result⟩)
 (.leaf ⟨(32, 15068427255808), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00037.record083_result⟩)))
 (.branch 85
 (.leaf ⟨(32, 15068435578880), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00037.record084_result⟩)
 (.branch 86
 (.leaf ⟨(32, 15068625436672), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00037.record085_result⟩)
 (.leaf ⟨(32, 15075369877760), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00037.record086_result⟩)))))
 (.branch 93
 (.branch 90
 (.branch 88
 (.leaf ⟨(32, 15076484513792), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00037.record087_result⟩)
 (.branch 89
 (.leaf ⟨(32, 15077021319168), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00037.record088_result⟩)
 (.leaf ⟨(32, 15092540309760), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00037.record089_result⟩)))
 (.branch 91
 (.leaf ⟨(32, 15093077180416), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00037.record090_result⟩)
 (.branch 92
 (.leaf ⟨(32, 15101126050048), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00037.record091_result⟩)
 (.leaf ⟨(32, 15101662920704), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00037.record092_result⟩))))
 (.branch 96
 (.branch 94
 (.leaf ⟨(32, 15101671243776), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00037.record093_result⟩)
 (.branch 95
 (.leaf ⟨(32, 15101910646784), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00037.record094_result⟩)
 (.leaf ⟨(32, 15109695144192), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00037.record095_result⟩)))
 (.branch 98
 (.branch 97
 (.leaf ⟨(32, 15125533196544), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00037.record096_result⟩)
 (.leaf ⟨(32, 15125545226240), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00037.record097_result⟩))
 (.branch 99
 (.leaf ⟨(32, 15129425543424), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00037.record098_result⟩)
 (.leaf ⟨(32, 15129693946112), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00037.record099_result⟩))))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (30486 + i))) 0 100 :=
  interval_of_check _ 0 100 (by decide +kernel)

public theorem complete : Block 30486 30586 :=
  block_of_table results 30486 100 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock1002
