module
prelude
import GraphInputsSix0Part00060Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock1025
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 50
 (.branch 25
 (.branch 12
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(32, 23421876436992), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00060.record000_result⟩)
 (.branch 2
 (.leaf ⟨(32, 23422336778240), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00060.record001_result⟩)
 (.leaf ⟨(32, 23422404919296), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00060.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(32, 23425894596864), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00060.record003_result⟩)
 (.branch 5
 (.leaf ⟨(32, 23426028863488), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00060.record004_result⟩)
 (.leaf ⟨(32, 23426037186560), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00060.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(32, 23426431467520), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00060.record006_result⟩)
 (.branch 8
 (.leaf ⟨(32, 23426497527808), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00060.record007_result⟩)
 (.leaf ⟨(32, 23429081219328), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00060.record008_result⟩)))
 (.branch 10
 (.leaf ⟨(32, 23429149425664), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00060.record009_result⟩)
 (.branch 11
 (.leaf ⟨(32, 23429157748736), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00060.record010_result⟩)
 (.leaf ⟨(32, 23429618089984), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00060.record011_result⟩)))))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf ⟨(32, 23436900499712), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00060.record012_result⟩)
 (.branch 14
 (.leaf ⟨(32, 23437168902400), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00060.record013_result⟩)
 (.leaf ⟨(32, 23437179371520), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00060.record014_result⟩)))
 (.branch 16
 (.leaf ⟨(32, 23443618676736), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00060.record015_result⟩)
 (.branch 17
 (.leaf ⟨(32, 23451940175872), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00060.record016_result⟩)
 (.leaf ⟨(32, 23461361680384), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00060.record017_result⟩))))
 (.branch 21
 (.branch 19
 (.leaf ⟨(32, 23461370003456), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00060.record018_result⟩)
 (.branch 20
 (.leaf ⟨(32, 23470004044032), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00060.record019_result⟩)
 (.leaf ⟨(32, 23470012432384), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00060.record020_result⟩)))
 (.branch 23
 (.branch 22
 (.leaf ⟨(32, 23470136164608), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00060.record021_result⟩)
 (.leaf ⟨(32, 23470144552960), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00060.record022_result⟩))
 (.branch 24
 (.leaf ⟨(32, 23470251770112), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00060.record023_result⟩)
 (.leaf ⟨(32, 23470404567296), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00060.record024_result⟩))))))
 (.branch 37
 (.branch 31
 (.branch 28
 (.branch 26
 (.leaf ⟨(32, 23470408794112), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00060.record025_result⟩)
 (.branch 27
 (.leaf ⟨(32, 23470415036416), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00060.record026_result⟩)
 (.leaf ⟨(32, 23470520172800), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00060.record027_result⟩)))
 (.branch 29
 (.leaf ⟨(32, 23470532462592), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00060.record028_result⟩)
 (.branch 30
 (.leaf ⟨(32, 23470654374144), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00060.record029_result⟩)
 (.leaf ⟨(32, 23474819104768), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00060.record030_result⟩))))
 (.branch 34
 (.branch 32
 (.leaf ⟨(32, 23474949063424), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00060.record031_result⟩)
 (.branch 33
 (.leaf ⟨(32, 23476492894464), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00060.record032_result⟩)
 (.leaf ⟨(32, 23476845953280), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00060.record033_result⟩)))
 (.branch 35
 (.leaf ⟨(32, 23476848099328), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00060.record034_result⟩)
 (.branch 36
 (.leaf ⟨(32, 23476854341632), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00060.record035_result⟩)
 (.leaf ⟨(32, 23476895498496), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00060.record036_result⟩)))))
 (.branch 43
 (.branch 40
 (.branch 38
 (.leaf ⟨(32, 23476905707520), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00060.record037_result⟩)
 (.branch 39
 (.leaf ⟨(32, 23479109812992), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00060.record038_result⟩)
 (.leaf ⟨(32, 23485082796288), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00060.record039_result⟩)))
 (.branch 41
 (.leaf ⟨(32, 23485095086080), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00060.record040_result⟩)
 (.branch 42
 (.leaf ⟨(32, 23485216997632), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00060.record041_result⟩)
 (.leaf ⟨(32, 23485227206656), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00060.record042_result⟩))))
 (.branch 46
 (.branch 44
 (.leaf ⟨(32, 23485440081920), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00060.record043_result⟩)
 (.branch 45
 (.leaf ⟨(32, 23485686751296), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00060.record044_result⟩)
 (.leaf ⟨(32, 23487833965120), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00060.record045_result⟩)))
 (.branch 48
 (.branch 47
 (.leaf ⟨(32, 23491323789568), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00060.record046_result⟩)
 (.leaf ⟨(32, 23491592257536), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00060.record047_result⟩))
 (.branch 49
 (.leaf ⟨(32, 23491600580608), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00060.record048_result⟩)
 (.leaf ⟨(32, 23492128932352), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00060.record049_result⟩)))))))
 (.branch 75
 (.branch 62
 (.branch 56
 (.branch 53
 (.branch 51
 (.leaf ⟨(32, 23495618740480), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00060.record050_result⟩)
 (.branch 52
 (.leaf ⟨(32, 23495753007104), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00060.record051_result⟩)
 (.leaf ⟨(32, 23495761330176), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00060.record052_result⟩)))
 (.branch 54
 (.leaf ⟨(32, 23496155611136), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00060.record053_result⟩)
 (.branch 55
 (.leaf ⟨(32, 23496289681920), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00060.record054_result⟩)
 (.leaf ⟨(32, 23505485758720), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00060.record055_result⟩))))
 (.branch 59
 (.branch 57
 (.leaf ⟨(32, 23505494147072), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00060.record056_result⟩)
 (.branch 58
 (.leaf ⟨(32, 23505888362752), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00060.record057_result⟩)
 (.leaf ⟨(32, 23505896751104), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00060.record058_result⟩)))
 (.branch 60
 (.leaf ⟨(32, 23505954423040), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00060.record059_result⟩)
 (.branch 61
 (.leaf ⟨(32, 23508043186176), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00060.record060_result⟩)
 (.leaf ⟨(32, 23508713799680), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00060.record061_result⟩)))))
 (.branch 68
 (.branch 65
 (.branch 63
 (.leaf ⟨(32, 23509074985216), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00060.record062_result⟩)
 (.branch 64
 (.leaf ⟨(32, 23509083373568), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00060.record063_result⟩)
 (.leaf ⟨(32, 23520919699520), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00060.record064_result⟩)))
 (.branch 66
 (.leaf ⟨(32, 23522060017728), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00060.record065_result⟩)
 (.branch 67
 (.leaf ⟨(32, 23525717983488), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00060.record066_result⟩)
 (.leaf ⟨(32, 23525786189824), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00060.record067_result⟩))))
 (.branch 71
 (.branch 69
 (.leaf ⟨(32, 23525794512896), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00060.record068_result⟩)
 (.branch 70
 (.leaf ⟨(32, 23525893603328), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00060.record069_result⟩)
 (.leaf ⟨(32, 23526254854144), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00060.record070_result⟩)))
 (.branch 73
 (.branch 72
 (.leaf ⟨(32, 23538721423616), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00060.record071_result⟩)
 (.leaf ⟨(32, 23538729811968), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00060.record072_result⟩))
 (.branch 74
 (.leaf ⟨(32, 23539124027648), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00060.record073_result⟩)
 (.leaf ⟨(32, 23539132416000), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00060.record074_result⟩))))))
 (.branch 87
 (.branch 81
 (.branch 78
 (.branch 76
 (.leaf ⟨(32, 23539239633152), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00060.record075_result⟩)
 (.branch 77
 (.leaf ⟨(32, 23539249842176), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00060.record076_result⟩)
 (.leaf ⟨(32, 23540876247040), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00060.record077_result⟩)))
 (.branch 79
 (.leaf ⟨(32, 23540917403904), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00060.record078_result⟩)
 (.branch 80
 (.leaf ⟨(32, 23541270462720), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00060.record079_result⟩)
 (.leaf ⟨(32, 23541272608768), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00060.record080_result⟩))))
 (.branch 84
 (.branch 82
 (.leaf ⟨(32, 23541278851072), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00060.record081_result⟩)
 (.branch 83
 (.leaf ⟨(32, 23541320007936), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00060.record082_result⟩)
 (.leaf ⟨(32, 23541330216960), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00060.record083_result⟩)))
 (.branch 85
 (.leaf ⟨(32, 23543534322432), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00060.record084_result⟩)
 (.branch 86
 (.leaf ⟨(32, 23553802256640), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00060.record085_result⟩)
 (.leaf ⟨(32, 23553812465664), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00060.record086_result⟩)))))
 (.branch 93
 (.branch 90
 (.branch 88
 (.leaf ⟨(32, 23554155364416), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00060.record087_result⟩)
 (.branch 89
 (.leaf ⟨(32, 23554157461504), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00060.record088_result⟩)
 (.leaf ⟨(32, 23554204909632), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00060.record089_result⟩)))
 (.branch 91
 (.leaf ⟨(32, 23554272010304), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00060.record090_result⟩)
 (.branch 92
 (.leaf ⟨(32, 23556419224128), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00060.record091_result⟩)
 (.leaf ⟨(32, 23573014053120), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00060.record092_result⟩))))
 (.branch 96
 (.branch 94
 (.leaf ⟨(32, 23573491105792), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00060.record093_result⟩)
 (.branch 95
 (.leaf ⟨(32, 23573532262656), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00060.record094_result⟩)
 (.leaf ⟨(32, 23590711853632), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00060.record095_result⟩)))
 (.branch 98
 (.branch 97
 (.leaf ⟨(32, 23642901643520), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00060.record096_result⟩)
 (.leaf ⟨(32, 23643033764096), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00060.record097_result⟩))
 (.branch 99
 (.leaf ⟨(32, 23643298005248), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00060.record098_result⟩)
 (.leaf ⟨(32, 23643302166784), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00060.record099_result⟩))))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (32720 + i))) 0 100 :=
  interval_of_check _ 0 100 (by decide +kernel)

public theorem complete : Block 32720 32820 :=
  block_of_table results 32720 100 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock1025
