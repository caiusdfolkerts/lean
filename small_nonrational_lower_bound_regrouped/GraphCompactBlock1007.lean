module
prelude
import GraphInputsSix0Part00042Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock1007
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 50
 (.branch 25
 (.branch 12
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(32, 16943801237504), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00042.record000_result⟩)
 (.branch 2
 (.leaf ⟨(32, 16943914551552), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00042.record001_result⟩)
 (.leaf ⟨(32, 16943922939904), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00042.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(32, 16943931196160), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00042.record003_result⟩)
 (.branch 5
 (.leaf ⟨(32, 16944451289608), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00042.record004_result⟩)
 (.leaf ⟨(32, 16948083689472), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00042.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(32, 16948477954112), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00042.record006_result⟩)
 (.branch 8
 (.leaf ⟨(32, 16948494598720), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00042.record007_result⟩)
 (.leaf ⟨(32, 16948612039176), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00042.record008_result⟩)))
 (.branch 10
 (.leaf ⟨(32, 16969415787012), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00042.record009_result⟩)
 (.branch 11
 (.leaf ⟨(32, 16969415918592), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00042.record010_result⟩)
 (.leaf ⟨(32, 16975877144832), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00042.record011_result⟩)))))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf ⟨(32, 16976013492224), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00042.record012_result⟩)
 (.branch 14
 (.leaf ⟨(32, 16976021815296), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00042.record013_result⟩)
 (.leaf ⟨(32, 16976153935872), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00042.record014_result⟩)))
 (.branch 16
 (.leaf ⟨(32, 16976261218304), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00042.record015_result⟩)
 (.branch 17
 (.leaf ⟨(32, 16978023579904), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00042.record016_result⟩)
 (.leaf ⟨(32, 16978292047872), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00042.record017_result⟩))))
 (.branch 21
 (.branch 19
 (.leaf ⟨(32, 16978300370944), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00042.record018_result⟩)
 (.branch 20
 (.leaf ⟨(32, 16978341593088), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00042.record019_result⟩)
 (.leaf ⟨(32, 16978811297792), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00042.record020_result⟩)))
 (.branch 23
 (.branch 22
 (.leaf ⟨(32, 16980153368832), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00042.record021_result⟩)
 (.leaf ⟨(32, 16980958511616), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00042.record022_result⟩))
 (.branch 24
 (.leaf ⟨(32, 16982502342656), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00042.record023_result⟩)
 (.leaf ⟨(32, 16982857482240), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00042.record024_result⟩))))))
 (.branch 37
 (.branch 31
 (.branch 28
 (.branch 26
 (.leaf ⟨(32, 16982972047360), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00042.record025_result⟩)
 (.branch 27
 (.leaf ⟨(32, 16985119261184), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00042.record026_result⟩)
 (.leaf ⟨(32, 16986595795200), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00042.record027_result⟩)))
 (.branch 29
 (.leaf ⟨(32, 17003775664128), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00042.record028_result⟩)
 (.branch 30
 (.leaf ⟨(32, 17003842764800), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00042.record029_result⟩)
 (.leaf ⟨(32, 17010356453376), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00042.record030_result⟩))))
 (.branch 34
 (.branch 32
 (.leaf ⟨(32, 17014789767168), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00042.record031_result⟩)
 (.branch 33
 (.leaf ⟨(32, 17015318249472), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00042.record032_result⟩)
 (.leaf ⟨(32, 17023639748608), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00042.record033_result⟩)))
 (.branch 35
 (.leaf ⟨(32, 17040282746880), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00042.record034_result⟩)
 (.branch 36
 (.leaf ⟨(32, 17042447669632), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00042.record035_result⟩)
 (.leaf ⟨(32, 17042447698192), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00042.record036_result⟩)))))
 (.branch 43
 (.branch 40
 (.branch 38
 (.leaf ⟨(32, 17042481381633), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00042.record037_result⟩)
 (.branch 39
 (.leaf ⟨(32, 17042481447168), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00042.record038_result⟩)
 (.leaf ⟨(32, 17042485088512), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00042.record039_result⟩)))
 (.branch 41
 (.leaf ⟨(32, 17042489282688), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00042.record040_result⟩)
 (.branch 42
 (.leaf ⟨(32, 17042489311248), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00042.record041_result⟩)
 (.leaf ⟨(32, 17042724163600), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00042.record042_result⟩))))
 (.branch 46
 (.branch 44
 (.leaf ⟨(32, 17042740938768), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00042.record043_result⟩)
 (.branch 45
 (.leaf ⟨(32, 17043558564608), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00042.record044_result⟩)
 (.leaf ⟨(32, 17043562758784), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00042.record045_result⟩)))
 (.branch 48
 (.branch 47
 (.leaf ⟨(32, 17043566919936), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00042.record046_result⟩)
 (.leaf ⟨(32, 17043566985216), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00042.record047_result⟩))
 (.branch 49
 (.leaf ⟨(32, 17043780995088), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00042.record048_result⟩)
 (.leaf ⟨(32, 17043793969408), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00042.record049_result⟩)))))))
 (.branch 75
 (.branch 62
 (.branch 56
 (.branch 53
 (.branch 51
 (.leaf ⟨(32, 17043797639696), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00042.record050_result⟩)
 (.branch 52
 (.leaf ⟨(32, 17043798130944), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00042.record051_result⟩)
 (.leaf ⟨(32, 17043798196224), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00042.record052_result⟩)))
 (.branch 54
 (.leaf ⟨(32, 17043801772288), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00042.record053_result⟩)
 (.branch 55
 (.leaf ⟨(32, 17044321863696), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00042.record054_result⟩)
 (.leaf ⟨(32, 17048105189632), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00042.record055_result⟩))))
 (.branch 59
 (.branch 57
 (.leaf ⟨(32, 17048113577984), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00042.record056_result⟩)
 (.branch 58
 (.leaf ⟨(32, 17048604803328), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00042.record057_result⟩)
 (.leaf ⟨(32, 17048616833024), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00042.record058_result⟩)))
 (.branch 60
 (.leaf ⟨(32, 17051314295040), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00042.record059_result⟩)
 (.branch 61
 (.leaf ⟨(32, 17051314360320), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00042.record060_result⟩)
 (.leaf ⟨(32, 17051578536192), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00042.record061_result⟩)))))
 (.branch 68
 (.branch 65
 (.branch 63
 (.leaf ⟨(32, 17051578601472), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00042.record062_result⟩)
 (.branch 64
 (.leaf ⟨(32, 17051586400272), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00042.record063_result⟩)
 (.leaf ⟨(32, 17051603175440), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00042.record064_result⟩)))
 (.branch 66
 (.leaf ⟨(32, 17052406448128), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00042.record065_result⟩)
 (.branch 67
 (.leaf ⟨(32, 17052497150208), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00042.record066_result⟩)
 (.leaf ⟨(32, 17052666462464), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00042.record067_result⟩))))
 (.branch 71
 (.branch 69
 (.leaf ⟨(32, 17052670689280), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00042.record068_result⟩)
 (.branch 70
 (.leaf ⟨(32, 17052676915201), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00042.record069_result⟩)
 (.leaf ⟨(32, 17052765552896), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00042.record070_result⟩)))
 (.branch 73
 (.branch 72
 (.leaf ⟨(32, 17052777582592), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00042.record071_result⟩)
 (.leaf ⟨(32, 17056120967424), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00042.record072_result⟩))
 (.branch 74
 (.leaf ⟨(32, 17082431373568), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00042.record073_result⟩)
 (.leaf ⟨(32, 17082968244224), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00042.record074_result⟩))))))
 (.branch 87
 (.branch 81
 (.branch 78
 (.branch 76
 (.leaf ⟨(32, 17082976567296), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00042.record075_result⟩)
 (.branch 77
 (.leaf ⟨(32, 17086592123136), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00042.record076_result⟩)
 (.leaf ⟨(32, 17086864752640), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00042.record077_result⟩)))
 (.branch 79
 (.leaf ⟨(32, 17087128993792), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00042.record078_result⟩)
 (.branch 80
 (.leaf ⟨(32, 17087137316864), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00042.record079_result⟩)
 (.leaf ⟨(32, 17089712685312), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00042.record080_result⟩))))
 (.branch 84
 (.branch 82
 (.leaf ⟨(32, 17090480766976), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00042.record081_result⟩)
 (.branch 83
 (.leaf ⟨(32, 17102595457280), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00042.record082_result⟩)
 (.leaf ⟨(32, 17120025444608), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00042.record083_result⟩)))
 (.branch 85
 (.leaf ⟨(32, 17120033832960), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00042.record084_result⟩)
 (.branch 86
 (.leaf ⟨(32, 17120050348032), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00042.record085_result⟩)
 (.leaf ⟨(32, 17120293847296), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00042.record086_result⟩)))))
 (.branch 93
 (.branch 90
 (.branch 88
 (.leaf ⟨(32, 17120305876992), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00042.record087_result⟩)
 (.branch 89
 (.leaf ⟨(32, 17120545214720), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00042.record088_result⟩)
 (.leaf ⟨(32, 17121618690816), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00042.record089_result⟩)))
 (.branch 91
 (.leaf ⟨(32, 17137724817936), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00042.record090_result⟩)
 (.branch 92
 (.leaf ⟨(32, 17146855883008), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00042.record091_result⟩)
 (.leaf ⟨(32, 17155450011648), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00042.record092_result⟩))))
 (.branch 96
 (.branch 94
 (.leaf ⟨(32, 17155986817024), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00042.record093_result⟩)
 (.branch 95
 (.leaf ⟨(32, 17171279413504), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00042.record094_result⟩)
 (.leaf ⟨(32, 17171317063680), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00042.record095_result⟩)))
 (.branch 98
 (.branch 97
 (.leaf ⟨(32, 17172084556288), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00042.record096_result⟩)
 (.leaf ⟨(32, 17172085080064), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00042.record097_result⟩))
 (.branch 99
 (.leaf ⟨(32, 17172629815296), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00042.record098_result⟩)
 (.leaf ⟨(32, 17173158297600), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00042.record099_result⟩))))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (30986 + i))) 0 100 :=
  interval_of_check _ 0 100 (by decide +kernel)

public theorem complete : Block 30986 31086 :=
  block_of_table results 30986 100 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock1007
