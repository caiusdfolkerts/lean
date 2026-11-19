module
prelude
import GraphInputsSix0Part00062Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock1027
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 50
 (.branch 25
 (.branch 12
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(32, 24053447458816), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00062.record000_result⟩)
 (.branch 2
 (.leaf ⟨(32, 24053453701120), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00062.record001_result⟩)
 (.leaf ⟨(32, 24053494857984), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00062.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(32, 24053505067008), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00062.record003_result⟩)
 (.branch 5
 (.leaf ⟨(32, 24054124314624), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00062.record004_result⟩)
 (.leaf ⟨(32, 24054132441344), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00062.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(32, 24054520676352), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00062.record006_result⟩)
 (.branch 8
 (.leaf ⟨(32, 24054526918656), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00062.record007_result⟩)
 (.leaf ⟨(32, 24054535045376), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00062.record008_result⟩)))
 (.branch 10
 (.leaf ⟨(32, 24054545254400), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00062.record009_result⟩)
 (.branch 11
 (.leaf ⟨(32, 24055709172480), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00062.record010_result⟩)
 (.leaf ⟨(32, 24058829734656), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00062.record011_result⟩)))))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf ⟨(32, 24069097668864), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00062.record012_result⟩)
 (.branch 14
 (.leaf ⟨(32, 24069107877888), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00062.record013_result⟩)
 (.leaf ⟨(32, 24069206968320), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00062.record014_result⟩)))
 (.branch 16
 (.leaf ⟨(32, 24069550907456), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00062.record015_result⟩)
 (.branch 17
 (.leaf ⟨(32, 24069551964160), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00062.record016_result⟩)
 (.leaf ⟨(32, 24069567422528), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00062.record017_result⟩))))
 (.branch 21
 (.branch 19
 (.leaf ⟨(32, 24070674448960), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00062.record018_result⟩)
 (.branch 20
 (.leaf ⟨(32, 24086327918848), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00062.record019_result⟩)
 (.leaf ⟨(32, 24086336307200), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00062.record020_result⟩)))
 (.branch 23
 (.branch 22
 (.leaf ⟨(32, 24086730522880), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00062.record021_result⟩)
 (.leaf ⟨(32, 24086738911232), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00062.record022_result⟩))
 (.branch 24
 (.leaf ⟨(32, 24086740731904), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00062.record023_result⟩)
 (.leaf ⟨(32, 24086847949056), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00062.record024_result⟩))))))
 (.branch 37
 (.branch 31
 (.branch 28
 (.branch 26
 (.leaf ⟨(32, 24091008567552), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00062.record025_result⟩)
 (.branch 27
 (.leaf ⟨(32, 24091016955904), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00062.record026_result⟩)
 (.leaf ⟨(32, 24091025212160), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00062.record027_result⟩)))
 (.branch 29
 (.leaf ⟨(32, 24103499204608), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00062.record028_result⟩)
 (.branch 30
 (.leaf ⟨(32, 24103893469248), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00062.record029_result⟩)
 (.leaf ⟨(32, 24103910113856), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00062.record030_result⟩))))
 (.branch 34
 (.branch 32
 (.leaf ⟨(32, 24104027554312), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00062.record031_result⟩)
 (.branch 33
 (.leaf ⟨(32, 24192588267648), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00062.record032_result⟩)
 (.leaf ⟨(32, 24192654327936), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00062.record033_result⟩)))
 (.branch 35
 (.leaf ⟨(32, 24193050689664), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00062.record034_result⟩)
 (.branch 36
 (.leaf ⟨(32, 24194801803392), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00062.record035_result⟩)
 (.leaf ⟨(32, 24194804973600), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00062.record036_result⟩)))))
 (.branch 43
 (.branch 40
 (.branch 38
 (.leaf ⟨(32, 24194937094176), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00062.record037_result⟩)
 (.branch 39
 (.leaf ⟨(32, 24195198165120), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00062.record038_result⟩)
 (.leaf ⟨(32, 24195201335328), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00062.record039_result⟩)))
 (.branch 41
 (.leaf ⟨(32, 24199232045088), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00062.record040_result⟩)
 (.branch 42
 (.leaf ⟨(32, 24199496286240), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00062.record041_result⟩)
 (.leaf ⟨(32, 24208083017856), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00062.record042_result⟩))))
 (.branch 46
 (.branch 44
 (.leaf ⟨(32, 24208086188064), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00062.record043_result⟩)
 (.branch 45
 (.leaf ⟨(32, 24225923022976), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00062.record044_result⟩)
 (.leaf ⟨(32, 24227245785344), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00062.record045_result⟩)))
 (.branch 48
 (.branch 47
 (.leaf ⟨(32, 24227249946880), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00062.record046_result⟩)
 (.leaf ⟨(32, 24227250012160), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00062.record047_result⟩))
 (.branch 49
 (.leaf ⟨(32, 24227252027648), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00062.record048_result⟩)
 (.leaf ⟨(32, 24227654680640), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00062.record049_result⟩)))))))
 (.branch 75
 (.branch 62
 (.branch 56
 (.branch 53
 (.branch 51
 (.leaf ⟨(32, 24228070498432), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00062.record050_result⟩)
 (.branch 52
 (.leaf ⟨(32, 24228473102464), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00062.record051_result⟩)
 (.leaf ⟨(32, 24229198201088), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00062.record052_result⟩)))
 (.branch 54
 (.leaf ⟨(32, 24229198266368), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00062.record053_result⟩)
 (.branch 55
 (.leaf ⟨(32, 24229326160128), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00062.record054_result⟩)
 (.leaf ⟨(32, 24229330321664), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00062.record055_result⟩))))
 (.branch 59
 (.branch 57
 (.leaf ⟨(32, 24229330386944), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00062.record056_result⟩)
 (.branch 58
 (.leaf ⟨(32, 24229332402432), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00062.record057_result⟩)
 (.leaf ⟨(32, 24229396381952), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00062.record058_result⟩)))
 (.branch 60
 (.leaf ⟨(32, 24229529673856), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00062.record059_result⟩)
 (.branch 61
 (.leaf ⟨(32, 24229802156096), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00062.record060_result⟩)
 (.leaf ⟨(32, 24230473240832), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00062.record061_result⟩)))))
 (.branch 68
 (.branch 65
 (.branch 63
 (.leaf ⟨(32, 24230875893824), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00062.record062_result⟩)
 (.branch 64
 (.leaf ⟨(32, 24233486909696), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00062.record063_result⟩)
 (.leaf ⟨(32, 24233491071232), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00062.record064_result⟩)))
 (.branch 66
 (.leaf ⟨(32, 24233491136512), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00062.record065_result⟩)
 (.branch 67
 (.leaf ⟨(32, 24233493152000), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00062.record066_result⟩)
 (.leaf ⟨(32, 24233625272576), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00062.record067_result⟩))))
 (.branch 71
 (.branch 69
 (.leaf ⟨(32, 24233625337856), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00062.record068_result⟩)
 (.branch 70
 (.leaf ⟨(32, 24233889513728), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00062.record069_result⟩)
 (.leaf ⟨(32, 24233889579008), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00062.record070_result⟩)))
 (.branch 73
 (.branch 72
 (.leaf ⟨(32, 24233895804992), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00062.record071_result⟩)
 (.leaf ⟨(32, 24233962905664), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00062.record072_result⟩))
 (.branch 74
 (.leaf ⟨(32, 24234766110976), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00062.record073_result⟩)
 (.leaf ⟨(32, 24235036643392), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00062.record074_result⟩))))))
 (.branch 87
 (.branch 81
 (.branch 78
 (.branch 76
 (.leaf ⟨(32, 24236912546048), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00062.record075_result⟩)
 (.branch 77
 (.leaf ⟨(32, 24242211012864), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00062.record076_result⟩)
 (.leaf ⟨(32, 24243358142528), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00062.record077_result⟩)))
 (.branch 79
 (.leaf ⟨(32, 24260215652480), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00062.record078_result⟩)
 (.branch 80
 (.leaf ⟨(32, 24260282753152), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00062.record079_result⟩)
 (.leaf ⟨(32, 24262564479008), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00062.record080_result⟩))))
 (.branch 84
 (.branch 82
 (.leaf ⟨(32, 24263621050400), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00062.record081_result⟩)
 (.branch 83
 (.leaf ⟨(32, 24266859429920), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00062.record082_result⟩)
 (.leaf ⟨(32, 24267123671072), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00062.record083_result⟩)))
 (.branch 85
 (.leaf ⟨(32, 24267127832608), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00062.record084_result⟩)
 (.branch 86
 (.leaf ⟨(32, 24267983962368), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00062.record085_result⟩)
 (.leaf ⟨(32, 24269329272896), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00062.record086_result⟩)))))
 (.branch 93
 (.branch 90
 (.branch 88
 (.leaf ⟨(32, 24275713572896), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00062.record087_result⟩)
 (.branch 89
 (.leaf ⟨(32, 24276569702656), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00062.record088_result⟩)
 (.leaf ⟨(32, 24293478203400), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00062.record089_result⟩)))
 (.branch 91
 (.leaf ⟨(32, 24299184390400), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00062.record090_result⟩)
 (.branch 92
 (.leaf ⟨(32, 24299595366401), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00062.record091_result⟩)
 (.leaf ⟨(32, 24302805074176), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00062.record092_result⟩))))
 (.branch 96
 (.branch 94
 (.leaf ⟨(32, 24303756115969), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00062.record093_result⟩)
 (.branch 95
 (.leaf ⟨(32, 24305892098304), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00062.record094_result⟩)
 (.leaf ⟨(32, 24319247810816), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00062.record095_result⟩)))
 (.branch 98
 (.branch 97
 (.leaf ⟨(32, 24319384158208), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00062.record096_result⟩)
 (.leaf ⟨(32, 24319392481280), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00062.record097_result⟩))
 (.branch 99
 (.leaf ⟨(32, 24319516278784), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00062.record098_result⟩)
 (.leaf ⟨(32, 24319524601856), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00062.record099_result⟩))))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (32920 + i))) 0 100 :=
  interval_of_check _ 0 100 (by decide +kernel)

public theorem complete : Block 32920 33020 :=
  block_of_table results 32920 100 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock1027
