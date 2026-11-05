module
prelude
import GraphInputsSix0Part00077Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock1042
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 50
 (.branch 25
 (.branch 12
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(32, 29689131894912), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00077.record000_result⟩)
 (.branch 2
 (.leaf ⟨(32, 29690343473408), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00077.record001_result⟩)
 (.leaf ⟨(32, 29690444124416), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00077.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(32, 29691212269696), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00077.record003_result⟩)
 (.branch 5
 (.leaf ⟨(32, 29691261554816), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00077.record004_result⟩)
 (.leaf ⟨(32, 29692489908480), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00077.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(32, 29692524499200), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00077.record006_result⟩)
 (.branch 8
 (.leaf ⟨(32, 29696685248768), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00077.record007_result⟩)
 (.leaf ⟨(32, 29696782778624), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00077.record008_result⟩)))
 (.branch 10
 (.leaf ⟨(32, 29725758603520), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00077.record009_result⟩)
 (.branch 11
 (.leaf ⟨(32, 29725760164096), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00077.record010_result⟩)
 (.leaf ⟨(32, 29726815174912), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00077.record011_result⟩)))))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf ⟨(32, 29757972418816), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00077.record012_result⟩)
 (.branch 14
 (.leaf ⟨(32, 29760118853888), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00077.record013_result⟩)
 (.leaf ⟨(32, 29764411724032), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00077.record014_result⟩)))
 (.branch 16
 (.leaf ⟨(32, 29765500158208), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00077.record015_result⟩)
 (.branch 17
 (.leaf ⟨(32, 29826557677824), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00077.record016_result⟩)
 (.leaf ⟨(32, 29828704112896), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00077.record017_result⟩))))
 (.branch 21
 (.branch 19
 (.leaf ⟨(32, 29828836233472), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00077.record018_result⟩)
 (.branch 20
 (.leaf ⟨(32, 29829924667648), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00077.record019_result⟩)
 (.leaf ⟨(32, 29838783037440), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00077.record020_result⟩)))
 (.branch 23
 (.branch 22
 (.leaf ⟨(32, 29894332399872), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00077.record021_result⟩)
 (.leaf ⟨(32, 29902133010496), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00077.record022_result⟩))
 (.branch 24
 (.leaf ⟨(32, 30030464813184), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00077.record023_result⟩)
 (.leaf ⟨(32, 30031554414720), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00077.record024_result⟩))))))
 (.branch 37
 (.branch 31
 (.branch 28
 (.branch 26
 (.leaf ⟨(32, 30031554447360), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00077.record025_result⟩)
 (.branch 27
 (.leaf ⟨(32, 30236620931328), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00077.record026_result⟩)
 (.leaf ⟨(32, 30236620963968), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00077.record027_result⟩)))
 (.branch 29
 (.leaf ⟨(32, 30236622491904), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00077.record028_result⟩)
 (.branch 30
 (.leaf ⟨(32, 30236622524544), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00077.record029_result⟩)
 (.leaf ⟨(32, 30236622553104), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00077.record030_result⟩))))
 (.branch 34
 (.branch 32
 (.leaf ⟨(32, 30236628795408), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00077.record031_result⟩)
 (.branch 33
 (.leaf ⟨(32, 30236725284880), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00077.record032_result⟩)
 (.leaf ⟨(32, 30236725544976), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00077.record033_result⟩)))
 (.branch 35
 (.leaf ⟨(32, 30237695968000), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00077.record034_result⟩)
 (.branch 36
 (.leaf ⟨(32, 30237696000640), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00077.record035_result⟩)
 (.leaf ⟨(32, 30237782116368), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00077.record036_result⟩)))))
 (.branch 43
 (.branch 40
 (.branch 38
 (.leaf ⟨(32, 30237782246416), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00077.record037_result⟩)
 (.branch 39
 (.leaf ⟨(32, 30237933453568), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00077.record038_result⟩)
 (.leaf ⟨(32, 30237935014144), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00077.record039_result⟩)))
 (.branch 41
 (.leaf ⟨(32, 30241154666752), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00077.record040_result⟩)
 (.branch 42
 (.leaf ⟨(32, 30242211238144), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00077.record041_result⟩)
 (.leaf ⟨(32, 30242246819840), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00077.record042_result⟩))))
 (.branch 46
 (.branch 44
 (.leaf ⟨(32, 30249857847552), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00077.record043_result⟩)
 (.branch 45
 (.leaf ⟨(32, 30284217647104), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00077.record044_result⟩)
 (.leaf ⟨(32, 30305306509328), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00077.record045_result⟩)))
 (.branch 48
 (.branch 47
 (.leaf ⟨(32, 30305310410768), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00077.record046_result⟩)
 (.leaf ⟨(32, 30305578914048), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00077.record047_result⟩))
 (.branch 49
 (.leaf ⟨(32, 30309874204672), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00077.record048_result⟩)
 (.leaf ⟨(32, 30310930776064), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00077.record049_result⟩)))))))
 (.branch 75
 (.branch 62
 (.branch 56
 (.branch 53
 (.branch 51
 (.leaf ⟨(32, 30314282094848), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00077.record050_result⟩)
 (.branch 52
 (.leaf ⟨(32, 30315355570944), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00077.record051_result⟩)
 (.leaf ⟨(32, 30316429901824), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00077.record052_result⟩)))
 (.branch 54
 (.leaf ⟨(32, 30349723697152), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00077.record053_result⟩)
 (.branch 55
 (.leaf ⟨(32, 30374164173056), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00077.record054_result⟩)
 (.leaf ⟨(32, 30446360461312), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00077.record055_result⟩))))
 (.branch 59
 (.branch 57
 (.leaf ⟨(32, 30448440836096), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00077.record056_result⟩)
 (.branch 58
 (.leaf ⟨(32, 30457802522624), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00077.record057_result⟩)
 (.leaf ⟨(32, 30458331004928), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00077.record058_result⟩)))
 (.branch 60
 (.leaf ⟨(32, 30481676500992), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00077.record059_result⟩)
 (.branch 61
 (.leaf ⟨(32, 30489973030912), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00077.record060_result⟩)
 (.leaf ⟨(32, 30511464890384), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00077.record061_result⟩)))))
 (.branch 68
 (.branch 65
 (.branch 63
 (.leaf ⟨(32, 30511466711056), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00077.record062_result⟩)
 (.branch 64
 (.leaf ⟨(32, 30717606495240), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00077.record063_result⟩)
 (.leaf ⟨(32, 30717606497280), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00077.record064_result⟩)))
 (.branch 66
 (.leaf ⟨(32, 30717623271425), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00077.record065_result⟩)
 (.branch 67
 (.leaf ⟨(32, 30787452871040), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00077.record066_result⟩)
 (.leaf ⟨(32, 30787459162304), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00077.record067_result⟩))))
 (.branch 71
 (.branch 69
 (.leaf ⟨(32, 30787484860800), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00077.record068_result⟩)
 (.branch 70
 (.leaf ⟨(32, 30787485901184), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00077.record069_result⟩)
 (.leaf ⟨(32, 30787492192448), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00077.record070_result⟩)))
 (.branch 73
 (.branch 72
 (.leaf ⟨(32, 30787555107104), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00077.record071_result⟩)
 (.leaf ⟨(32, 30787555627296), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00077.record072_result⟩))
 (.branch 74
 (.leaf ⟨(32, 30789649630080), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00077.record073_result⟩)
 (.leaf ⟨(32, 30789653856512), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00077.record074_result⟩))))))
 (.branch 87
 (.branch 81
 (.branch 78
 (.branch 76
 (.leaf ⟨(32, 30789655921344), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00077.record075_result⟩)
 (.branch 77
 (.leaf ⟨(32, 30789660147776), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00077.record076_result⟩)
 (.leaf ⟨(32, 30789685416224), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00077.record077_result⟩)))
 (.branch 79
 (.leaf ⟨(32, 30789685806368), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00077.record078_result⟩)
 (.branch 80
 (.leaf ⟨(32, 30789719884033), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00077.record079_result⟩)
 (.leaf ⟨(32, 30789719916800), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00077.record080_result⟩))))
 (.branch 84
 (.branch 82
 (.leaf ⟨(32, 30789727256608), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00077.record081_result⟩)
 (.branch 83
 (.leaf ⟨(32, 30789854118144), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00077.record082_result⟩)
 (.leaf ⟨(32, 30789858279680), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00077.record083_result⟩)))
 (.branch 85
 (.leaf ⟨(32, 30789858328640), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00077.record084_result⟩)
 (.branch 86
 (.leaf ⟨(32, 30789859377184), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00077.record085_result⟩)
 (.leaf ⟨(32, 30792001593600), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00077.record086_result⟩)))))
 (.branch 93
 (.branch 90
 (.branch 88
 (.leaf ⟨(32, 30792005812256), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00077.record087_result⟩)
 (.branch 89
 (.leaf ⟨(32, 30792035143936), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00077.record088_result⟩)
 (.leaf ⟨(32, 30793079029792), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00077.record089_result⟩)))
 (.branch 91
 (.leaf ⟨(32, 30796300755008), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00077.record090_result⟩)
 (.branch 92
 (.leaf ⟨(32, 30796300763168), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00077.record091_result⟩)
 (.leaf ⟨(32, 30796564996160), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00077.record092_result⟩))))
 (.branch 96
 (.branch 94
 (.leaf ⟨(32, 30796565004320), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00077.record093_result⟩)
 (.branch 95
 (.leaf ⟨(32, 30820840837408), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00077.record094_result⟩)
 (.leaf ⟨(32, 30824026112256), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00077.record095_result⟩)))
 (.branch 98
 (.branch 97
 (.leaf ⟨(32, 30824030339072), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00077.record096_result⟩)
 (.leaf ⟨(32, 30824038662144), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00077.record097_result⟩))
 (.branch 99
 (.leaf ⟨(32, 30824045019908), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00077.record098_result⟩)
 (.leaf ⟨(32, 30824045150465), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00077.record099_result⟩))))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (34272 + i))) 0 100 :=
  interval_of_check _ 0 100 (by decide +kernel)

public theorem complete : Block 34272 34372 :=
  block_of_table results 34272 100 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock1042
