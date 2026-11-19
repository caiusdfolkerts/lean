module
prelude
import GraphInputsSix0Part00053Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock1018
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 50
 (.branch 25
 (.branch 12
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(32, 20420837249280), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00053.record000_result⟩)
 (.branch 2
 (.leaf ⟨(32, 20457336144128), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00053.record001_result⟩)
 (.leaf ⟨(32, 20480711540864), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00053.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(32, 20482859016320), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00053.record003_result⟩)
 (.branch 5
 (.leaf ⟨(32, 20485261758720), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00053.record004_result⟩)
 (.leaf ⟨(32, 20488275427584), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00053.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(32, 20488281669888), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00053.record006_result⟩)
 (.branch 8
 (.leaf ⟨(32, 20488413790464), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00053.record007_result⟩)
 (.leaf ⟨(32, 20488678031616), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00053.record008_result⟩)))
 (.branch 10
 (.leaf ⟨(32, 20489554628864), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00053.record009_result⟩)
 (.branch 11
 (.leaf ⟨(32, 20496999530752), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00053.record010_result⟩)
 (.leaf ⟨(32, 20498140369152), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00053.record011_result⟩)))))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf ⟨(32, 20552832057600), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00053.record012_result⟩)
 (.branch 14
 (.leaf ⟨(32, 20552840445952), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00053.record013_result⟩)
 (.leaf ⟨(32, 20557403799552), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00053.record014_result⟩)))
 (.branch 16
 (.leaf ⟨(32, 20557593592064), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00053.record015_result⟩)
 (.branch 17
 (.leaf ⟨(32, 20561962991616), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00053.record016_result⟩)
 (.leaf ⟨(32, 20574304796672), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00053.record017_result⟩))))
 (.branch 21
 (.branch 19
 (.leaf ⟨(32, 20626989388032), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00053.record018_result⟩)
 (.branch 20
 (.leaf ⟨(32, 20629978906624), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00053.record019_result⟩)
 (.leaf ⟨(32, 20638694654080), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00053.record020_result⟩)))
 (.branch 23
 (.branch 22
 (.leaf ⟨(32, 20685726449920), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00053.record021_result⟩)
 (.leaf ⟨(32, 20685726515200), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00053.record022_result⟩))
 (.branch 24
 (.leaf ⟨(32, 20685730644096), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00053.record023_result⟩)
 (.leaf ⟨(32, 20685732724864), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00053.record024_result⟩))))))
 (.branch 37
 (.branch 31
 (.branch 28
 (.branch 26
 (.leaf ⟨(32, 20685792510208), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00053.record025_result⟩)
 (.branch 27
 (.leaf ⟨(32, 20685792575488), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00053.record026_result⟩)
 (.leaf ⟨(32, 20685796704384), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00053.record027_result⟩)))
 (.branch 29
 (.leaf ⟨(32, 20685850151040), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00053.record028_result⟩)
 (.branch 30
 (.leaf ⟨(32, 20685924630784), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00053.record029_result⟩)
 (.leaf ⟨(32, 20685924696064), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00053.record030_result⟩))))
 (.branch 34
 (.branch 32
 (.leaf ⟨(32, 20685926776832), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00053.record031_result⟩)
 (.branch 33
 (.leaf ⟨(32, 20685927817216), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00053.record032_result⟩)
 (.leaf ⟨(32, 20685930905728), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00053.record033_result⟩)))
 (.branch 35
 (.leaf ⟨(32, 20685978077440), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00053.record034_result⟩)
 (.branch 36
 (.leaf ⟨(32, 20685982271616), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00053.record035_result⟩)
 (.leaf ⟨(32, 20686048331904), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00053.record036_result⟩)))))
 (.branch 43
 (.branch 40
 (.branch 38
 (.leaf ⟨(32, 20686193066112), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00053.record037_result⟩)
 (.branch 39
 (.leaf ⟨(32, 20686195146880), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00053.record038_result⟩)
 (.leaf ⟨(32, 20686195179520), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00053.record039_result⟩)))
 (.branch 41
 (.leaf ⟨(32, 20688198959105), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00053.record040_result⟩)
 (.branch 42
 (.leaf ⟨(32, 20688970713216), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00053.record041_result⟩)
 (.leaf ⟨(32, 20689144283392), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00053.record042_result⟩))))
 (.branch 46
 (.branch 44
 (.leaf ⟨(32, 20689144348672), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00053.record043_result⟩)
 (.branch 45
 (.leaf ⟨(32, 20689147469824), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00053.record044_result⟩)
 (.leaf ⟨(32, 20689164699904), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00053.record045_result⟩)))
 (.branch 48
 (.branch 47
 (.leaf ⟨(32, 20689168894080), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00053.record046_result⟩)
 (.leaf ⟨(32, 20689412718720), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00053.record047_result⟩))
 (.branch 49
 (.leaf ⟨(32, 20689415872512), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00053.record048_result⟩)
 (.leaf ⟨(32, 20690279333889), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00053.record049_result⟩)))))))
 (.branch 75
 (.branch 62
 (.branch 56
 (.branch 53
 (.branch 51
 (.leaf ⟨(32, 20693259389184), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00053.record050_result⟩)
 (.branch 52
 (.leaf ⟨(32, 20693263583360), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00053.record051_result⟩)
 (.leaf ⟨(32, 20693325449472), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00053.record052_result⟩)))
 (.branch 54
 (.leaf ⟨(32, 20693329643648), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00053.record053_result⟩)
 (.branch 55
 (.leaf ⟨(32, 20693439299584), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00053.record054_result⟩)
 (.leaf ⟨(32, 20693440339968), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00053.record055_result⟩))))
 (.branch 59
 (.branch 57
 (.leaf ⟨(32, 20693707669632), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00053.record056_result⟩)
 (.branch 58
 (.leaf ⟨(32, 20693707702272), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00053.record057_result⟩)
 (.leaf ⟨(32, 20693708742656), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00053.record058_result⟩)))
 (.branch 60
 (.leaf ⟨(32, 20694568075264), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00053.record059_result⟩)
 (.branch 61
 (.leaf ⟨(32, 20694572204033), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00053.record060_result⟩)
 (.leaf ⟨(32, 20694638264321), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00053.record061_result⟩)))))
 (.branch 68
 (.branch 65
 (.branch 63
 (.leaf ⟨(32, 20701849323648), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00053.record062_result⟩)
 (.branch 64
 (.leaf ⟨(32, 20701915383936), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00053.record063_result⟩)
 (.leaf ⟨(32, 20710385811456), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00053.record064_result⟩)))
 (.branch 66
 (.leaf ⟨(32, 20710435356672), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00053.record065_result⟩)
 (.branch 67
 (.leaf ⟨(32, 20711475412992), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00053.record066_result⟩)
 (.leaf ⟨(32, 20711607370368), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00053.record067_result⟩))))
 (.branch 71
 (.branch 69
 (.leaf ⟨(32, 20719077720320), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00053.record068_result⟩)
 (.branch 70
 (.leaf ⟨(32, 20719077785600), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00053.record069_result⟩)
 (.leaf ⟨(32, 20719081914496), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00053.record070_result⟩)))
 (.branch 73
 (.branch 72
 (.leaf ⟨(32, 20719085815936), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00053.record071_result⟩)
 (.leaf ⟨(32, 20719211986944), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00053.record072_result⟩))
 (.branch 74
 (.leaf ⟨(32, 20719213742336), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00053.record073_result⟩)
 (.leaf ⟨(32, 20719216115840), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00053.record074_result⟩))))))
 (.branch 87
 (.branch 81
 (.branch 78
 (.branch 76
 (.leaf ⟨(32, 20719216148480), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00053.record075_result⟩)
 (.branch 77
 (.leaf ⟨(32, 20719217936512), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00053.record076_result⟩)
 (.leaf ⟨(32, 20719337474056), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00053.record077_result⟩)))
 (.branch 79
 (.leaf ⟨(32, 20719482177664), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00053.record078_result⟩)
 (.branch 80
 (.leaf ⟨(32, 20723489966336), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00053.record079_result⟩)
 (.leaf ⟨(32, 20723490031616), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00053.record080_result⟩))))
 (.branch 84
 (.branch 82
 (.leaf ⟨(32, 20723494160512), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00053.record081_result⟩)
 (.branch 83
 (.leaf ⟨(32, 20723498222600), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00053.record082_result⟩)
 (.leaf ⟨(32, 20723514998785), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00053.record083_result⟩)))
 (.branch 85
 (.leaf ⟨(32, 20727650715904), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00053.record084_result⟩)
 (.branch 86
 (.leaf ⟨(32, 20727650781184), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00053.record085_result⟩)
 (.leaf ⟨(32, 20727654910080), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00053.record086_result⟩)))))
 (.branch 93
 (.branch 90
 (.branch 88
 (.leaf ⟨(32, 20727791092744), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00053.record087_result⟩)
 (.branch 89
 (.leaf ⟨(32, 20727803740160), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00053.record088_result⟩)
 (.leaf ⟨(32, 20727807868929), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00053.record089_result⟩)))
 (.branch 91
 (.leaf ⟨(32, 20728055333896), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00053.record090_result⟩)
 (.branch 92
 (.leaf ⟨(32, 20728072110081), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00053.record091_result⟩)
 (.leaf ⟨(32, 20736240650368), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00053.record092_result⟩))))
 (.branch 96
 (.branch 94
 (.leaf ⟨(32, 20748987139200), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00053.record093_result⟩)
 (.branch 95
 (.leaf ⟨(32, 20748991333376), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00053.record094_result⟩)
 (.leaf ⟨(32, 20749255442948), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00053.record095_result⟩)))
 (.branch 98
 (.branch 97
 (.leaf ⟨(32, 20754509889792), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00053.record096_result⟩)
 (.leaf ⟨(32, 20754567530624), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00053.record097_result⟩))
 (.branch 99
 (.leaf ⟨(32, 20756912209920), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00053.record098_result⟩)
 (.leaf ⟨(32, 20757688092800), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00053.record099_result⟩))))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (32050 + i))) 0 100 :=
  interval_of_check _ 0 100 (by decide +kernel)

public theorem complete : Block 32050 32150 :=
  block_of_table results 32050 100 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock1018
