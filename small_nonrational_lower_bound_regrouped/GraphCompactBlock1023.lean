module
prelude
import GraphInputsSix0Part00058Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock1023
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 50
 (.branch 25
 (.branch 12
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(32, 22732599263232), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00058.record000_result⟩)
 (.branch 2
 (.leaf ⟨(32, 22732863504384), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00058.record001_result⟩)
 (.leaf ⟨(32, 22732871827456), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00058.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(32, 22732995624960), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00058.record003_result⟩)
 (.branch 5
 (.leaf ⟨(32, 22733934067968), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00058.record004_result⟩)
 (.leaf ⟨(32, 22739236749312), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00058.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(32, 22787225878784), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00058.record006_result⟩)
 (.branch 8
 (.leaf ⟨(32, 22800509239296), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00058.record007_result⟩)
 (.leaf ⟨(32, 22802052743424), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00058.record008_result⟩)))
 (.branch 10
 (.leaf ⟨(32, 22804405747712), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00058.record009_result⟩)
 (.branch 11
 (.leaf ⟨(32, 22804942553088), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00058.record010_result⟩)
 (.leaf ⟨(32, 22826220261440), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00058.record011_result⟩)))))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf ⟨(32, 22833460691200), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00058.record012_result⟩)
 (.branch 14
 (.leaf ⟨(32, 22835378552832), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00058.record013_result⟩)
 (.leaf ⟨(32, 22850394161408), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00058.record014_result⟩)))
 (.branch 16
 (.leaf ⟨(32, 22851929800960), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00058.record015_result⟩)
 (.branch 17
 (.leaf ⟨(32, 22851954411648), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00058.record016_result⟩)
 (.leaf ⟨(32, 22853254676736), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00058.record017_result⟩))))
 (.branch 21
 (.branch 19
 (.leaf ⟨(32, 22853265145856), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00058.record018_result⟩)
 (.branch 20
 (.leaf ⟨(32, 22859227398400), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00058.record019_result⟩)
 (.leaf ⟨(32, 22859495801088), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00058.record020_result⟩)))
 (.branch 23
 (.branch 22
 (.leaf ⟨(32, 22859506270208), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00058.record021_result⟩)
 (.leaf ⟨(32, 22862783086848), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00058.record022_result⟩))
 (.branch 24
 (.leaf ⟨(32, 22866517035136), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00058.record023_result⟩)
 (.leaf ⟨(32, 22867817300224), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00058.record024_result⟩))))))
 (.branch 37
 (.branch 31
 (.branch 28
 (.branch 26
 (.leaf ⟨(32, 22867827769344), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00058.record025_result⟩)
 (.branch 27
 (.leaf ⟨(32, 22869761491200), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00058.record026_result⟩)
 (.leaf ⟨(32, 22869769879552), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00058.record027_result⟩)))
 (.branch 29
 (.leaf ⟨(32, 22870298198656), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00058.record028_result⟩)
 (.branch 30
 (.leaf ⟨(32, 22876407267328), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00058.record029_result⟩)
 (.leaf ⟨(32, 22876944072704), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00058.record030_result⟩))))
 (.branch 34
 (.branch 32
 (.leaf ⟨(32, 22924660637952), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00058.record031_result⟩)
 (.branch 33
 (.leaf ⟨(32, 22925197508608), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00058.record032_result⟩)
 (.leaf ⟨(32, 22925205831680), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00058.record033_result⟩)))
 (.branch 35
 (.leaf ⟨(32, 22928821387520), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00058.record034_result⟩)
 (.branch 36
 (.leaf ⟨(32, 22929094017024), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00058.record035_result⟩)
 (.leaf ⟨(32, 22929358258176), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00058.record036_result⟩)))))
 (.branch 43
 (.branch 40
 (.branch 38
 (.leaf ⟨(32, 22929366581248), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00058.record037_result⟩)
 (.branch 39
 (.leaf ⟨(32, 22930901762304), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00058.record038_result⟩)
 (.leaf ⟨(32, 22931636813824), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00058.record039_result⟩)))
 (.branch 41
 (.leaf ⟨(32, 22937679757312), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00058.record040_result⟩)
 (.branch 42
 (.leaf ⟨(32, 22937688080384), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00058.record041_result⟩)
 (.leaf ⟨(32, 22943784534272), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00058.record042_result⟩))))
 (.branch 46
 (.branch 44
 (.leaf ⟨(32, 22948081631232), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00058.record043_result⟩)
 (.branch 45
 (.leaf ⟨(32, 22948354195456), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00058.record044_result⟩)
 (.leaf ⟨(32, 22948816617472), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00058.record045_result⟩)))
 (.branch 48
 (.branch 47
 (.leaf ⟨(32, 22955864162560), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00058.record046_result⟩)
 (.leaf ⟨(32, 22956132565248), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00058.record047_result⟩))
 (.branch 49
 (.leaf ⟨(32, 22956143034368), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00058.record048_result⟩)
 (.leaf ⟨(32, 22962582339584), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00058.record049_result⟩)))))))
 (.branch 75
 (.branch 62
 (.branch 56
 (.branch 53
 (.branch 51
 (.leaf ⟨(32, 22970903838720), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00058.record050_result⟩)
 (.branch 52
 (.leaf ⟨(32, 22980325343232), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00058.record051_result⟩)
 (.leaf ⟨(32, 22989099827456), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00058.record052_result⟩)))
 (.branch 54
 (.leaf ⟨(32, 22989368230144), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00058.record053_result⟩)
 (.branch 55
 (.leaf ⟨(32, 22989378699264), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00058.record054_result⟩)
 (.leaf ⟨(32, 22989618036992), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00058.record055_result⟩))))
 (.branch 59
 (.branch 57
 (.leaf ⟨(32, 22993782767616), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00058.record056_result⟩)
 (.branch 58
 (.leaf ⟨(32, 22995818004480), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00058.record057_result⟩)
 (.leaf ⟨(32, 22995859161344), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00058.record058_result⟩)))
 (.branch 60
 (.leaf ⟨(32, 23004180660480), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00058.record059_result⟩)
 (.branch 61
 (.leaf ⟨(32, 23004403744768), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00058.record060_result⟩)
 (.leaf ⟨(32, 23006797627968), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00058.record061_result⟩)))))
 (.branch 68
 (.branch 65
 (.branch 63
 (.leaf ⟨(32, 23014582403328), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00058.record062_result⟩)
 (.branch 64
 (.leaf ⟨(32, 23014716669952), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00058.record063_result⟩)
 (.leaf ⟨(32, 23014724993024), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00058.record064_result⟩)))
 (.branch 66
 (.leaf ⟨(32, 23015119273984), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00058.record065_result⟩)
 (.branch 67
 (.leaf ⟨(32, 23015253344768), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00058.record066_result⟩)
 (.leaf ⟨(32, 23027538526464), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00058.record067_result⟩))))
 (.branch 71
 (.branch 69
 (.leaf ⟨(32, 23028075397120), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00058.record068_result⟩)
 (.branch 70
 (.leaf ⟨(32, 23042567733504), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00058.record069_result⟩)
 (.leaf ⟨(32, 23095693901856), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00058.record070_result⟩)))
 (.branch 73
 (.branch 72
 (.leaf ⟨(32, 23099988852768), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00058.record071_result⟩)
 (.leaf ⟨(32, 23108574593056), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00058.record072_result⟩))
 (.branch 74
 (.leaf ⟨(32, 23127738351872), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00058.record073_result⟩)
 (.leaf ⟨(32, 23128006754560), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00058.record074_result⟩))))))
 (.branch 87
 (.branch 81
 (.branch 78
 (.branch 76
 (.leaf ⟨(32, 23128006819840), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00058.record075_result⟩)
 (.branch 77
 (.leaf ⟨(32, 23128008835328), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00058.record076_result⟩)
 (.leaf ⟨(32, 23129686606080), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00058.record077_result⟩)))
 (.branch 79
 (.leaf ⟨(32, 23129818726656), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00058.record078_result⟩)
 (.branch 80
 (.leaf ⟨(32, 23130087129344), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00058.record079_result⟩)
 (.leaf ⟨(32, 23130087194624), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00058.record080_result⟩))))
 (.branch 84
 (.branch 82
 (.leaf ⟨(32, 23130089210112), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00058.record081_result⟩)
 (.branch 83
 (.leaf ⟨(32, 23131230048512), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00058.record082_result⟩)
 (.leaf ⟨(32, 23133979476224), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00058.record083_result⟩)))
 (.branch 85
 (.leaf ⟨(32, 23134382080256), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00058.record084_result⟩)
 (.branch 86
 (.leaf ⟨(32, 23134382145536), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00058.record085_result⟩)
 (.leaf ⟨(32, 23135522918656), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00058.record086_result⟩)))))
 (.branch 93
 (.branch 90
 (.branch 88
 (.leaf ⟨(32, 23137603293440), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00058.record087_result⟩)
 (.branch 89
 (.leaf ⟨(32, 23142565216512), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00058.record088_result⟩)
 (.leaf ⟨(32, 23142569378048), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00058.record089_result⟩)))
 (.branch 91
 (.leaf ⟨(32, 23142569443328), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00058.record090_result⟩)
 (.branch 92
 (.leaf ⟨(32, 23142571458816), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00058.record091_result⟩)
 (.leaf ⟨(32, 23142703579392), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00058.record092_result⟩))))
 (.branch 96
 (.branch 94
 (.leaf ⟨(32, 23142703644672), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00058.record093_result⟩)
 (.branch 95
 (.leaf ⟨(32, 23142769704960), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00058.record094_result⟩)
 (.leaf ⟨(32, 23142967820544), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00058.record095_result⟩)))
 (.branch 98
 (.branch 97
 (.leaf ⟨(32, 23142974111808), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00058.record096_result⟩)
 (.leaf ⟨(32, 23143041212480), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00058.record097_result⟩))
 (.branch 99
 (.leaf ⟨(32, 23144114950208), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00058.record098_result⟩)
 (.leaf ⟨(32, 23163321286688), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00058.record099_result⟩))))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (32520 + i))) 0 100 :=
  interval_of_check _ 0 100 (by decide +kernel)

public theorem complete : Block 32520 32620 :=
  block_of_table results 32520 100 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock1023
