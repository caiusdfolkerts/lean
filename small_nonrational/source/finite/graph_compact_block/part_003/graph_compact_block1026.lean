module
prelude
import GraphInputsSix0Part00061Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock1026
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 50
 (.branch 25
 (.branch 12
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(32, 23643302232064), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00061.record000_result⟩)
 (.branch 2
 (.leaf ⟨(32, 23643304247552), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00061.record001_result⟩)
 (.leaf ⟨(32, 23643404898560), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00061.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(32, 23649737310464), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00061.record003_result⟩)
 (.branch 5
 (.leaf ⟨(32, 23649743552768), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00061.record004_result⟩)
 (.leaf ⟨(32, 23649743618048), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00061.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(32, 23649778143488), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00061.record006_result⟩)
 (.branch 8
 (.leaf ⟨(32, 23657967522048), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00061.record007_result⟩)
 (.leaf ⟨(32, 23658099642624), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00061.record008_result⟩)))
 (.branch 10
 (.leaf ⟨(32, 23658327212288), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00061.record009_result⟩)
 (.branch 11
 (.leaf ⟨(32, 23658327277568), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00061.record010_result⟩)
 (.leaf ⟨(32, 23658329293056), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00061.record011_result⟩)))))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf ⟨(32, 23658329358336), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00061.record012_result⟩)
 (.branch 14
 (.leaf ⟨(32, 23658336624704), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00061.record013_result⟩)
 (.leaf ⟨(32, 23658370175040), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00061.record014_result⟩)))
 (.branch 16
 (.leaf ⟨(32, 23659511025680), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00061.record015_result⟩)
 (.branch 17
 (.leaf ⟨(32, 23678448894208), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00061.record016_result⟩)
 (.leaf ⟨(32, 23678717296896), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00061.record017_result⟩))))
 (.branch 21
 (.branch 19
 (.leaf ⟨(32, 23678717362176), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00061.record018_result⟩)
 (.branch 20
 (.leaf ⟨(32, 23678720938240), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00061.record019_result⟩)
 (.leaf ⟨(32, 23679505465600), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00061.record020_result⟩)))
 (.branch 23
 (.branch 22
 (.leaf ⟨(32, 23679773868288), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00061.record021_result⟩)
 (.leaf ⟨(32, 23679773933568), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00061.record022_result⟩))
 (.branch 24
 (.leaf ⟨(32, 23679903793408), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00061.record023_result⟩)
 (.leaf ⟨(32, 23683012247808), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00061.record024_result⟩))))))
 (.branch 37
 (.branch 31
 (.branch 28
 (.branch 26
 (.leaf ⟨(32, 23683012313088), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00061.record025_result⟩)
 (.branch 27
 (.leaf ⟨(32, 23683013808384), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00061.record026_result⟩)
 (.leaf ⟨(32, 23691597988096), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00061.record027_result⟩)))
 (.branch 29
 (.leaf ⟨(32, 23691598053376), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00061.record028_result⟩)
 (.branch 30
 (.leaf ⟨(32, 23691599548672), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00061.record029_result⟩)
 (.leaf ⟨(32, 23691602214912), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00061.record030_result⟩))))
 (.branch 34
 (.branch 32
 (.leaf ⟨(32, 23691605839936), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00061.record031_result⟩)
 (.branch 33
 (.leaf ⟨(32, 23691723278352), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00061.record032_result⟩)
 (.leaf ⟨(32, 23692797018113), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00061.record033_result⟩)))
 (.branch 35
 (.leaf ⟨(32, 23696006217984), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00061.record034_result⟩)
 (.branch 36
 (.leaf ⟨(32, 23714196422912), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00061.record035_result⟩)
 (.leaf ⟨(32, 23726678671616), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00061.record036_result⟩)))))
 (.branch 43
 (.branch 40
 (.branch 38
 (.leaf ⟨(32, 23727145255168), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00061.record037_result⟩)
 (.branch 39
 (.leaf ⟨(32, 23728218472704), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00061.record038_result⟩)
 (.leaf ⟨(32, 23749298553088), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00061.record039_result⟩)))
 (.branch 41
 (.leaf ⟨(32, 23762581913600), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00061.record040_result⟩)
 (.branch 42
 (.leaf ⟨(32, 23779650572544), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00061.record041_result⟩)
 (.leaf ⟨(32, 23794675618048), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00061.record042_result⟩))))
 (.branch 46
 (.branch 44
 (.leaf ⟨(32, 23794681389120), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00061.record043_result⟩)
 (.branch 45
 (.leaf ⟨(32, 23794681405440), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00061.record044_result⟩)
 (.leaf ⟨(32, 23794681909312), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00061.record045_result⟩)))
 (.branch 48
 (.branch 47
 (.leaf ⟨(32, 23794733287440), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00061.record046_result⟩)
 (.leaf ⟨(32, 23795764052224), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00061.record047_result⟩))
 (.branch 49
 (.leaf ⟨(32, 23795807027201), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00061.record048_result⟩)
 (.leaf ⟨(32, 23880572141824), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00061.record049_result⟩)))))))
 (.branch 75
 (.branch 62
 (.branch 56
 (.branch 53
 (.branch 51
 (.leaf ⟨(32, 23880580530176), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00061.record050_result⟩)
 (.branch 52
 (.leaf ⟨(32, 23897735039232), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00061.record051_result⟩)
 (.leaf ⟨(32, 23897743427584), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00061.record052_result⟩)))
 (.branch 54
 (.leaf ⟨(32, 23897751683840), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00061.record053_result⟩)
 (.branch 55
 (.leaf ⟨(32, 23916688969984), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00061.record054_result⟩)
 (.leaf ⟨(32, 23916821090560), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00061.record055_result⟩))))
 (.branch 59
 (.branch 57
 (.leaf ⟨(32, 23917085331712), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00061.record056_result⟩)
 (.branch 58
 (.leaf ⟨(32, 23917091622976), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00061.record057_result⟩)
 (.leaf ⟨(32, 23921492001024), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00061.record058_result⟩)))
 (.branch 60
 (.leaf ⟨(32, 23923524636928), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00061.record059_result⟩)
 (.branch 61
 (.leaf ⟨(32, 23923530928192), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00061.record060_result⟩)
 (.leaf ⟨(32, 23924613071104), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00061.record061_result⟩)))))
 (.branch 68
 (.branch 65
 (.branch 63
 (.leaf ⟨(32, 23931771684880), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00061.record062_result⟩)
 (.branch 64
 (.leaf ⟨(32, 23931903805456), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00061.record063_result⟩)
 (.leaf ⟨(32, 23932116668480), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00061.record064_result⟩)))
 (.branch 66
 (.leaf ⟨(32, 23932845424641), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00061.record065_result⟩)
 (.branch 67
 (.leaf ⟨(32, 23932977545217), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00061.record066_result⟩)
 (.leaf ⟨(32, 23941792940032), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00061.record067_result⟩))))
 (.branch 71
 (.branch 69
 (.leaf ⟨(32, 23971286384896), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00061.record068_result⟩)
 (.branch 70
 (.leaf ⟨(32, 23971554852864), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00061.record069_result⟩)
 (.leaf ⟨(32, 23971563175936), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00061.record070_result⟩)))
 (.branch 73
 (.branch 72
 (.leaf ⟨(32, 23972091527680), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00061.record071_result⟩)
 (.leaf ⟨(32, 23986993954816), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00061.record072_result⟩))
 (.branch 74
 (.leaf ⟨(32, 23988537458944), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00061.record073_result⟩)
 (.leaf ⟨(32, 23989074329600), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00061.record074_result⟩))))))
 (.branch 87
 (.branch 81
 (.branch 78
 (.branch 76
 (.leaf ⟨(32, 23990114516992), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00061.record075_result⟩)
 (.branch 77
 (.leaf ⟨(32, 24004606853376), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00061.record076_result⟩)
 (.leaf ⟨(32, 24005717327872), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00061.record077_result⟩)))
 (.branch 79
 (.leaf ⟨(32, 24005989892096), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00061.record078_result⟩)
 (.branch 80
 (.leaf ⟨(32, 24006452314112), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00061.record079_result⟩)
 (.leaf ⟨(32, 24017742659840), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00061.record080_result⟩))))
 (.branch 84
 (.branch 82
 (.leaf ⟨(32, 24017751048192), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00061.record081_result⟩)
 (.branch 83
 (.leaf ⟨(32, 24018011062528), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00061.record082_result⟩)
 (.leaf ⟨(32, 24018023352320), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00061.record083_result⟩)))
 (.branch 85
 (.leaf ⟨(32, 24018262690048), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00061.record084_result⟩)
 (.branch 86
 (.leaf ⟨(32, 24021773123840), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00061.record085_result⟩)
 (.leaf ⟨(32, 24022309994496), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00061.record086_result⟩)))))
 (.branch 93
 (.branch 90
 (.branch 88
 (.leaf ⟨(32, 24024176459776), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00061.record087_result⟩)
 (.branch 89
 (.leaf ⟨(32, 24026584058112), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00061.record088_result⟩)
 (.leaf ⟨(32, 24026592446464), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00061.record089_result⟩)))
 (.branch 91
 (.leaf ⟨(32, 24026600702720), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00061.record090_result⟩)
 (.branch 92
 (.leaf ⟨(32, 24034913945600), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00061.record091_result⟩)
 (.leaf ⟨(32, 24035442295304), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00061.record092_result⟩))))
 (.branch 96
 (.branch 94
 (.leaf ⟨(32, 24038932119808), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00061.record093_result⟩)
 (.branch 95
 (.leaf ⟨(32, 24041356263424), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00061.record094_result⟩)
 (.leaf ⟨(32, 24041884745728), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00061.record095_result⟩)))
 (.branch 98
 (.branch 97
 (.leaf ⟨(32, 24052976648448), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00061.record096_result⟩)
 (.leaf ⟨(32, 24052985036800), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00061.record097_result⟩))
 (.branch 99
 (.leaf ⟨(32, 24053092253952), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00061.record098_result⟩)
 (.leaf ⟨(32, 24053445312768), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00061.record099_result⟩))))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (32820 + i))) 0 100 :=
  interval_of_check _ 0 100 (by decide +kernel)

public theorem complete : Block 32820 32920 :=
  block_of_table results 32820 100 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock1026
