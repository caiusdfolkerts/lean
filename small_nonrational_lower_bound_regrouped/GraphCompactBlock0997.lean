module
prelude
import GraphInputsSix0Part00032Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0997
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 50
 (.branch 25
 (.branch 12
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(32, 12138137600016), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00032.record000_result⟩)
 (.branch 2
 (.leaf ⟨(32, 12139060330752), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00032.record001_result⟩)
 (.leaf ⟨(32, 12139066573056), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00032.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(32, 12142287786240), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00032.record003_result⟩)
 (.branch 5
 (.leaf ⟨(32, 12146727501840), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00032.record004_result⟩)
 (.leaf ⟨(32, 12165654872192), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00032.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(32, 12165658542096), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00032.record006_result⟩)
 (.branch 8
 (.leaf ⟨(32, 12165789040896), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00032.record007_result⟩)
 (.leaf ⟨(32, 12165789073536), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00032.record008_result⟩)))
 (.branch 10
 (.leaf ⟨(32, 12165790662672), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00032.record009_result⟩)
 (.branch 11
 (.leaf ⟨(32, 12166054903824), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00032.record010_result⟩)
 (.leaf ⟨(32, 12167932354816), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00032.record011_result⟩)))))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf ⟨(32, 12167936516352), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00032.record012_result⟩)
 (.branch 14
 (.leaf ⟨(32, 12167936548992), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00032.record013_result⟩)
 (.leaf ⟨(32, 12167937097744), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00032.record014_result⟩)))
 (.branch 16
 (.leaf ⟨(32, 12168201338896), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00032.record015_result⟩)
 (.branch 17
 (.leaf ⟨(32, 12168204951680), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00032.record016_result⟩)
 (.leaf ⟨(32, 12168988926208), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00032.record017_result⟩))))
 (.branch 21
 (.branch 19
 (.leaf ⟨(32, 12169261523072), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00032.record018_result⟩)
 (.branch 20
 (.leaf ⟨(32, 12172231467264), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00032.record019_result⟩)
 (.leaf ⟨(32, 12172232048656), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00032.record020_result⟩)))
 (.branch 23
 (.branch 22
 (.leaf ⟨(32, 12172494209040), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00032.record021_result⟩)
 (.leaf ⟨(32, 12172496289808), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00032.record022_result⟩))
 (.branch 24
 (.leaf ⟨(32, 12172497330192), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00032.record023_result⟩)
 (.leaf ⟨(32, 12172499902592), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00032.record024_result⟩))))))
 (.branch 37
 (.branch 31
 (.branch 28
 (.branch 26
 (.leaf ⟨(32, 12173352960256), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00032.record025_result⟩)
 (.branch 27
 (.leaf ⟨(32, 12173359202560), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00032.record026_result⟩)
 (.leaf ⟨(32, 12173556473984), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00032.record027_result⟩)))
 (.branch 29
 (.leaf ⟨(32, 12174500040960), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00032.record028_result⟩)
 (.branch 30
 (.leaf ⟨(32, 12181086191632), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00032.record029_result⟩)
 (.leaf ⟨(32, 12190762418304), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00032.record030_result⟩))))
 (.branch 34
 (.branch 32
 (.leaf ⟨(32, 12210998935808), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00032.record031_result⟩)
 (.branch 33
 (.leaf ⟨(32, 12211007324160), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00032.record032_result⟩)
 (.leaf ⟨(32, 12234374299904), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00032.record033_result⟩)))
 (.branch 35
 (.leaf ⟨(32, 12234374332544), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00032.record034_result⟩)
 (.branch 36
 (.leaf ⟨(32, 12234375921680), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00032.record035_result⟩)
 (.leaf ⟨(32, 12234510123024), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00032.record036_result⟩)))))
 (.branch 43
 (.branch 40
 (.branch 38
 (.leaf ⟨(32, 12234774364176), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00032.record037_result⟩)
 (.branch 39
 (.leaf ⟨(32, 12236521775360), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00032.record038_result⟩)
 (.leaf ⟨(32, 12236521808000), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00032.record039_result⟩)))
 (.branch 41
 (.leaf ⟨(32, 12236522356752), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00032.record040_result⟩)
 (.branch 42
 (.leaf ⟨(32, 12236655976704), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00032.record041_result⟩)
 (.leaf ⟨(32, 12236656558096), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00032.record042_result⟩))))
 (.branch 46
 (.branch 44
 (.leaf ⟨(32, 12236918718480), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00032.record043_result⟩)
 (.branch 45
 (.leaf ⟨(32, 12236920799248), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00032.record044_result⟩)
 (.leaf ⟨(32, 12236921839632), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00032.record045_result⟩)))
 (.branch 48
 (.branch 47
 (.leaf ⟨(32, 12238924550400), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00032.record046_result⟩)
 (.leaf ⟨(32, 12241213669392), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00032.record047_result⟩))
 (.branch 49
 (.leaf ⟨(32, 12241938219264), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00032.record048_result⟩)
 (.leaf ⟨(32, 12241944461568), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00032.record049_result⟩)))))))
 (.branch 75
 (.branch 62
 (.branch 56
 (.branch 53
 (.branch 51
 (.leaf ⟨(32, 12242076582144), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00032.record050_result⟩)
 (.branch 52
 (.leaf ⟨(32, 12242340823296), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00032.record051_result⟩)
 (.leaf ⟨(32, 12243217420544), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00032.record052_result⟩)))
 (.branch 54
 (.leaf ⟨(32, 12249803571216), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00032.record053_result⟩)
 (.branch 55
 (.leaf ⟨(32, 12250662322432), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00032.record054_result⟩)
 (.leaf ⟨(32, 12251803160832), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00032.record055_result⟩))))
 (.branch 59
 (.branch 57
 (.leaf ⟨(32, 12255186927744), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00032.record056_result⟩)
 (.branch 58
 (.leaf ⟨(32, 12279724703744), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00032.record057_result⟩)
 (.leaf ⟨(32, 12311256383744), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00032.record058_result⟩)))
 (.branch 60
 (.leaf ⟨(32, 12314075005184), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00032.record059_result⟩)
 (.branch 61
 (.leaf ⟨(32, 12327967588352), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00032.record060_result⟩)
 (.leaf ⟨(32, 12371810680848), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00032.record061_result⟩)))))
 (.branch 68
 (.branch 65
 (.branch 63
 (.leaf ⟨(32, 12371944882192), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00032.record062_result⟩)
 (.branch 64
 (.leaf ⟨(32, 12372213284880), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00032.record063_result⟩)
 (.leaf ⟨(32, 12373957115920), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00032.record064_result⟩)))
 (.branch 66
 (.leaf ⟨(32, 12374089236496), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00032.record065_result⟩)
 (.branch 67
 (.leaf ⟨(32, 12374091317264), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00032.record066_result⟩)
 (.leaf ⟨(32, 12374092357648), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00032.record067_result⟩))))
 (.branch 71
 (.branch 69
 (.leaf ⟨(32, 12374359719952), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00032.record068_result⟩)
 (.branch 70
 (.leaf ⟨(32, 12378384187408), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00032.record069_result⟩)
 (.leaf ⟨(32, 12378652590096), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00032.record070_result⟩)))
 (.branch 73
 (.branch 72
 (.leaf ⟨(32, 12380652179712), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00032.record071_result⟩)
 (.leaf ⟨(32, 12384035946624), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00032.record072_result⟩))
 (.branch 74
 (.leaf ⟨(32, 12392357445760), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00032.record073_result⟩)
 (.leaf ⟨(32, 12417159462912), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00032.record074_result⟩))))))
 (.branch 87
 (.branch 81
 (.branch 78
 (.branch 76
 (.leaf ⟨(32, 12439512942720), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00032.record075_result⟩)
 (.branch 77
 (.leaf ⟨(32, 12439587422464), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00032.record076_result⟩)
 (.leaf ⟨(32, 12439587487744), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00032.record077_result⟩)))
 (.branch 79
 (.leaf ⟨(32, 12439589568512), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00032.record078_result⟩)
 (.branch 80
 (.leaf ⟨(32, 12439593697408), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00032.record079_result⟩)
 (.leaf ⟨(32, 12439640869120), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00032.record080_result⟩))))
 (.branch 84
 (.branch 82
 (.leaf ⟨(32, 12439645063296), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00032.record081_result⟩)
 (.branch 83
 (.leaf ⟨(32, 12439855857792), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00032.record082_result⟩)
 (.leaf ⟨(32, 12439857938560), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00032.record083_result⟩)))
 (.branch 85
 (.leaf ⟨(32, 12439857971200), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00032.record084_result⟩)
 (.branch 86
 (.leaf ⟨(32, 12464046489728), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00032.record085_result⟩)
 (.leaf ⟨(32, 12465136091264), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00032.record086_result⟩)))))
 (.branch 93
 (.branch 90
 (.branch 88
 (.leaf ⟨(32, 12465138204672), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00032.record087_result⟩)
 (.branch 89
 (.leaf ⟨(32, 12465142236160), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00032.record088_result⟩)
 (.leaf ⟨(32, 12465270162048), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00032.record089_result⟩)))
 (.branch 91
 (.leaf ⟨(32, 12465340417024), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00032.record090_result⟩)
 (.branch 92
 (.leaf ⟨(32, 12508172681472), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00032.record091_result⟩)
 (.leaf ⟨(32, 12508230322304), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00032.record092_result⟩))))
 (.branch 96
 (.branch 94
 (.leaf ⟨(32, 12510575001600), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00032.record093_result⟩)
 (.branch 95
 (.leaf ⟨(32, 12511350884480), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00032.record094_result⟩)
 (.leaf ⟨(32, 12511392334080), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00032.record095_result⟩)))
 (.branch 98
 (.branch 97
 (.leaf ⟨(32, 12511416944768), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00032.record096_result⟩)
 (.leaf ⟨(32, 12512655376384), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00032.record097_result⟩))
 (.branch 99
 (.leaf ⟨(32, 12516946100480), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00032.record098_result⟩)
 (.leaf ⟨(32, 12517012160768), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00032.record099_result⟩))))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (29986 + i))) 0 100 :=
  interval_of_check _ 0 100 (by decide +kernel)

public theorem complete : Block 29986 30086 :=
  block_of_table results 29986 100 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0997
