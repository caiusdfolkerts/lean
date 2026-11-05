module
prelude
import GraphInputsSix0Part00050Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock1015
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 50
 (.branch 25
 (.branch 12
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(32, 19564259704833), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00050.record000_result⟩)
 (.branch 2
 (.leaf ⟨(32, 19573374091520), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00050.record001_result⟩)
 (.leaf ⟨(32, 19573382479872), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00050.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(32, 19573910798976), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00050.record003_result⟩)
 (.branch 5
 (.leaf ⟨(32, 19586194046984), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00050.record004_result⟩)
 (.leaf ⟨(32, 19586219016448), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00050.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(32, 19586681438464), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00050.record006_result⟩)
 (.branch 8
 (.leaf ⟨(32, 19586739079296), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00050.record007_result⟩)
 (.leaf ⟨(32, 19587358294272), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00050.record008_result⟩)))
 (.branch 10
 (.leaf ⟨(32, 19587754656000), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00050.record009_result⟩)
 (.branch 11
 (.leaf ⟨(32, 19587779266688), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00050.record010_result⟩)
 (.leaf ⟨(32, 19588679008512), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00050.record011_result⟩)))))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf ⟨(32, 19588687396864), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00050.record012_result⟩)
 (.branch 14
 (.leaf ⟨(32, 19589079531776), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00050.record013_result⟩)
 (.leaf ⟨(32, 19589090000896), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00050.record014_result⟩)))
 (.branch 16
 (.leaf ⟨(32, 19590759383296), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00050.record015_result⟩)
 (.branch 17
 (.leaf ⟨(32, 19590767771648), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00050.record016_result⟩)
 (.leaf ⟨(32, 19595052253440), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00050.record017_result⟩))))
 (.branch 21
 (.branch 19
 (.leaf ⟨(32, 19595060641792), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00050.record018_result⟩)
 (.branch 20
 (.leaf ⟨(32, 19595320656128), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00050.record019_result⟩)
 (.leaf ⟨(32, 19595324882944), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00050.record020_result⟩)))
 (.branch 23
 (.branch 22
 (.leaf ⟨(32, 19595331125248), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00050.record021_result⟩)
 (.leaf ⟨(32, 19595520917760), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00050.record022_result⟩))
 (.branch 24
 (.leaf ⟨(32, 19596360843520), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00050.record023_result⟩)
 (.leaf ⟨(32, 19596365070336), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00050.record024_result⟩))))))
 (.branch 37
 (.branch 31
 (.branch 28
 (.branch 26
 (.leaf ⟨(32, 19602341890176), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00050.record025_result⟩)
 (.branch 27
 (.leaf ⟨(32, 19602440980608), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00050.record026_result⟩)
 (.leaf ⟨(32, 19611626512448), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00050.record027_result⟩)))
 (.branch 29
 (.leaf ⟨(32, 19611963654400), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00050.record028_result⟩)
 (.branch 30
 (.leaf ⟨(32, 19612100001792), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00050.record029_result⟩)
 (.leaf ⟨(32, 19612108324864), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00050.record030_result⟩))))
 (.branch 34
 (.branch 32
 (.leaf ⟨(32, 19612232122368), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00050.record031_result⟩)
 (.branch 33
 (.leaf ⟨(32, 19612240445440), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00050.record032_result⟩)
 (.leaf ⟨(32, 19612504686592), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00050.record033_result⟩)))
 (.branch 35
 (.leaf ⟨(32, 19612700786688), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00050.record034_result⟩)
 (.branch 36
 (.leaf ⟨(32, 19612768927744), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00050.record035_result⟩)
 (.leaf ⟨(32, 19619429711880), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00050.record036_result⟩)))))
 (.branch 43
 (.branch 40
 (.branch 38
 (.leaf ⟨(32, 19619570286848), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00050.record037_result⟩)
 (.branch 39
 (.leaf ⟨(32, 19619974744192), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00050.record038_result⟩)
 (.leaf ⟨(32, 19623709967368), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00050.record039_result⟩)))
 (.branch 41
 (.leaf ⟨(32, 19623995048192), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00050.record040_result⟩)
 (.branch 42
 (.leaf ⟨(32, 19624003436544), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00050.record041_result⟩)
 (.leaf ⟨(32, 19624250968192), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00050.record042_result⟩))))
 (.branch 46
 (.branch 44
 (.leaf ⟨(32, 19624511176960), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00050.record043_result⟩)
 (.branch 45
 (.leaf ⟨(32, 19624523466752), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00050.record044_result⟩)
 (.leaf ⟨(32, 19628287918336), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00050.record045_result⟩)))
 (.branch 48
 (.branch 47
 (.leaf ⟨(32, 19628296306688), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00050.record046_result⟩)
 (.leaf ⟨(32, 19628403523840), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00050.record047_result⟩))
 (.branch 49
 (.leaf ⟨(32, 19628556321024), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00050.record048_result⟩)
 (.leaf ⟨(32, 19628560547840), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00050.record049_result⟩)))))))
 (.branch 75
 (.branch 62
 (.branch 56
 (.branch 53
 (.branch 51
 (.leaf ⟨(32, 19628566790144), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00050.record050_result⟩)
 (.branch 52
 (.leaf ⟨(32, 19628671926528), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00050.record051_result⟩)
 (.leaf ⟨(32, 19628684216320), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00050.record052_result⟩)))
 (.branch 54
 (.leaf ⟨(32, 19628806127872), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00050.record053_result⟩)
 (.branch 55
 (.leaf ⟨(32, 19632970858496), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00050.record054_result⟩)
 (.leaf ⟨(32, 19633100817152), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00050.record055_result⟩))))
 (.branch 59
 (.branch 57
 (.leaf ⟨(32, 19636733216896), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00050.record056_result⟩)
 (.branch 58
 (.leaf ⟨(32, 19645985718848), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00050.record057_result⟩)
 (.leaf ⟨(32, 19646004592640), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00050.record058_result⟩)))
 (.branch 60
 (.leaf ⟨(32, 19649475543296), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00050.record059_result⟩)
 (.branch 61
 (.leaf ⟨(32, 19649744011264), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00050.record060_result⟩)
 (.leaf ⟨(32, 19649752334336), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00050.record061_result⟩)))))
 (.branch 68
 (.branch 65
 (.branch 63
 (.leaf ⟨(32, 19650280686080), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00050.record062_result⟩)
 (.branch 64
 (.leaf ⟨(32, 19657396388096), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00050.record063_result⟩)
 (.leaf ⟨(32, 19657404776448), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00050.record064_result⟩)))
 (.branch 66
 (.leaf ⟨(32, 19657664790784), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00050.record065_result⟩)
 (.branch 67
 (.leaf ⟨(32, 19657675259904), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00050.record066_result⟩)
 (.leaf ⟨(32, 19657798992128), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00050.record067_result⟩))))
 (.branch 71
 (.branch 69
 (.leaf ⟨(32, 19659344642304), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00050.record068_result⟩)
 (.branch 70
 (.leaf ⟨(32, 19659353030656), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00050.record069_result⟩)
 (.leaf ⟨(32, 19659476762880), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00050.record070_result⟩)))
 (.branch 73
 (.branch 72
 (.leaf ⟨(32, 19659485151232), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00050.record071_result⟩)
 (.leaf ⟨(32, 19659745165568), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00050.record072_result⟩))
 (.branch 74
 (.leaf ⟨(32, 19659749392384), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00050.record073_result⟩)
 (.leaf ⟨(32, 19659755634688), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00050.record074_result⟩))))))
 (.branch 87
 (.branch 81
 (.branch 78
 (.branch 76
 (.leaf ⟨(32, 19659945427200), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00050.record075_result⟩)
 (.branch 77
 (.leaf ⟨(32, 19660516950272), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00050.record076_result⟩)
 (.leaf ⟨(32, 19660525338624), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00050.record077_result⟩)))
 (.branch 79
 (.leaf ⟨(32, 19660785352960), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00050.record078_result⟩)
 (.branch 80
 (.leaf ⟨(32, 19660789579776), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00050.record079_result⟩)
 (.leaf ⟨(32, 19660795822080), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00050.record080_result⟩))))
 (.branch 84
 (.branch 82
 (.leaf ⟨(32, 19664040116480), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00050.record081_result⟩)
 (.branch 83
 (.leaf ⟨(32, 19664048504832), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00050.record082_result⟩)
 (.leaf ⟨(32, 19664106176768), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00050.record083_result⟩)))
 (.branch 85
 (.leaf ⟨(32, 19672361615616), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00050.record084_result⟩)
 (.branch 86
 (.leaf ⟨(32, 19672370003968), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00050.record085_result⟩)
 (.leaf ⟨(32, 19672427675904), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00050.record086_result⟩)))))
 (.branch 93
 (.branch 90
 (.branch 88
 (.leaf ⟨(32, 19672634245120), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00050.record087_result⟩)
 (.branch 89
 (.leaf ⟨(32, 19672830328896), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00050.record088_result⟩)
 (.leaf ⟨(32, 19676051021888), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00050.record089_result⟩)))
 (.branch 91
 (.leaf ⟨(32, 19680683114752), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00050.record090_result⟩)
 (.branch 92
 (.leaf ⟨(32, 19680817381376), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00050.record091_result⟩)
 (.leaf ⟨(32, 19680825704448), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00050.record092_result⟩))))
 (.branch 96
 (.branch 94
 (.leaf ⟨(32, 19681219985408), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00050.record093_result⟩)
 (.branch 95
 (.leaf ⟨(32, 19681286045696), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00050.record094_result⟩)
 (.leaf ⟨(32, 19683869737216), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00050.record095_result⟩)))
 (.branch 98
 (.branch 97
 (.leaf ⟨(32, 19683937943552), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00050.record096_result⟩)
 (.leaf ⟨(32, 19683946266624), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00050.record097_result⟩))
 (.branch 99
 (.leaf ⟨(32, 19684012326912), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00050.record098_result⟩)
 (.leaf ⟨(32, 19684045357056), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00050.record099_result⟩))))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (31750 + i))) 0 100 :=
  interval_of_check _ 0 100 (by decide +kernel)

public theorem complete : Block 31750 31850 :=
  block_of_table results 31750 100 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock1015
