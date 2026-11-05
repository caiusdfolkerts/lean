module
prelude
import GraphInputsRow23Part00005Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0083
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 50
 (.branch 25
 (.branch 12
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(23, 9529597165824), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00005.record000_result⟩)
 (.branch 2
 (.leaf ⟨(23, 9529869795328), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00005.record001_result⟩)
 (.leaf ⟨(23, 9530134036480), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00005.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(23, 9530142359552), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00005.record003_result⟩)
 (.branch 5
 (.leaf ⟨(23, 9531350384640), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00005.record004_result⟩)
 (.leaf ⟨(23, 9535387435008), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00005.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(23, 9537782317312), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00005.record006_result⟩)
 (.branch 8
 (.leaf ⟨(23, 9634429538336), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00005.record007_result⟩)
 (.leaf ⟨(23, 9675221270656), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00005.record008_result⟩)))
 (.branch 10
 (.leaf ⟨(23, 9794964488192), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00005.record009_result⟩)
 (.branch 11
 (.leaf ⟨(23, 9803401330944), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00005.record010_result⟩)
 (.leaf ⟨(23, 9811991232768), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00005.record011_result⟩)))))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf ⟨(23, 9812660224000), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00005.record012_result⟩)
 (.branch 14
 (.leaf ⟨(23, 9820581199872), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00005.record013_result⟩)
 (.leaf ⟨(23, 9820853764096), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00005.record014_result⟩)))
 (.branch 16
 (.leaf ⟨(23, 9821118005248), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00005.record015_result⟩)
 (.branch 17
 (.leaf ⟨(23, 9936822079744), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00005.record016_result⟩)
 (.leaf ⟨(23, 9970309496832), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00005.record017_result⟩))))
 (.branch 21
 (.branch 19
 (.leaf ⟨(23, 9974602366976), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00005.record018_result⟩)
 (.branch 20
 (.leaf ⟨(23, 10072977637632), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00005.record019_result⟩)
 (.leaf ⟨(23, 10090165829632), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00005.record020_result⟩)))
 (.branch 23
 (.branch 22
 (.leaf ⟨(23, 10138826080512), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00005.record021_result⟩)
 (.leaf ⟨(23, 10138830307328), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00005.record022_result⟩))
 (.branch 24
 (.leaf ⟨(23, 10138953975808), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00005.record023_result⟩)
 (.leaf ⟨(23, 10208472530944), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00005.record024_result⟩))))))
 (.branch 37
 (.branch 31
 (.branch 28
 (.branch 26
 (.leaf ⟨(23, 10210552905728), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00005.record025_result⟩)
 (.branch 27
 (.leaf ⟨(23, 10214713655296), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00005.record026_result⟩)
 (.leaf ⟨(23, 10276000825344), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00005.record027_result⟩)))
 (.branch 29
 (.leaf ⟨(23, 10293696561152), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00005.record028_result⟩)
 (.branch 30
 (.leaf ⟨(23, 10301617537024), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00005.record029_result⟩)
 (.leaf ⟨(23, 10301890101248), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00005.record030_result⟩))))
 (.branch 34
 (.branch 32
 (.leaf ⟨(23, 10302154342400), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00005.record031_result⟩)
 (.branch 33
 (.leaf ⟨(23, 10349399048192), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00005.record032_result⟩)
 (.leaf ⟨(23, 10396574449664), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00005.record033_result⟩)))
 (.branch 35
 (.leaf ⟨(23, 10448894263296), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00005.record034_result⟩)
 (.branch 36
 (.leaf ⟨(23, 10448996929792), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00005.record035_result⟩)
 (.leaf ⟨(23, 10484309393408), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00005.record036_result⟩)))))
 (.branch 43
 (.branch 40
 (.branch 38
 (.leaf ⟨(23, 10484312969472), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00005.record037_result⟩)
 (.branch 39
 (.leaf ⟨(23, 10488868585472), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00005.record038_result⟩)
 (.leaf ⟨(23, 10498781249792), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00005.record039_result⟩)))
 (.branch 41
 (.leaf ⟨(23, 10585506844928), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00005.record040_result⟩)
 (.branch 42
 (.leaf ⟨(23, 10639451881472), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00005.record041_result⟩)
 (.leaf ⟨(23, 10643736428544), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00005.record042_result⟩))))
 (.branch 46
 (.branch 44
 (.leaf ⟨(23, 10722677362944), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00005.record043_result⟩)
 (.branch 45
 (.leaf ⟨(23, 10740371570816), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00005.record044_result⟩)
 (.leaf ⟨(23, 10781580132352), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00005.record045_result⟩)))
 (.branch 48
 (.branch 47
 (.leaf ⟨(23, 10781852696576), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00005.record046_result⟩)
 (.leaf ⟨(23, 10782116937728), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00005.record047_result⟩))
 (.branch 49
 (.leaf ⟨(23, 10858841309184), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00005.record048_result⟩)
 (.leaf ⟨(23, 10859097098240), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00005.record049_result⟩)))))))
 (.branch 75
 (.branch 62
 (.branch 56
 (.branch 53
 (.branch 51
 (.leaf ⟨(23, 10861037027584), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00005.record050_result⟩)
 (.branch 52
 (.leaf ⟨(23, 10876537044992), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00005.record051_result⟩)
 (.leaf ⟨(23, 10892192579584), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00005.record052_result⟩)))
 (.branch 54
 (.leaf ⟨(23, 10892439980288), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00005.record053_result⟩)
 (.branch 55
 (.leaf ⟨(23, 10896600598784), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00005.record054_result⟩)
 (.leaf ⟨(23, 10896889937920), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00005.record055_result⟩))))
 (.branch 59
 (.branch 57
 (.leaf ⟨(23, 10896898260992), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00005.record056_result⟩)
 (.branch 58
 (.leaf ⟨(23, 10897137664000), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00005.record057_result⟩)
 (.leaf ⟨(23, 10901191131136), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00005.record058_result⟩)))
 (.branch 60
 (.leaf ⟨(23, 10901298413568), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00005.record059_result⟩)
 (.branch 61
 (.leaf ⟨(23, 10905735659520), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00005.record060_result⟩)
 (.leaf ⟨(23, 10909235839232), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00005.record061_result⟩)))))
 (.branch 68
 (.branch 65
 (.branch 63
 (.leaf ⟨(23, 10909619912704), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00005.record062_result⟩)
 (.branch 64
 (.leaf ⟨(23, 10909772709888), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00005.record063_result⟩)
 (.leaf ⟨(23, 10909776871424), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00005.record064_result⟩)))
 (.branch 66
 (.leaf ⟨(23, 10909888315392), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00005.record065_result⟩)
 (.branch 67
 (.leaf ⟨(23, 10914317206016), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00005.record066_result⟩)
 (.leaf ⟨(23, 11082504609920), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00005.record067_result⟩))))
 (.branch 71
 (.branch 69
 (.leaf ⟨(23, 11109616615424), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00005.record068_result⟩)
 (.branch 70
 (.leaf ⟨(23, 11238073499648), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00005.record069_result⟩)
 (.leaf ⟨(23, 11242894786560), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00005.record070_result⟩)))
 (.branch 73
 (.branch 72
 (.leaf ⟨(23, 11247055536128), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00005.record071_result⟩)
 (.leaf ⟨(23, 11255769235456), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00005.record072_result⟩))
 (.branch 74
 (.leaf ⟨(23, 11283294326816), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00005.record073_result⟩)
 (.leaf ⟨(23, 11380325384192), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00005.record074_result⟩))))))
 (.branch 87
 (.branch 81
 (.branch 78
 (.branch 76
 (.leaf ⟨(23, 11384226054144), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00005.record075_result⟩)
 (.branch 77
 (.leaf ⟨(23, 11384618254336), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00005.record076_result⟩)
 (.leaf ⟨(23, 11401129132032), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00005.record077_result⟩)))
 (.branch 79
 (.leaf ⟨(23, 11401397534720), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00005.record078_result⟩)
 (.branch 80
 (.leaf ⟨(23, 11448373772544), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00005.record079_result⟩)
 (.leaf ⟨(23, 11448642240512), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00005.record080_result⟩))))
 (.branch 84
 (.branch 82
 (.leaf ⟨(23, 11448650563584), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00005.record081_result⟩)
 (.branch 83
 (.leaf ⟨(23, 11448910643200), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00005.record082_result⟩)
 (.leaf ⟨(23, 11449042763776), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00005.record083_result⟩)))
 (.branch 85
 (.leaf ⟨(23, 11452943433728), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00005.record084_result⟩)
 (.branch 86
 (.leaf ⟨(23, 11453203513344), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00005.record085_result⟩)
 (.leaf ⟨(23, 11454747017472), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00005.record086_result⟩)))))
 (.branch 93
 (.branch 90
 (.branch 88
 (.leaf ⟨(23, 11455089868800), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00005.record087_result⟩)
 (.branch 89
 (.leaf ⟨(23, 11455283888128), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00005.record088_result⟩)
 (.leaf ⟨(23, 11471926886400), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00005.record089_result⟩)))
 (.branch 91
 (.leaf ⟨(23, 11472063168512), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00005.record090_result⟩)
 (.branch 92
 (.leaf ⟨(23, 11487496142848), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00005.record091_result⟩)
 (.leaf ⟨(23, 11585418461184), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00005.record092_result⟩))))
 (.branch 96
 (.branch 94
 (.leaf ⟨(23, 11589310808064), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00005.record093_result⟩)
 (.branch 95
 (.leaf ⟨(23, 11589579210752), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00005.record094_result⟩)
 (.leaf ⟨(23, 11589702942976), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00005.record095_result⟩)))
 (.branch 98
 (.branch 97
 (.leaf ⟨(23, 11592934625280), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00005.record096_result⟩)
 (.leaf ⟨(23, 11597900709888), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00005.record097_result⟩))
 (.branch 99
 (.leaf ⟨(23, 11689571389440), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00005.record098_result⟩)
 (.leaf ⟨(23, 11693732139008), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00005.record099_result⟩))))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (6038 + i))) 0 100 :=
  interval_of_check _ 0 100 (by decide +kernel)

public theorem complete : Block 6038 6138 :=
  block_of_table results 6038 100 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0083
