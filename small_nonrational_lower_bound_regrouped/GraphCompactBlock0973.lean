module
prelude
import GraphInputsSix0Part00008Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0973
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 50
 (.branch 25
 (.branch 12
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(32, 3144476033152), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00008.record000_result⟩)
 (.branch 2
 (.leaf ⟨(32, 3153330208768), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00008.record001_result⟩)
 (.leaf ⟨(32, 3153334370304), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00008.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(32, 3157069562112), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00008.record003_result⟩)
 (.branch 5
 (.leaf ⟨(32, 3157073788928), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00008.record004_result⟩)
 (.leaf ⟨(32, 3157077950464), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00008.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(32, 3157081981952), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00008.record006_result⟩)
 (.branch 8
 (.leaf ⟨(32, 3157337997440), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00008.record007_result⟩)
 (.leaf ⟨(32, 3157606269568), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00008.record008_result⟩)))
 (.branch 10
 (.leaf ⟨(32, 3162259898624), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00008.record009_result⟩)
 (.branch 11
 (.leaf ⟨(32, 3162325958912), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00008.record010_result⟩)
 (.leaf ⟨(32, 3164726165760), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00008.record011_result⟩)))))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf ⟨(32, 3164730327296), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00008.record012_result⟩)
 (.branch 14
 (.leaf ⟨(32, 3164730392576), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00008.record013_result⟩)
 (.leaf ⟨(32, 3164998762624), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00008.record014_result⟩)))
 (.branch 16
 (.leaf ⟨(32, 3165000843392), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00008.record015_result⟩)
 (.branch 17
 (.leaf ⟨(32, 3165546651904), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00008.record016_result⟩)
 (.leaf ⟨(32, 3165677732096), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00008.record017_result⟩))))
 (.branch 21
 (.branch 19
 (.leaf ⟨(32, 3165678772480), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00008.record018_result⟩)
 (.branch 20
 (.leaf ⟨(32, 3166678581504), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00008.record019_result⟩)
 (.leaf ⟨(32, 3166678646784), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00008.record020_result⟩)))
 (.branch 23
 (.branch 22
 (.leaf ⟨(32, 3166806540544), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00008.record021_result⟩)
 (.leaf ⟨(32, 3166810702080), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00008.record022_result⟩))
 (.branch 24
 (.leaf ⟨(32, 3166810767360), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00008.record023_result⟩)
 (.leaf ⟨(32, 3166876762368), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00008.record024_result⟩))))))
 (.branch 37
 (.branch 31
 (.branch 28
 (.branch 26
 (.leaf ⟨(32, 3166876827648), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00008.record025_result⟩)
 (.branch 27
 (.leaf ⟨(32, 3167079137408), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00008.record026_result⟩)
 (.leaf ⟨(32, 3167081218176), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00008.record027_result⟩)))
 (.branch 29
 (.leaf ⟨(32, 3167850889472), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00008.record028_result⟩)
 (.branch 30
 (.leaf ⟨(32, 3167850954752), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00008.record029_result⟩)
 (.leaf ⟨(32, 3174392471552), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00008.record030_result⟩))))
 (.branch 34
 (.branch 32
 (.leaf ⟨(32, 3174560710784), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00008.record031_result⟩)
 (.branch 33
 (.leaf ⟨(32, 3188151320576), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00008.record032_result⟩)
 (.leaf ⟨(32, 3191263494400), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00008.record033_result⟩)))
 (.branch 35
 (.leaf ⟨(32, 3191267721216), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00008.record034_result⟩)
 (.branch 36
 (.leaf ⟨(32, 3191271882752), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00008.record035_result⟩)
 (.leaf ⟨(32, 3191333781504), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00008.record036_result⟩)))))
 (.branch 43
 (.branch 40
 (.branch 38
 (.leaf ⟨(32, 3191337943040), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00008.record037_result⟩)
 (.branch 39
 (.leaf ⟨(32, 3191732191360), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00008.record038_result⟩)
 (.leaf ⟨(32, 3195611169024), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00008.record039_result⟩)))
 (.branch 41
 (.leaf ⟨(32, 3199889213696), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00008.record040_result⟩)
 (.branch 42
 (.leaf ⟨(32, 3199905858304), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00008.record041_result⟩)
 (.leaf ⟨(32, 3199914246400), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00008.record042_result⟩))))
 (.branch 46
 (.branch 44
 (.leaf ⟨(32, 3199914311680), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00008.record043_result⟩)
 (.branch 45
 (.leaf ⟨(32, 3200042205440), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00008.record044_result⟩)
 (.leaf ⟨(32, 3200046366976), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00008.record045_result⟩)))
 (.branch 48
 (.branch 47
 (.leaf ⟨(32, 3200046432256), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00008.record046_result⟩)
 (.leaf ⟨(32, 3200165873920), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00008.record047_result⟩))
 (.branch 49
 (.leaf ⟨(32, 3200310608128), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00008.record048_result⟩)
 (.leaf ⟨(32, 3200310673408), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00008.record049_result⟩)))))))
 (.branch 75
 (.branch 62
 (.branch 56
 (.branch 53
 (.branch 51
 (.leaf ⟨(32, 3200314802304), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00008.record050_result⟩)
 (.branch 52
 (.leaf ⟨(32, 3200316883072), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00008.record051_result⟩)
 (.leaf ⟨(32, 3200434309248), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00008.record052_result⟩)))
 (.branch 54
 (.leaf ⟨(32, 3204727179392), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00008.record053_result⟩)
 (.branch 55
 (.leaf ⟨(32, 3208747483392), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00008.record054_result⟩)
 (.leaf ⟨(32, 3208755871744), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00008.record055_result⟩))))
 (.branch 59
 (.branch 57
 (.leaf ⟨(32, 3209024241665), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00008.record056_result⟩)
 (.branch 58
 (.leaf ⟨(32, 3213044484352), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00008.record057_result⟩)
 (.leaf ⟨(32, 3213048678528), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00008.record058_result⟩)))
 (.branch 60
 (.leaf ⟨(32, 3213195493504), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00008.record059_result⟩)
 (.branch 61
 (.leaf ⟨(32, 3213195526144), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00008.record060_result⟩)
 (.leaf ⟨(32, 3225654821120), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00008.record061_result⟩)))))
 (.branch 68
 (.branch 65
 (.branch 63
 (.leaf ⟨(32, 3225659047936), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00008.record062_result⟩)
 (.branch 64
 (.leaf ⟨(32, 3225663209472), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00008.record063_result⟩)
 (.leaf ⟨(32, 3225667240960), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00008.record064_result⟩)))
 (.branch 66
 (.leaf ⟨(32, 3225923093248), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00008.record065_result⟩)
 (.branch 67
 (.leaf ⟨(32, 3226057457792), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00008.record066_result⟩)
 (.leaf ⟨(32, 3226063602688), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00008.record067_result⟩))))
 (.branch 71
 (.branch 69
 (.leaf ⟨(32, 3226191528576), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00008.record068_result⟩)
 (.branch 70
 (.leaf ⟨(32, 3226459963904), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00008.record069_result⟩)
 (.leaf ⟨(32, 3229903798528), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00008.record070_result⟩)))
 (.branch 73
 (.branch 72
 (.leaf ⟨(32, 3230105100544), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00008.record071_result⟩)
 (.leaf ⟨(32, 3232101468416), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00008.record072_result⟩))
 (.branch 74
 (.leaf ⟨(32, 3232118113024), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00008.record073_result⟩)
 (.leaf ⟨(32, 3232126501120), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00008.record074_result⟩))))))
 (.branch 87
 (.branch 81
 (.branch 78
 (.branch 76
 (.leaf ⟨(32, 3232126566400), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00008.record075_result⟩)
 (.branch 77
 (.leaf ⟨(32, 3232254460160), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00008.record076_result⟩)
 (.leaf ⟨(32, 3232258621696), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00008.record077_result⟩)))
 (.branch 79
 (.leaf ⟨(32, 3232258686976), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00008.record078_result⟩)
 (.branch 80
 (.leaf ⟨(32, 3232378128640), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00008.record079_result⟩)
 (.leaf ⟨(32, 3232522862848), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00008.record080_result⟩))))
 (.branch 84
 (.branch 82
 (.leaf ⟨(32, 3232522928128), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00008.record081_result⟩)
 (.branch 83
 (.leaf ⟨(32, 3232527057024), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00008.record082_result⟩)
 (.leaf ⟨(32, 3232529137792), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00008.record083_result⟩)))
 (.branch 85
 (.leaf ⟨(32, 3232646563968), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00008.record084_result⟩)
 (.branch 86
 (.leaf ⟨(32, 3234400895232), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00008.record085_result⟩)
 (.leaf ⟨(32, 3234405056768), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00008.record086_result⟩)))))
 (.branch 93
 (.branch 90
 (.branch 88
 (.leaf ⟨(32, 3234405122048), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00008.record087_result⟩)
 (.branch 89
 (.leaf ⟨(32, 3234458503424), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00008.record088_result⟩)
 (.leaf ⟨(32, 3234669297920), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00008.record089_result⟩)))
 (.branch 91
 (.leaf ⟨(32, 3234669363200), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00008.record090_result⟩)
 (.branch 92
 (.leaf ⟨(32, 3234673492096), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00008.record091_result⟩)
 (.leaf ⟨(32, 3234726938752), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00008.record092_result⟩))))
 (.branch 96
 (.branch 94
 (.leaf ⟨(32, 3237075746817), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00008.record093_result⟩)
 (.branch 95
 (.leaf ⟨(32, 3238619252992), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00008.record094_result⟩)
 (.leaf ⟨(32, 3238693765376), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00008.record095_result⟩)))
 (.branch 98
 (.branch 97
 (.leaf ⟨(32, 3238700072960), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00008.record096_result⟩)
 (.leaf ⟨(32, 3238751373568), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00008.record097_result⟩))
 (.branch 99
 (.leaf ⟨(32, 3238817433856), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00008.record098_result⟩)
 (.leaf ⟨(32, 3238962168064), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00008.record099_result⟩))))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (27586 + i))) 0 100 :=
  interval_of_check _ 0 100 (by decide +kernel)

public theorem complete : Block 27586 27686 :=
  block_of_table results 27586 100 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0973
