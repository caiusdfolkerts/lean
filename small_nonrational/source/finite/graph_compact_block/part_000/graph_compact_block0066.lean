module
prelude
import GraphInputsRow19Part00026Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0066
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 50
 (.branch 25
 (.branch 12
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(19, 27632852861184), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00026.record000_result⟩)
 (.branch 2
 (.leaf ⟨(19, 27632857088000), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00026.record001_result⟩)
 (.leaf ⟨(19, 27637211791616), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00026.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(19, 27637218033920), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00026.record003_result⟩)
 (.branch 5
 (.leaf ⟨(19, 27637218099200), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00026.record004_result⟩)
 (.leaf ⟨(19, 27637620686912), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00026.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(19, 27637680455936), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00026.record006_result⟩)
 (.branch 8
 (.leaf ⟨(19, 27637688844288), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00026.record007_result⟩)
 (.leaf ⟨(19, 27637754904576), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00026.record008_result⟩)))
 (.branch 10
 (.leaf ⟨(19, 27645801758720), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00026.record009_result⟩)
 (.branch 11
 (.leaf ⟨(19, 27645803839488), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00026.record010_result⟩)
 (.leaf ⟨(19, 27645808001024), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00026.record011_result⟩)))))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf ⟨(19, 27645943226432), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00026.record012_result⟩)
 (.branch 14
 (.leaf ⟨(19, 27646076403712), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00026.record013_result⟩)
 (.leaf ⟨(19, 27646570799168), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00026.record014_result⟩)))
 (.branch 16
 (.leaf ⟨(19, 27646571855872), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00026.record015_result⟩)
 (.branch 17
 (.leaf ⟨(19, 27648652230656), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00026.record016_result⟩)
 (.leaf ⟨(19, 27652177019136), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00026.record017_result⟩))))
 (.branch 21
 (.branch 19
 (.leaf ⟨(19, 27652177084416), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00026.record018_result⟩)
 (.branch 20
 (.leaf ⟨(19, 27652183310400), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00026.record019_result⟩)
 (.leaf ⟨(19, 27653323628608), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00026.record020_result⟩)))
 (.branch 23
 (.branch 22
 (.leaf ⟨(19, 27660823609600), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00026.record021_result⟩)
 (.leaf ⟨(19, 27661219971328), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00026.record022_result⟩))
 (.branch 24
 (.leaf ⟨(19, 27661226262592), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00026.record023_result⟩)
 (.leaf ⟨(19, 27664172261632), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00026.record024_result⟩))))))
 (.branch 37
 (.branch 31
 (.branch 28
 (.branch 26
 (.leaf ⟨(19, 27664178552896), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00026.record025_result⟩)
 (.branch 27
 (.leaf ⟨(19, 27664464265224), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00026.record026_result⟩)
 (.leaf ⟨(19, 27668735664192), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00026.record027_result⟩)))
 (.branch 29
 (.leaf ⟨(19, 27672534073600), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00026.record028_result⟩)
 (.branch 30
 (.leaf ⟨(19, 27673623675136), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00026.record029_result⟩)
 (.leaf ⟨(19, 27673623740416), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00026.record030_result⟩))))
 (.branch 34
 (.branch 32
 (.leaf ⟨(19, 27674094339136), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00026.record031_result⟩)
 (.branch 33
 (.leaf ⟨(19, 27676946513928), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00026.record032_result⟩)
 (.leaf ⟨(19, 27680129105920), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00026.record033_result⟩)))
 (.branch 35
 (.leaf ⟨(19, 27681117798400), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00026.record034_result⟩)
 (.branch 36
 (.leaf ⟨(19, 27682209415424), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00026.record035_result⟩)
 (.leaf ⟨(19, 27682209480704), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00026.record036_result⟩)))))
 (.branch 43
 (.branch 40
 (.branch 38
 (.leaf ⟨(19, 27682211366144), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00026.record037_result⟩)
 (.branch 39
 (.leaf ⟨(19, 27682415838272), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00026.record038_result⟩)
 (.leaf ⟨(19, 27685412684032), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00026.record039_result⟩)))
 (.branch 41
 (.leaf ⟨(19, 27685412749312), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00026.record040_result⟩)
 (.branch 42
 (.leaf ⟨(19, 27685418975296), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00026.record041_result⟩)
 (.leaf ⟨(19, 27685512880128), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00026.record042_result⟩))))
 (.branch 46
 (.branch 44
 (.leaf ⟨(19, 27685519106112), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00026.record043_result⟩)
 (.branch 45
 (.leaf ⟨(19, 27685530175488), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00026.record044_result⟩)
 (.leaf ⟨(19, 27686575693824), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00026.record045_result⟩)))
 (.branch 48
 (.branch 47
 (.leaf ⟨(19, 27689696256000), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00026.record046_result⟩)
 (.leaf ⟨(19, 27695581831232), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00026.record047_result⟩))
 (.branch 49
 (.leaf ⟨(19, 27712407240960), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00026.record048_result⟩)
 (.leaf ⟨(19, 27714100150272), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00026.record049_result⟩)))))))
 (.branch 75
 (.branch 62
 (.branch 56
 (.branch 53
 (.branch 51
 (.leaf ⟨(19, 27719804403968), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00026.record050_result⟩)
 (.branch 52
 (.leaf ⟨(19, 27721901162752), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00026.record051_result⟩)
 (.leaf ⟨(19, 27721901228032), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00026.record052_result⟩)))
 (.branch 54
 (.leaf ⟨(19, 27721909404736), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00026.record053_result⟩)
 (.branch 55
 (.leaf ⟨(19, 27722404856896), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00026.record054_result⟩)
 (.leaf ⟨(19, 27728401449216), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00026.record055_result⟩))))
 (.branch 59
 (.branch 57
 (.leaf ⟨(19, 27728602800192), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00026.record056_result⟩)
 (.branch 58
 (.leaf ⟨(19, 27730617860352), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00026.record057_result⟩)
 (.leaf ⟨(19, 27730733369408), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00026.record058_result⟩)))
 (.branch 60
 (.leaf ⟨(19, 27733160657152), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00026.record059_result⟩)
 (.branch 61
 (.leaf ⟨(19, 27745564409864), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00026.record060_result⟩)
 (.leaf ⟨(19, 27756228445184), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00026.record061_result⟩)))))
 (.branch 68
 (.branch 65
 (.branch 63
 (.leaf ⟨(19, 27765996830976), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00026.record062_result⟩)
 (.branch 64
 (.leaf ⟨(19, 27774586732800), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00026.record063_result⟩)
 (.leaf ⟨(19, 27774925422592), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00026.record064_result⟩)))
 (.branch 66
 (.leaf ⟨(19, 27798192308480), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00026.record065_result⟩)
 (.branch 67
 (.leaf ⟨(19, 27798258368768), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00026.record066_result⟩)
 (.leaf ⟨(19, 27798390489344), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00026.record067_result⟩))))
 (.branch 71
 (.branch 69
 (.leaf ⟨(19, 27809968832768), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00026.record068_result⟩)
 (.branch 70
 (.leaf ⟨(19, 27809968898048), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00026.record069_result⟩)
 (.leaf ⟨(19, 27865836208384), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00026.record070_result⟩)))
 (.branch 73
 (.branch 72
 (.leaf ⟨(19, 27901268377856), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00026.record071_result⟩)
 (.leaf ⟨(19, 27901469728832), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00026.record072_result⟩))
 (.branch 74
 (.leaf ⟨(19, 27902542946368), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00026.record073_result⟩)
 (.leaf ⟨(19, 27904689381440), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00026.record074_result⟩))))))
 (.branch 87
 (.branch 81
 (.branch 78
 (.branch 76
 (.leaf ⟨(19, 27915174691072), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00026.record075_result⟩)
 (.branch 77
 (.leaf ⟨(19, 27915174756352), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00026.record076_result⟩)
 (.leaf ⟨(19, 27915182933056), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00026.record077_result⟩)))
 (.branch 79
 (.leaf ⟨(19, 27915215589376), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00026.record078_result⟩)
 (.branch 80
 (.leaf ⟨(19, 27915678385216), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00026.record079_result⟩)
 (.leaf ⟨(19, 28043088331008), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00026.record080_result⟩))))
 (.branch 84
 (.branch 82
 (.leaf ⟨(19, 28076478204176), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00026.record081_result⟩)
 (.branch 83
 (.leaf ⟨(19, 28076489146624), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00026.record082_result⟩)
 (.leaf ⟨(19, 28076495388928), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00026.record083_result⟩)))
 (.branch 85
 (.leaf ⟨(19, 28077621084160), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00026.record084_result⟩)
 (.branch 86
 (.leaf ⟨(19, 28110850957568), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00026.record085_result⟩)
 (.leaf ⟨(19, 28110855119104), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00026.record086_result⟩)))))
 (.branch 93
 (.branch 90
 (.branch 88
 (.leaf ⟨(19, 28116242145536), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00026.record087_result⟩)
 (.branch 89
 (.leaf ⟨(19, 28120527732992), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00026.record088_result⟩)
 (.leaf ⟨(19, 28120807645184), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00026.record089_result⟩)))
 (.branch 91
 (.leaf ⟨(19, 28121064603648), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00026.record090_result⟩)
 (.branch 92
 (.leaf ⟨(19, 28121072926720), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00026.record091_result⟩)
 (.leaf ⟨(19, 28152046817280), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00026.record092_result⟩))))
 (.branch 96
 (.branch 94
 (.leaf ⟨(19, 28152575361280), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00026.record093_result⟩)
 (.branch 95
 (.leaf ⟨(19, 28152847990784), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00026.record094_result⟩)
 (.leaf ⟨(19, 28153112231936), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00026.record095_result⟩)))
 (.branch 98
 (.branch 97
 (.leaf ⟨(19, 28153120555008), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00026.record096_result⟩)
 (.leaf ⟨(19, 28153384796160), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00026.record097_result⟩))
 (.branch 99
 (.leaf ⟨(19, 28168946253824), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00026.record098_result⟩)
 (.leaf ⟨(19, 28214919495936), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00026.record099_result⟩))))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (4639 + i))) 0 100 :=
  interval_of_check _ 0 100 (by decide +kernel)

public theorem complete : Block 4639 4739 :=
  block_of_table results 4639 100 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0066
