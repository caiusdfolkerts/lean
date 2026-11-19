module
prelude
import GraphInputsRow25Part00008Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0298
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 42
 (.branch 21
 (.branch 10
 (.branch 5
 (.branch 2
 (.branch 1
 (.leaf ⟨(25, 10490067550209), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00008.record000_result⟩)
 (.leaf ⟨(25, 10585242603776), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00008.record001_result⟩))
 (.branch 3
 (.leaf ⟨(25, 10585506844928), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00008.record002_result⟩)
 (.branch 4
 (.leaf ⟨(25, 10601399058433), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00008.record003_result⟩)
 (.leaf ⟨(25, 10639451881472), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00008.record004_result⟩))))
 (.branch 7
 (.branch 6
 (.leaf ⟨(25, 10781852696576), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00008.record005_result⟩)
 (.leaf ⟨(25, 10782116937728), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00008.record006_result⟩))
 (.branch 8
 (.leaf ⟨(25, 10858841309184), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00008.record007_result⟩)
 (.branch 9
 (.leaf ⟨(25, 10859097098240), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00008.record008_result⟩)
 (.leaf ⟨(25, 10892192579584), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00008.record009_result⟩)))))
 (.branch 15
 (.branch 12
 (.branch 11
 (.leaf ⟨(25, 10892439980288), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00008.record010_result⟩)
 (.leaf ⟨(25, 10896600598784), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00008.record011_result⟩))
 (.branch 13
 (.leaf ⟨(25, 10896617243392), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00008.record012_result⟩)
 (.branch 14
 (.leaf ⟨(25, 10896898260992), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00008.record013_result⟩)
 (.leaf ⟨(25, 10901191131136), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00008.record014_result⟩))))
 (.branch 18
 (.branch 16
 (.leaf ⟨(25, 10905735659520), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00008.record015_result⟩)
 (.branch 17
 (.leaf ⟨(25, 10909619912704), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00008.record016_result⟩)
 (.leaf ⟨(25, 10909776871424), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00008.record017_result⟩)))
 (.branch 19
 (.leaf ⟨(25, 10909888315392), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00008.record018_result⟩)
 (.branch 20
 (.leaf ⟨(25, 11040622383360), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00008.record019_result⟩)
 (.leaf ⟨(25, 11238073499648), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00008.record020_result⟩))))))
 (.branch 31
 (.branch 26
 (.branch 23
 (.branch 22
 (.leaf ⟨(25, 11242894786560), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00008.record021_result⟩)
 (.leaf ⟨(25, 11246774518528), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00008.record022_result⟩))
 (.branch 24
 (.leaf ⟨(25, 11247055536128), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00008.record023_result⟩)
 (.branch 25
 (.leaf ⟨(25, 11283294326816), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00008.record024_result⟩)
 (.leaf ⟨(25, 11380325384192), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00008.record025_result⟩))))
 (.branch 28
 (.branch 27
 (.leaf ⟨(25, 11384226054144), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00008.record026_result⟩)
 (.leaf ⟨(25, 11384618254336), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00008.record027_result⟩))
 (.branch 29
 (.leaf ⟨(25, 11398912442496), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00008.record028_result⟩)
 (.branch 30
 (.leaf ⟨(25, 11401129132032), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00008.record029_result⟩)
 (.leaf ⟨(25, 11401397534720), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00008.record030_result⟩)))))
 (.branch 36
 (.branch 33
 (.branch 32
 (.leaf ⟨(25, 11448650563584), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00008.record031_result⟩)
 (.leaf ⟨(25, 11448910643200), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00008.record032_result⟩))
 (.branch 34
 (.leaf ⟨(25, 11452943433728), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00008.record033_result⟩)
 (.branch 35
 (.leaf ⟨(25, 11453203513344), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00008.record034_result⟩)
 (.leaf ⟨(25, 11455089868800), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00008.record035_result⟩))))
 (.branch 39
 (.branch 37
 (.leaf ⟨(25, 11463336951936), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00008.record036_result⟩)
 (.branch 38
 (.leaf ⟨(25, 11471926886400), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00008.record037_result⟩)
 (.leaf ⟨(25, 11472063168512), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00008.record038_result⟩)))
 (.branch 40
 (.leaf ⟨(25, 11487496142848), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00008.record039_result⟩)
 (.branch 41
 (.leaf ⟨(25, 11554877608192), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00008.record040_result⟩)
 (.leaf ⟨(25, 11585410072832), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00008.record041_result⟩)))))))
 (.branch 63
 (.branch 52
 (.branch 47
 (.branch 44
 (.branch 43
 (.leaf ⟨(25, 11585418461184), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00008.record042_result⟩)
 (.leaf ⟨(25, 11588113273088), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00008.record043_result⟩))
 (.branch 45
 (.leaf ⟨(25, 11589310808064), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00008.record044_result⟩)
 (.branch 46
 (.leaf ⟨(25, 11589579210752), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00008.record045_result⟩)
 (.leaf ⟨(25, 11592922595584), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00008.record046_result⟩))))
 (.branch 49
 (.branch 48
 (.leaf ⟨(25, 11592934625280), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00008.record047_result⟩)
 (.leaf ⟨(25, 11597900709888), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00008.record048_result⟩))
 (.branch 50
 (.leaf ⟨(25, 11598292877440), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00008.record049_result⟩)
 (.branch 51
 (.leaf ⟨(25, 11601512530048), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00008.record050_result⟩)
 (.leaf ⟨(25, 11605807480960), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00008.record051_result⟩)))))
 (.branch 57
 (.branch 54
 (.branch 53
 (.leaf ⟨(25, 11674526417536), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00008.record052_result⟩)
 (.leaf ⟨(25, 11684750037248), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00008.record053_result⟩))
 (.branch 55
 (.leaf ⟨(25, 11689571389440), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00008.record054_result⟩)
 (.branch 56
 (.leaf ⟨(25, 11693732139008), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00008.record055_result⟩)
 (.leaf ⟨(25, 11700778598400), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00008.record056_result⟩))))
 (.branch 60
 (.branch 58
 (.leaf ⟨(25, 11701371027584), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00008.record057_result⟩)
 (.branch 59
 (.leaf ⟨(25, 11730360992512), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00008.record058_result⟩)
 (.leaf ⟨(25, 11738950926976), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00008.record059_result⟩)))
 (.branch 61
 (.leaf ⟨(25, 11826998313088), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00008.record060_result⟩)
 (.branch 62
 (.leaf ⟨(25, 11830902657024), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00008.record061_result⟩)
 (.leaf ⟨(25, 11831293264000), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00008.record062_result⟩))))))
 (.branch 73
 (.branch 68
 (.branch 65
 (.branch 64
 (.leaf ⟨(25, 11931716943872), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00008.record063_result⟩)
 (.leaf ⟨(25, 11960548622592), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00008.record064_result⟩))
 (.branch 66
 (.leaf ⟨(25, 11960817090560), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00008.record065_result⟩)
 (.branch 67
 (.leaf ⟨(25, 11960825413632), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00008.record066_result⟩)
 (.leaf ⟨(25, 11961085493248), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00008.record067_result⟩))))
 (.branch 70
 (.branch 69
 (.leaf ⟨(25, 11961217613824), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00008.record068_result⟩)
 (.leaf ⟨(25, 11963937652736), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00008.record069_result⟩))
 (.branch 71
 (.leaf ⟨(25, 11963945975808), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00008.record070_result⟩)
 (.branch 72
 (.leaf ⟨(25, 11966921867520), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00008.record071_result⟩)
 (.leaf ⟨(25, 11967198658560), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00008.record072_result⟩)))))
 (.branch 78
 (.branch 75
 (.branch 74
 (.leaf ⟨(25, 11967458738176), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00008.record073_result⟩)
 (.leaf ⟨(25, 11984101736448), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00008.record074_result⟩))
 (.branch 76
 (.leaf ⟨(25, 11984238018560), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00008.record075_result⟩)
 (.branch 77
 (.leaf ⟨(25, 11995864662272), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00008.record076_result⟩)
 (.leaf ⟨(25, 11996133130240), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00008.record077_result⟩))))
 (.branch 81
 (.branch 79
 (.leaf ⟨(25, 11996141453312), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00008.record078_result⟩)
 (.branch 80
 (.leaf ⟨(25, 11996401532928), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00008.record079_result⟩)
 (.leaf ⟨(25, 11996649259008), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00008.record080_result⟩)))
 (.branch 82
 (.leaf ⟨(25, 12000434323456), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00008.record081_result⟩)
 (.branch 83
 (.leaf ⟨(25, 12000541605888), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00008.record082_result⟩)
 (.leaf ⟨(25, 12000694403072), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00008.record083_result⟩))))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (12737 + i))) 0 84 :=
  interval_of_check _ 0 84 (by decide +kernel)

public theorem complete : Block 12737 12821 :=
  block_of_table results 12737 84 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0298
