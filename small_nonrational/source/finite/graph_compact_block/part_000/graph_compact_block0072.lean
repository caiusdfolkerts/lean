module
prelude
import GraphInputsRow19Part00032Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0072
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 34
 (.branch 17
 (.branch 8
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨(19, 31658309124096), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00032.record000_result⟩)
 (.leaf ⟨(19, 31681042981120), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00032.record001_result⟩))
 (.branch 3
 (.leaf ⟨(19, 31682116198656), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00032.record002_result⟩)
 (.leaf ⟨(19, 31688374618368), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00032.record003_result⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨(19, 31688555503872), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00032.record004_result⟩)
 (.leaf ⟨(19, 31714328191232), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00032.record005_result⟩))
 (.branch 7
 (.leaf ⟨(19, 31714328971520), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00032.record006_result⟩)
 (.leaf ⟨(19, 31722699884800), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00032.record007_result⟩))))
 (.branch 12
 (.branch 10
 (.branch 9
 (.leaf ⟨(19, 31749559123968), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00032.record008_result⟩)
 (.leaf ⟨(19, 31749628240128), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00032.record009_result⟩))
 (.branch 11
 (.leaf ⟨(19, 31749628305408), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00032.record010_result⟩)
 (.leaf ⟨(19, 31749635579936), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00032.record011_result⟩)))
 (.branch 14
 (.branch 13
 (.leaf ⟨(19, 31749678565632), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00032.record012_result⟩)
 (.leaf ⟨(19, 31750652692736), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00032.record013_result⟩))
 (.branch 15
 (.leaf ⟨(19, 31750698336512), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00032.record014_result⟩)
 (.branch 16
 (.leaf ⟨(19, 31750698401792), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00032.record015_result⟩)
 (.leaf ⟨(19, 31750701522944), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00032.record016_result⟩))))))
 (.branch 25
 (.branch 21
 (.branch 19
 (.branch 18
 (.leaf ⟨(19, 31752799127808), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00032.record017_result⟩)
 (.leaf ⟨(19, 31752806467616), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00032.record018_result⟩))
 (.branch 20
 (.leaf ⟨(19, 31752980013312), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00032.record019_result⟩)
 (.leaf ⟨(19, 31752980078592), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00032.record020_result⟩)))
 (.branch 23
 (.branch 22
 (.leaf ⟨(19, 31752987353120), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00032.record021_result⟩)
 (.leaf ⟨(19, 31752987873312), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00032.record022_result⟩))
 (.branch 24
 (.leaf ⟨(19, 31753004648480), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00032.record023_result⟩)
 (.leaf ⟨(19, 31755126448384), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00032.record024_result⟩))))
 (.branch 29
 (.branch 27
 (.branch 26
 (.leaf ⟨(19, 31755663319040), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00032.record025_result⟩)
 (.leaf ⟨(19, 31755664359424), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00032.record026_result⟩))
 (.branch 28
 (.leaf ⟨(19, 31761367572736), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00032.record027_result⟩)
 (.leaf ⟨(19, 31761375961088), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00032.record028_result⟩)))
 (.branch 31
 (.branch 30
 (.leaf ⟨(19, 31761837334560), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00032.record029_result⟩)
 (.leaf ⟨(19, 31763464331520), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00032.record030_result⟩))
 (.branch 32
 (.leaf ⟨(19, 31763465437184), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00032.record031_result⟩)
 (.branch 33
 (.leaf ⟨(19, 31763472719872), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00032.record032_result⟩)
 (.leaf ⟨(19, 31763473630208), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00032.record033_result⟩)))))))
 (.branch 51
 (.branch 42
 (.branch 38
 (.branch 36
 (.branch 35
 (.leaf ⟨(19, 31763506660352), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00032.record034_result⟩)
 (.leaf ⟨(19, 31763531301632), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00032.record035_result⟩))
 (.branch 37
 (.leaf ⟨(19, 31763967643680), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00032.record036_result⟩)
 (.leaf ⟨(19, 31763969082368), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00032.record037_result⟩)))
 (.branch 40
 (.branch 39
 (.leaf ⟨(19, 31778497765376), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00032.record038_result⟩)
 (.leaf ⟨(19, 31778531705856), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00032.record039_result⟩))
 (.branch 41
 (.leaf ⟨(19, 31782844334080), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00032.record040_result⟩)
 (.leaf ⟨(19, 31782913450240), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00032.record041_result⟩))))
 (.branch 46
 (.branch 44
 (.branch 43
 (.leaf ⟨(19, 31782913515520), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00032.record042_result⟩)
 (.leaf ⟨(19, 31785044019456), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00032.record043_result⟩))
 (.branch 45
 (.leaf ⟨(19, 31785044084736), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00032.record044_result⟩)
 (.leaf ⟨(19, 31785052275720), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00032.record045_result⟩)))
 (.branch 48
 (.branch 47
 (.leaf ⟨(19, 31785182447616), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00032.record046_result⟩)
 (.leaf ⟨(19, 31787124394240), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00032.record047_result⟩))
 (.branch 49
 (.leaf ⟨(19, 31787329914912), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00032.record048_result⟩)
 (.branch 50
 (.leaf ⟨(19, 31787330831368), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00032.record049_result⟩)
 (.leaf ⟨(19, 31812823942144), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00032.record050_result⟩))))))
 (.branch 60
 (.branch 55
 (.branch 53
 (.branch 52
 (.leaf ⟨(19, 31817206145024), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00032.record051_result⟩)
 (.leaf ⟨(19, 31819336714240), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00032.record052_result⟩))
 (.branch 54
 (.leaf ⟨(19, 31930457276416), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00032.record053_result⟩)
 (.leaf ⟨(19, 31942914375936), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00032.record054_result⟩)))
 (.branch 57
 (.branch 56
 (.leaf ⟨(19, 31942925885440), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00032.record055_result⟩)
 (.leaf ⟨(19, 31957950988544), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00032.record056_result⟩))
 (.branch 58
 (.leaf ⟨(19, 31957955215360), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00032.record057_result⟩)
 (.branch 59
 (.leaf ⟨(19, 31957958271232), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00032.record058_result⟩)
 (.leaf ⟨(19, 31960508407840), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00032.record059_result⟩)))))
 (.branch 64
 (.branch 62
 (.branch 61
 (.leaf ⟨(19, 31960541958176), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00032.record060_result⟩)
 (.leaf ⟨(19, 31962375979264), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00032.record061_result⟩))
 (.branch 63
 (.leaf ⟨(19, 31962655891456), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00032.record062_result⟩)
 (.leaf ⟨(19, 31962912849920), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00032.record063_result⟩)))
 (.branch 66
 (.branch 65
 (.leaf ⟨(19, 31962921172992), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00032.record064_result⟩)
 (.leaf ⟨(19, 31975130857472), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00032.record065_result⟩))
 (.branch 67
 (.leaf ⟨(19, 31975138140160), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00032.record066_result⟩)
 (.branch 68
 (.leaf ⟨(19, 31977207005440), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00032.record067_result⟩)
 (.leaf ⟨(19, 31977211232256), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00032.record068_result⟩))))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (5213 + i))) 0 69 :=
  interval_of_check _ 0 69 (by decide +kernel)

public theorem complete : Block 5213 5282 :=
  block_of_table results 5213 69 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0072
