module
prelude
import GraphInputsSix0Part00049Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock1014
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 50
 (.branch 25
 (.branch 12
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(32, 19294884741184), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00049.record000_result⟩)
 (.branch 2
 (.leaf ⟨(32, 19298105954368), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00049.record001_result⟩)
 (.leaf ⟨(32, 19315030564992), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00049.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(32, 19315889864960), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00049.record003_result⟩)
 (.branch 5
 (.leaf ⟨(32, 19316087136384), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00049.record004_result⟩)
 (.leaf ⟨(32, 19316158267648), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00049.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(32, 19316158332928), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00049.record006_result⟩)
 (.branch 8
 (.leaf ⟨(32, 19317433307392), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00049.record007_result⟩)
 (.leaf ⟨(32, 19320050614528), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00049.record008_result⟩)))
 (.branch 10
 (.leaf ⟨(32, 19320182735104), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00049.record009_result⟩)
 (.branch 11
 (.leaf ⟨(32, 19320446976256), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00049.record010_result⟩)
 (.leaf ⟨(32, 19320451137792), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00049.record011_result⟩)))))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf ⟨(32, 19320451203072), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00049.record012_result⟩)
 (.branch 14
 (.leaf ⟨(32, 19320453218560), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00049.record013_result⟩)
 (.leaf ⟨(32, 19321594056960), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00049.record014_result⟩)))
 (.branch 16
 (.leaf ⟨(32, 19327915417728), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00049.record015_result⟩)
 (.branch 17
 (.leaf ⟨(32, 19328640516352), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00049.record016_result⟩)
 (.leaf ⟨(32, 19328640581632), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00049.record017_result⟩))))
 (.branch 21
 (.branch 19
 (.leaf ⟨(32, 19328768475392), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00049.record018_result⟩)
 (.branch 20
 (.leaf ⟨(32, 19328772636928), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00049.record019_result⟩)
 (.leaf ⟨(32, 19328772702208), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00049.record020_result⟩)))
 (.branch 23
 (.branch 22
 (.leaf ⟨(32, 19328774717696), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00049.record021_result⟩)
 (.leaf ⟨(32, 19329036878080), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00049.record022_result⟩))
 (.branch 24
 (.leaf ⟨(32, 19329036943360), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00049.record023_result⟩)
 (.leaf ⟨(32, 19329244471360), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00049.record024_result⟩))))))
 (.branch 37
 (.branch 31
 (.branch 28
 (.branch 26
 (.leaf ⟨(32, 19329915556096), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00049.record025_result⟩)
 (.branch 27
 (.leaf ⟨(32, 19330318209088), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00049.record026_result⟩)
 (.leaf ⟨(32, 19358092951808), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00049.record027_result⟩)))
 (.branch 29
 (.leaf ⟨(32, 19366825426945), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00049.record028_result⟩)
 (.branch 30
 (.leaf ⟨(32, 19386018566400), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00049.record029_result⟩)
 (.leaf ⟨(32, 19388767994112), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00049.record030_result⟩))))
 (.branch 34
 (.branch 32
 (.leaf ⟨(32, 19389170598144), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00049.record031_result⟩)
 (.branch 33
 (.leaf ⟨(32, 19389170663424), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00049.record032_result⟩)
 (.leaf ⟨(32, 19390311436544), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00049.record033_result⟩)))
 (.branch 35
 (.leaf ⟨(32, 19397353734400), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00049.record034_result⟩)
 (.branch 36
 (.leaf ⟨(32, 19397357895936), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00049.record035_result⟩)
 (.leaf ⟨(32, 19397357961216), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00049.record036_result⟩)))))
 (.branch 43
 (.branch 40
 (.branch 38
 (.leaf ⟨(32, 19397359976704), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00049.record037_result⟩)
 (.branch 39
 (.leaf ⟨(32, 19397492097280), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00049.record038_result⟩)
 (.leaf ⟨(32, 19397492162560), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00049.record039_result⟩)))
 (.branch 41
 (.leaf ⟨(32, 19397756338432), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00049.record040_result⟩)
 (.branch 42
 (.leaf ⟨(32, 19397756403712), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00049.record041_result⟩)
 (.leaf ⟨(32, 19397762629696), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00049.record042_result⟩))))
 (.branch 46
 (.branch 44
 (.leaf ⟨(32, 19397829730368), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00049.record043_result⟩)
 (.branch 45
 (.leaf ⟨(32, 19398632935680), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00049.record044_result⟩)
 (.leaf ⟨(32, 19398903468096), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00049.record045_result⟩)))
 (.branch 48
 (.branch 47
 (.leaf ⟨(32, 19435410685953), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00049.record046_result⟩)
 (.leaf ⟨(32, 19451244249344), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00049.record047_result⟩))
 (.branch 49
 (.leaf ⟨(32, 19451508490496), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00049.record048_result⟩)
 (.leaf ⟨(32, 19451516878848), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00049.record049_result⟩)))))))
 (.branch 75
 (.branch 62
 (.branch 56
 (.branch 53
 (.branch 51
 (.leaf ⟨(32, 19451640611072), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00049.record050_result⟩)
 (.branch 52
 (.leaf ⟨(32, 19453324624128), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00049.record051_result⟩)
 (.leaf ⟨(32, 19453588865280), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00049.record052_result⟩)))
 (.branch 54
 (.leaf ⟨(32, 19453597253632), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00049.record053_result⟩)
 (.branch 55
 (.leaf ⟨(32, 19457881735424), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00049.record054_result⟩)
 (.leaf ⟨(32, 19457890123776), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00049.record055_result⟩))))
 (.branch 59
 (.branch 57
 (.leaf ⟨(32, 19466471637248), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00049.record056_result⟩)
 (.branch 58
 (.leaf ⟨(32, 19466475864064), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00049.record057_result⟩)
 (.leaf ⟨(32, 19466482106368), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00049.record058_result⟩)))
 (.branch 60
 (.leaf ⟨(32, 19466671898880), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00049.record059_result⟩)
 (.branch 61
 (.leaf ⟨(32, 19469758923008), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00049.record060_result⟩)
 (.leaf ⟨(32, 19471041298432), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00049.record061_result⟩)))))
 (.branch 68
 (.branch 65
 (.branch 63
 (.leaf ⟨(32, 19474524733696), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00049.record062_result⟩)
 (.branch 64
 (.leaf ⟨(32, 19474665242624), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00049.record063_result⟩)
 (.leaf ⟨(32, 19475061604352), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00049.record064_result⟩)))
 (.branch 66
 (.leaf ⟨(32, 19475069927424), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00049.record065_result⟩)
 (.branch 67
 (.leaf ⟨(32, 19486560289024), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00049.record066_result⟩)
 (.leaf ⟨(32, 19486824530176), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00049.record067_result⟩))))
 (.branch 71
 (.branch 69
 (.leaf ⟨(32, 19486832918528), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00049.record068_result⟩)
 (.branch 70
 (.leaf ⟨(32, 19487072256256), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00049.record069_result⟩)
 (.leaf ⟨(32, 19491117400320), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00049.record070_result⟩)))
 (.branch 73
 (.branch 72
 (.leaf ⟨(32, 19491125788672), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00049.record071_result⟩)
 (.leaf ⟨(32, 19491233005824), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00049.record072_result⟩))
 (.branch 74
 (.leaf ⟨(32, 19499554504960), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00049.record073_result⟩)
 (.leaf ⟨(32, 19499707302144), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00049.record074_result⟩))))))
 (.branch 87
 (.branch 81
 (.branch 78
 (.branch 76
 (.leaf ⟨(32, 19499711528960), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00049.record075_result⟩)
 (.branch 77
 (.leaf ⟨(32, 19499717771264), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00049.record076_result⟩)
 (.leaf ⟨(32, 19499822907648), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00049.record077_result⟩)))
 (.branch 79
 (.leaf ⟨(32, 19499835197440), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00049.record078_result⟩)
 (.branch 80
 (.leaf ⟨(32, 19499957108992), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00049.record079_result⟩)
 (.leaf ⟨(32, 19504121839616), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00049.record080_result⟩))))
 (.branch 84
 (.branch 82
 (.leaf ⟨(32, 19504251798272), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00049.record081_result⟩)
 (.branch 83
 (.leaf ⟨(32, 19512036622592), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00049.record082_result⟩)
 (.leaf ⟨(32, 19512573493248), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00049.record083_result⟩)))
 (.branch 85
 (.leaf ⟨(32, 19512581816320), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00049.record084_result⟩)
 (.branch 86
 (.leaf ⟨(32, 19523189084416), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00049.record085_result⟩)
 (.leaf ⟨(32, 19523591737408), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00049.record086_result⟩)))))
 (.branch 93
 (.branch 90
 (.branch 88
 (.leaf ⟨(32, 19527481954560), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00049.record087_result⟩)
 (.branch 89
 (.leaf ⟨(32, 19527752486976), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00049.record088_result⟩)
 (.leaf ⟨(32, 19534792655104), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00049.record089_result⟩)))
 (.branch 91
 (.leaf ⟨(32, 19534792720384), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00049.record090_result⟩)
 (.branch 92
 (.leaf ⟨(32, 19534926856448), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00049.record091_result⟩)
 (.leaf ⟨(32, 19534926921728), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00049.record092_result⟩))))
 (.branch 96
 (.branch 94
 (.leaf ⟨(32, 19534933147712), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00049.record093_result⟩)
 (.branch 95
 (.leaf ⟨(32, 19535000248384), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00049.record094_result⟩)
 (.leaf ⟨(32, 19535195324416), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00049.record095_result⟩)))
 (.branch 98
 (.branch 97
 (.leaf ⟨(32, 19536067694848), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00049.record096_result⟩)
 (.leaf ⟨(32, 19536073986112), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00049.record097_result⟩))
 (.branch 99
 (.leaf ⟨(32, 19538991153152), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00049.record098_result⟩)
 (.leaf ⟨(32, 19539090243584), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00049.record099_result⟩))))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (31650 + i))) 0 100 :=
  interval_of_check _ 0 100 (by decide +kernel)

public theorem complete : Block 31650 31750 :=
  block_of_table results 31650 100 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock1014
