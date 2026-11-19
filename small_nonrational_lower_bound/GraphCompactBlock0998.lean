module
prelude
import GraphInputsSix0Part00033Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0998
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 50
 (.branch 25
 (.branch 12
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(32, 12524295555200), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00033.record000_result⟩)
 (.branch 2
 (.leaf ⟨(32, 12541457891584), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00033.record001_result⟩)
 (.leaf ⟨(32, 12541465987200), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00033.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(32, 12545742211200), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00033.record003_result⟩)
 (.branch 5
 (.leaf ⟨(32, 12545891041280), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00033.record004_result⟩)
 (.leaf ⟨(32, 12550181765376), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00033.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(32, 12550297370880), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00033.record006_result⟩)
 (.branch 8
 (.leaf ⟨(32, 12554592060160), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00033.record007_result⟩)
 (.leaf ⟨(32, 12558620821632), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00033.record008_result⟩)))
 (.branch 10
 (.leaf ⟨(32, 12575750521088), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00033.record009_result⟩)
 (.branch 11
 (.leaf ⟨(32, 12575750586368), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00033.record010_result⟩)
 (.leaf ⟨(32, 12575752667136), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00033.record011_result⟩)))))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf ⟨(32, 12575754422528), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00033.record012_result⟩)
 (.branch 14
 (.leaf ⟨(32, 12575756796032), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00033.record013_result⟩)
 (.leaf ⟨(32, 12575756828672), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00033.record014_result⟩)))
 (.branch 16
 (.leaf ⟨(32, 12575758616704), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00033.record015_result⟩)
 (.branch 17
 (.leaf ⟨(32, 12575878154248), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00033.record016_result⟩)
 (.leaf ⟨(32, 12575952603392), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00033.record017_result⟩))))
 (.branch 21
 (.branch 19
 (.leaf ⟨(32, 12575958130688), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00033.record018_result⟩)
 (.branch 20
 (.leaf ⟨(32, 12576010274824), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00033.record019_result⟩)
 (.leaf ⟨(32, 12576221038720), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00033.record020_result⟩)))
 (.branch 23
 (.branch 22
 (.leaf ⟨(32, 12577950271744), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00033.record021_result⟩)
 (.leaf ⟨(32, 12577950337024), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00033.record022_result⟩))
 (.branch 24
 (.leaf ⟨(32, 12577954465920), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00033.record023_result⟩)
 (.leaf ⟨(32, 12577958528008), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00033.record024_result⟩))))))
 (.branch 37
 (.branch 31
 (.branch 28
 (.branch 26
 (.leaf ⟨(32, 12577975304193), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00033.record025_result⟩)
 (.branch 27
 (.leaf ⟨(32, 12578090648584), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00033.record026_result⟩)
 (.leaf ⟨(32, 12578103296000), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00033.record027_result⟩)))
 (.branch 29
 (.leaf ⟨(32, 12578107424769), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00033.record028_result⟩)
 (.branch 30
 (.leaf ⟨(32, 12578354889736), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00033.record029_result⟩)
 (.leaf ⟨(32, 12578371665921), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00033.record030_result⟩))))
 (.branch 34
 (.branch 32
 (.leaf ⟨(32, 12580030711808), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00033.record031_result⟩)
 (.branch 33
 (.leaf ⟨(32, 12580249731072), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00033.record032_result⟩)
 (.leaf ⟨(32, 12584323516672), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00033.record033_result⟩)))
 (.branch 35
 (.leaf ⟨(32, 12584323581952), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00033.record034_result⟩)
 (.branch 36
 (.leaf ⟨(32, 12584540455168), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00033.record035_result⟩)
 (.leaf ⟨(32, 12584542601216), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00033.record036_result⟩)))))
 (.branch 43
 (.branch 40
 (.branch 38
 (.leaf ⟨(32, 12584590000384), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00033.record037_result⟩)
 (.branch 39
 (.leaf ⟨(32, 12584794194952), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00033.record038_result⟩)
 (.leaf ⟨(32, 12584810971137), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00033.record039_result⟩)))
 (.branch 41
 (.leaf ⟨(32, 12586804314880), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00033.record040_result⟩)
 (.branch 42
 (.leaf ⟨(32, 12588952911872), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00033.record041_result⟩)
 (.leaf ⟨(32, 12592913451136), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00033.record042_result⟩))))
 (.branch 46
 (.branch 44
 (.leaf ⟨(32, 12645514182912), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00033.record043_result⟩)
 (.branch 45
 (.leaf ⟨(32, 12645518377088), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00033.record044_result⟩)
 (.leaf ⟨(32, 12645613273344), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00033.record045_result⟩)))
 (.branch 48
 (.branch 47
 (.leaf ⟨(32, 12645617467520), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00033.record046_result⟩)
 (.leaf ⟨(32, 12645621137424), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00033.record047_result⟩))
 (.branch 49
 (.leaf ⟨(32, 12645747474688), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00033.record048_result⟩)
 (.leaf ⟨(32, 12645751636224), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00033.record049_result⟩)))))))
 (.branch 75
 (.branch 62
 (.branch 56
 (.branch 53
 (.branch 51
 (.leaf ⟨(32, 12645751668864), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00033.record050_result⟩)
 (.branch 52
 (.leaf ⟨(32, 12645753258000), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00033.record051_result⟩)
 (.leaf ⟨(32, 12646017499152), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00033.record052_result⟩)))
 (.branch 54
 (.leaf ⟨(32, 12646020071552), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00033.record053_result⟩)
 (.branch 55
 (.leaf ⟨(32, 12648968687872), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00033.record054_result⟩)
 (.leaf ⟨(32, 12648972882048), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00033.record055_result⟩))))
 (.branch 59
 (.branch 57
 (.leaf ⟨(32, 12648972910608), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00033.record056_result⟩)
 (.branch 58
 (.leaf ⟨(32, 12648985463040), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00033.record057_result⟩)
 (.leaf ⟨(32, 12648989397120), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00033.record058_result⟩)))
 (.branch 60
 (.leaf ⟨(32, 12648989425680), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00033.record059_result⟩)
 (.branch 61
 (.leaf ⟨(32, 12650062873216), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00033.record060_result⟩)
 (.leaf ⟨(32, 12653146212608), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00033.record061_result⟩)))))
 (.branch 68
 (.branch 65
 (.branch 63
 (.leaf ⟨(32, 12653150146688), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00033.record062_result⟩)
 (.branch 64
 (.leaf ⟨(32, 12653150175248), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00033.record063_result⟩)
 (.leaf ⟨(32, 12653261558016), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00033.record064_result⟩)))
 (.branch 66
 (.leaf ⟨(32, 12653267861520), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00033.record065_result⟩)
 (.branch 67
 (.leaf ⟨(32, 12653284376592), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00033.record066_result⟩)
 (.leaf ⟨(32, 12653536264208), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00033.record067_result⟩))))
 (.branch 71
 (.branch 69
 (.leaf ⟨(32, 12654355742976), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00033.record068_result⟩)
 (.branch 70
 (.leaf ⟨(32, 12654361985280), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00033.record069_result⟩)
 (.leaf ⟨(32, 12654462636288), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00033.record070_result⟩)))
 (.branch 73
 (.branch 72
 (.leaf ⟨(32, 12654592835600), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00033.record071_result⟩)
 (.leaf ⟨(32, 12713397157904), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00033.record072_result⟩))
 (.branch 74
 (.leaf ⟨(32, 12721970153488), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00033.record073_result⟩)
 (.leaf ⟨(32, 12721983127808), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00033.record074_result⟩))))))
 (.branch 87
 (.branch 81
 (.branch 78
 (.branch 76
 (.leaf ⟨(32, 12721986798096), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00033.record075_result⟩)
 (.branch 77
 (.leaf ⟨(32, 12721990930688), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00033.record076_result⟩)
 (.leaf ⟨(32, 12723173785856), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00033.record077_result⟩)))
 (.branch 79
 (.leaf ⟨(32, 12723182174208), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00033.record078_result⟩)
 (.branch 80
 (.leaf ⟨(32, 12781982416912), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00033.record079_result⟩)
 (.leaf ⟨(32, 12782116618256), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00033.record080_result⟩))))
 (.branch 84
 (.branch 82
 (.leaf ⟨(32, 12782385020944), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00033.record081_result⟩)
 (.branch 83
 (.leaf ⟨(32, 12786394662928), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00033.record082_result⟩)
 (.leaf ⟨(32, 12786411307536), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00033.record083_result⟩)))
 (.branch 85
 (.leaf ⟨(32, 12786415440128), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00033.record084_result⟩)
 (.branch 86
 (.leaf ⟨(32, 12790706749696), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00033.record085_result⟩)
 (.leaf ⟨(32, 12790708310272), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00033.record086_result⟩)))))
 (.branch 93
 (.branch 90
 (.branch 88
 (.leaf ⟨(32, 12790972551424), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00033.record087_result⟩)
 (.branch 89
 (.leaf ⟨(32, 12791899553792), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00033.record088_result⟩)
 (.leaf ⟨(32, 12795110818048), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00033.record089_result⟩)))
 (.branch 91
 (.leaf ⟨(32, 12800485294080), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00033.record090_result⟩)
 (.branch 92
 (.leaf ⟨(32, 12829205790976), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00033.record091_result⟩)
 (.leaf ⟨(32, 12829478420480), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00033.record092_result⟩))))
 (.branch 96
 (.branch 94
 (.leaf ⟨(32, 12864232358656), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00033.record093_result⟩)
 (.branch 95
 (.leaf ⟨(32, 12898063679488), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00033.record094_result⟩)
 (.leaf ⟨(32, 12898600484864), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00033.record095_result⟩)))
 (.branch 98
 (.branch 97
 (.leaf ⟨(32, 12919417176080), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00033.record096_result⟩)
 (.leaf ⟨(32, 12919551377424), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00033.record097_result⟩))
 (.branch 99
 (.leaf ⟨(32, 12919555538960), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00033.record098_result⟩)
 (.leaf ⟨(32, 12923829422096), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00033.record099_result⟩))))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (30086 + i))) 0 100 :=
  interval_of_check _ 0 100 (by decide +kernel)

public theorem complete : Block 30086 30186 :=
  block_of_table results 30086 100 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0998
