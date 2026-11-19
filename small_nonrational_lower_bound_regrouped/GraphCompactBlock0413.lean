module
prelude
import GraphInputsRow27Part00010Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0413
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 50
 (.branch 25
 (.branch 12
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(27, 23014724993024), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00010.record000_result⟩)
 (.branch 2
 (.leaf ⟨(27, 23163321286688), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00010.record001_result⟩)
 (.leaf ⟨(27, 23211883380992), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00010.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(27, 23219736215808), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00010.record003_result⟩)
 (.branch 5
 (.leaf ⟨(27, 23220273086464), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00010.record004_result⟩)
 (.leaf ⟨(27, 23220281409536), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00010.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(27, 23420324544512), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00010.record006_result⟩)
 (.branch 8
 (.leaf ⟨(27, 23421744316416), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00010.record007_result⟩)
 (.leaf ⟨(27, 23422336778240), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00010.record008_result⟩)))
 (.branch 10
 (.leaf ⟨(27, 23422404919296), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00010.record009_result⟩)
 (.branch 11
 (.leaf ⟨(27, 23425894596864), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00010.record010_result⟩)
 (.leaf ⟨(27, 23426028863488), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00010.record011_result⟩)))))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf ⟨(27, 23426037186560), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00010.record012_result⟩)
 (.branch 14
 (.leaf ⟨(27, 23426431467520), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00010.record013_result⟩)
 (.leaf ⟨(27, 23426497527808), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00010.record014_result⟩)))
 (.branch 16
 (.leaf ⟨(27, 23429157748736), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00010.record015_result⟩)
 (.branch 17
 (.leaf ⟨(27, 23429618089984), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00010.record016_result⟩)
 (.leaf ⟨(27, 23437179371520), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00010.record017_result⟩))))
 (.branch 21
 (.branch 19
 (.leaf ⟨(27, 23461361680384), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00010.record018_result⟩)
 (.branch 20
 (.leaf ⟨(27, 23461370003456), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00010.record019_result⟩)
 (.leaf ⟨(27, 23495761330176), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00010.record020_result⟩)))
 (.branch 23
 (.branch 22
 (.leaf ⟨(27, 23505494147072), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00010.record021_result⟩)
 (.leaf ⟨(27, 23505888362752), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00010.record022_result⟩))
 (.branch 24
 (.leaf ⟨(27, 23505896751104), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00010.record023_result⟩)
 (.leaf ⟨(27, 23505954423040), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00010.record024_result⟩))))))
 (.branch 37
 (.branch 31
 (.branch 28
 (.branch 26
 (.leaf ⟨(27, 23508043186176), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00010.record025_result⟩)
 (.branch 27
 (.leaf ⟨(27, 23508713799680), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00010.record026_result⟩)
 (.leaf ⟨(27, 23509074985216), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00010.record027_result⟩)))
 (.branch 29
 (.leaf ⟨(27, 23509083373568), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00010.record028_result⟩)
 (.branch 30
 (.leaf ⟨(27, 23520919699520), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00010.record029_result⟩)
 (.leaf ⟨(27, 23522060017728), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00010.record030_result⟩))))
 (.branch 34
 (.branch 32
 (.leaf ⟨(27, 23525717983488), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00010.record031_result⟩)
 (.branch 33
 (.leaf ⟨(27, 23525786189824), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00010.record032_result⟩)
 (.leaf ⟨(27, 23525794512896), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00010.record033_result⟩)))
 (.branch 35
 (.leaf ⟨(27, 23525893603328), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00010.record034_result⟩)
 (.branch 36
 (.leaf ⟨(27, 23526254854144), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00010.record035_result⟩)
 (.leaf ⟨(27, 23541270462720), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00010.record036_result⟩)))))
 (.branch 43
 (.branch 40
 (.branch 38
 (.leaf ⟨(27, 23541272608768), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00010.record037_result⟩)
 (.branch 39
 (.leaf ⟨(27, 23541278851072), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00010.record038_result⟩)
 (.leaf ⟨(27, 23573491105792), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00010.record039_result⟩)))
 (.branch 41
 (.leaf ⟨(27, 23678717362176), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00010.record040_result⟩)
 (.branch 42
 (.leaf ⟨(27, 23941792940032), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00010.record041_result⟩)
 (.leaf ⟨(27, 24006452314112), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00010.record042_result⟩))))
 (.branch 46
 (.branch 44
 (.leaf ⟨(27, 24053453701120), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00010.record043_result⟩)
 (.branch 45
 (.leaf ⟨(27, 24054520676352), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00010.record044_result⟩)
 (.leaf ⟨(27, 24054526918656), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00010.record045_result⟩)))
 (.branch 48
 (.branch 47
 (.leaf ⟨(27, 24069107877888), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00010.record046_result⟩)
 (.leaf ⟨(27, 24069551964160), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00010.record047_result⟩))
 (.branch 49
 (.leaf ⟨(27, 24086738911232), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00010.record048_result⟩)
 (.leaf ⟨(27, 24103499204608), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00010.record049_result⟩)))))))
 (.branch 75
 (.branch 62
 (.branch 56
 (.branch 53
 (.branch 51
 (.leaf ⟨(27, 24103893469248), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00010.record050_result⟩)
 (.branch 52
 (.leaf ⟨(27, 24208083017856), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00010.record051_result⟩)
 (.leaf ⟨(27, 24293478203400), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00010.record052_result⟩)))
 (.branch 54
 (.leaf ⟨(27, 24319384158208), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00010.record053_result⟩)
 (.branch 55
 (.leaf ⟨(27, 24319392481280), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00010.record054_result⟩)
 (.leaf ⟨(27, 24345152946176), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00010.record055_result⟩))))
 (.branch 59
 (.branch 57
 (.leaf ⟨(27, 24383816990720), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00010.record056_result⟩)
 (.branch 58
 (.leaf ⟨(27, 24384477593600), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00010.record057_result⟩)
 (.leaf ⟨(27, 24388109860864), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00010.record058_result⟩)))
 (.branch 60
 (.leaf ⟨(27, 24399252045824), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00010.record059_result⟩)
 (.branch 61
 (.leaf ⟨(27, 24423434354688), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00010.record060_result⟩)
 (.leaf ⟨(27, 24423442677760), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00010.record061_result⟩)))))
 (.branch 68
 (.branch 65
 (.branch 63
 (.leaf ⟨(27, 24447167760384), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00010.record062_result⟩)
 (.branch 64
 (.leaf ⟨(27, 24457834004480), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00010.record063_result⟩)
 (.leaf ⟨(27, 24458228285440), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00010.record064_result⟩)))
 (.branch 66
 (.leaf ⟨(27, 24471761092608), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00010.record065_result⟩)
 (.branch 67
 (.leaf ⟨(27, 24471827152896), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00010.record066_result⟩)
 (.leaf ⟨(27, 24484705763328), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00010.record067_result⟩))))
 (.branch 71
 (.branch 69
 (.leaf ⟨(27, 24513258471424), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00010.record068_result⟩)
 (.branch 70
 (.leaf ⟨(27, 24513326612480), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00010.record069_result⟩)
 (.leaf ⟨(27, 24515844245632), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00010.record070_result⟩)))
 (.branch 73
 (.branch 72
 (.leaf ⟨(27, 24520021803008), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00010.record071_result⟩)
 (.leaf ⟨(27, 24605404184576), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00010.record072_result⟩))
 (.branch 74
 (.leaf ⟨(27, 24608221233152), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00010.record073_result⟩)
 (.leaf ⟨(27, 24616716206080), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00010.record074_result⟩))))))
 (.branch 87
 (.branch 81
 (.branch 78
 (.branch 76
 (.leaf ⟨(27, 24616815296512), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00010.record075_result⟩)
 (.branch 77
 (.leaf ⟨(27, 24621303210048), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00010.record076_result⟩)
 (.leaf ⟨(27, 24628620689408), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00010.record077_result⟩)))
 (.branch 79
 (.leaf ⟨(27, 24629660876800), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00010.record078_result⟩)
 (.branch 80
 (.leaf ⟨(27, 24640441288704), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00010.record079_result⟩)
 (.leaf ⟨(27, 24640515801088), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00010.record080_result⟩))))
 (.branch 84
 (.branch 82
 (.leaf ⟨(27, 24644723949824), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00010.record081_result⟩)
 (.branch 83
 (.leaf ⟨(27, 24644734158848), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00010.record082_result⟩)
 (.leaf ⟨(27, 24645079154688), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00010.record083_result⟩)))
 (.branch 85
 (.leaf ⟨(27, 24663984062464), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00010.record084_result⟩)
 (.branch 86
 (.leaf ⟨(27, 24663986143232), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00010.record085_result⟩)
 (.leaf ⟨(27, 24665997320256), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00010.record086_result⟩)))))
 (.branch 93
 (.branch 90
 (.branch 88
 (.leaf ⟨(27, 24666064437248), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00010.record087_result⟩)
 (.branch 89
 (.leaf ⟨(27, 24666066518016), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00010.record088_result⟩)
 (.leaf ⟨(27, 24666198508032), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00010.record089_result⟩)))
 (.branch 91
 (.leaf ⟨(27, 24672734298112), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00010.record090_result⟩)
 (.branch 92
 (.leaf ⟨(27, 24676940185600), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00010.record091_result⟩)
 (.leaf ⟨(27, 24739097907472), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00010.record092_result⟩))))
 (.branch 96
 (.branch 94
 (.leaf ⟨(27, 24903865614336), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00010.record093_result⟩)
 (.branch 95
 (.leaf ⟨(27, 24968524988416), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00010.record094_result⟩)
 (.leaf ⟨(27, 25003957420032), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00010.record095_result⟩)))
 (.branch 98
 (.branch 97
 (.leaf ⟨(27, 25152696893440), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00010.record096_result⟩)
 (.leaf ⟨(27, 25153763868672), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00010.record097_result⟩))
 (.branch 99
 (.leaf ⟨(27, 25153770110976), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00010.record098_result⟩)
 (.leaf ⟨(27, 25160472600640), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00010.record099_result⟩))))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (18673 + i))) 0 100 :=
  interval_of_check _ 0 100 (by decide +kernel)

public theorem complete : Block 18673 18773 :=
  block_of_table results 18673 100 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0413
