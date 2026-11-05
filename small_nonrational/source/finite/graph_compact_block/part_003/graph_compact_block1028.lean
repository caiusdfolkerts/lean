module
prelude
import GraphInputsSix0Part00063Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock1028
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 50
 (.branch 25
 (.branch 12
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(32, 24319984943104), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00063.record000_result⟩)
 (.branch 2
 (.leaf ⟨(32, 24333351129344), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00063.record001_result⟩)
 (.leaf ⟨(32, 24333483249920), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00063.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(32, 24333549310208), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00063.record003_result⟩)
 (.branch 5
 (.leaf ⟨(32, 24333753782336), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00063.record004_result⟩)
 (.leaf ⟨(32, 24336562979072), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00063.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(32, 24336569221376), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00063.record006_result⟩)
 (.branch 8
 (.leaf ⟨(32, 24336569286656), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00063.record007_result⟩)
 (.leaf ⟨(32, 24336971874368), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00063.record008_result⟩)))
 (.branch 10
 (.leaf ⟨(32, 24336972914752), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00063.record009_result⟩)
 (.branch 11
 (.leaf ⟨(32, 24338046652480), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00063.record010_result⟩)
 (.leaf ⟨(32, 24345152880896), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00063.record011_result⟩)))))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf ⟨(32, 24345152946176), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00063.record012_result⟩)
 (.branch 14
 (.leaf ⟨(32, 24345154961664), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00063.record013_result⟩)
 (.leaf ⟨(32, 24345155026944), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00063.record014_result⟩)))
 (.branch 16
 (.leaf ⟨(32, 24345162293312), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00063.record015_result⟩)
 (.branch 17
 (.leaf ⟨(32, 24345293373504), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00063.record016_result⟩)
 (.leaf ⟨(32, 24345294413888), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00063.record017_result⟩))))
 (.branch 21
 (.branch 19
 (.leaf ⟨(32, 24345558655040), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00063.record018_result⟩)
 (.branch 20
 (.leaf ⟨(32, 24346632392768), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00063.record019_result⟩)
 (.leaf ⟨(32, 24366760919296), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00063.record020_result⟩)))
 (.branch 23
 (.branch 22
 (.leaf ⟨(32, 24366769307648), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00063.record021_result⟩)
 (.leaf ⟨(32, 24367029321984), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00063.record022_result⟩))
 (.branch 24
 (.leaf ⟨(32, 24367033548800), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00063.record023_result⟩)
 (.leaf ⟨(32, 24367039791104), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00063.record024_result⟩))))))
 (.branch 37
 (.branch 31
 (.branch 28
 (.branch 26
 (.leaf ⟨(32, 24367229583616), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00063.record025_result⟩)
 (.branch 27
 (.leaf ⟨(32, 24371390333184), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00063.record026_result⟩)
 (.leaf ⟨(32, 24372473495553), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00063.record027_result⟩)))
 (.branch 29
 (.leaf ⟨(32, 24375082418432), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00063.record028_result⟩)
 (.branch 30
 (.leaf ⟨(32, 24375222927360), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00063.record029_result⟩)
 (.leaf ⟨(32, 24375619289088), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00063.record030_result⟩))))
 (.branch 34
 (.branch 32
 (.leaf ⟨(32, 24375627612160), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00063.record031_result⟩)
 (.branch 33
 (.leaf ⟨(32, 24379711832320), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00063.record032_result⟩)
 (.leaf ⟨(32, 24380114485312), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00063.record033_result⟩)))
 (.branch 35
 (.leaf ⟨(32, 24380794994689), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00063.record034_result⟩)
 (.branch 36
 (.leaf ⟨(32, 24383672320256), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00063.record035_result⟩)
 (.leaf ⟨(32, 24383808667648), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00063.record036_result⟩)))))
 (.branch 43
 (.branch 40
 (.branch 38
 (.leaf ⟨(32, 24383816990720), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00063.record037_result⟩)
 (.branch 39
 (.leaf ⟨(32, 24383940788224), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00063.record038_result⟩)
 (.leaf ⟨(32, 24383949111296), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00063.record039_result⟩)))
 (.branch 41
 (.leaf ⟨(32, 24384409452544), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00063.record040_result⟩)
 (.branch 42
 (.leaf ⟨(32, 24384477593600), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00063.record041_result⟩)
 (.leaf ⟨(32, 24387967271168), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00063.record042_result⟩))))
 (.branch 46
 (.branch 44
 (.leaf ⟨(32, 24388101537792), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00063.record043_result⟩)
 (.branch 45
 (.leaf ⟨(32, 24388109860864), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00063.record044_result⟩)
 (.leaf ⟨(32, 24388504141824), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00063.record045_result⟩)))
 (.branch 48
 (.branch 47
 (.leaf ⟨(32, 24388570202112), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00063.record046_result⟩)
 (.leaf ⟨(32, 24391690764288), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00063.record047_result⟩))
 (.branch 49
 (.leaf ⟨(32, 24398973174016), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00063.record048_result⟩)
 (.leaf ⟨(32, 24399241576704), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00063.record049_result⟩)))))))
 (.branch 75
 (.branch 62
 (.branch 56
 (.branch 53
 (.branch 51
 (.leaf ⟨(32, 24399252045824), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00063.record050_result⟩)
 (.branch 52
 (.leaf ⟨(32, 24405691351040), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00063.record051_result⟩)
 (.leaf ⟨(32, 24414012850176), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00063.record052_result⟩)))
 (.branch 54
 (.leaf ⟨(32, 24415884574976), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00063.record053_result⟩)
 (.branch 55
 (.leaf ⟨(32, 24416020922368), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00063.record054_result⟩)
 (.leaf ⟨(32, 24423434354688), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00063.record055_result⟩))))
 (.branch 59
 (.branch 57
 (.leaf ⟨(32, 24423442677760), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00063.record056_result⟩)
 (.branch 58
 (.leaf ⟨(32, 24432076718336), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00063.record057_result⟩)
 (.leaf ⟨(32, 24432085106688), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00063.record058_result⟩)))
 (.branch 60
 (.leaf ⟨(32, 24432208838912), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00063.record059_result⟩)
 (.branch 61
 (.leaf ⟨(32, 24432217227264), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00063.record060_result⟩)
 (.leaf ⟨(32, 24432324444416), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00063.record061_result⟩)))))
 (.branch 68
 (.branch 65
 (.branch 63
 (.leaf ⟨(32, 24432477241600), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00063.record062_result⟩)
 (.branch 64
 (.leaf ⟨(32, 24432481468416), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00063.record063_result⟩)
 (.leaf ⟨(32, 24432487710720), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00063.record064_result⟩)))
 (.branch 66
 (.leaf ⟨(32, 24432592847104), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00063.record065_result⟩)
 (.branch 67
 (.leaf ⟨(32, 24432605136896), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00063.record066_result⟩)
 (.leaf ⟨(32, 24432727048448), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00063.record067_result⟩))))
 (.branch 71
 (.branch 69
 (.leaf ⟨(32, 24436891779072), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00063.record068_result⟩)
 (.branch 70
 (.leaf ⟨(32, 24437021737728), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00063.record069_result⟩)
 (.leaf ⟨(32, 24438565568768), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00063.record070_result⟩)))
 (.branch 73
 (.branch 72
 (.leaf ⟨(32, 24438918627584), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00063.record071_result⟩)
 (.leaf ⟨(32, 24438920773632), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00063.record072_result⟩))
 (.branch 74
 (.leaf ⟨(32, 24438927015936), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00063.record073_result⟩)
 (.leaf ⟨(32, 24438968172800), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00063.record074_result⟩))))))
 (.branch 87
 (.branch 81
 (.branch 78
 (.branch 76
 (.leaf ⟨(32, 24438978381824), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00063.record075_result⟩)
 (.branch 77
 (.leaf ⟨(32, 24441182487296), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00063.record076_result⟩)
 (.leaf ⟨(32, 24443262862080), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00063.record077_result⟩)))
 (.branch 79
 (.leaf ⟨(32, 24447155470592), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00063.record078_result⟩)
 (.branch 80
 (.leaf ⟨(32, 24447167760384), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00063.record079_result⟩)
 (.leaf ⟨(32, 24447289671936), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00063.record080_result⟩))))
 (.branch 84
 (.branch 82
 (.leaf ⟨(32, 24447299880960), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00063.record081_result⟩)
 (.branch 83
 (.leaf ⟨(32, 24447365941248), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00063.record082_result⟩)
 (.leaf ⟨(32, 24447512756224), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00063.record083_result⟩)))
 (.branch 85
 (.leaf ⟨(32, 24447759425600), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00063.record084_result⟩)
 (.branch 86
 (.leaf ⟨(32, 24449906639424), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00063.record085_result⟩)
 (.leaf ⟨(32, 24457691414784), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00063.record086_result⟩)))))
 (.branch 93
 (.branch 90
 (.branch 88
 (.leaf ⟨(32, 24457825681408), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00063.record087_result⟩)
 (.branch 89
 (.leaf ⟨(32, 24457834004480), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00063.record088_result⟩)
 (.leaf ⟨(32, 24458228285440), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00063.record089_result⟩)))
 (.branch 91
 (.leaf ⟨(32, 24458362356224), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00063.record090_result⟩)
 (.branch 92
 (.leaf ⟨(32, 24467525894400), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00063.record091_result⟩)
 (.leaf ⟨(32, 24470918009088), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00063.record092_result⟩))))
 (.branch 96
 (.branch 94
 (.leaf ⟨(32, 24471761092608), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00063.record093_result⟩)
 (.branch 95
 (.leaf ⟨(32, 24471827152896), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00063.record094_result⟩)
 (.leaf ⟨(32, 24484705763328), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00063.record095_result⟩)))
 (.branch 98
 (.branch 97
 (.leaf ⟨(32, 24499721371904), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00063.record096_result⟩)
 (.leaf ⟨(32, 24499779012736), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00063.record097_result⟩))
 (.branch 99
 (.leaf ⟨(32, 24502123692032), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00063.record098_result⟩)
 (.leaf ⟨(32, 24502899574912), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00063.record099_result⟩))))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (33020 + i))) 0 100 :=
  interval_of_check _ 0 100 (by decide +kernel)

public theorem complete : Block 33020 33120 :=
  block_of_table results 33020 100 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock1028
