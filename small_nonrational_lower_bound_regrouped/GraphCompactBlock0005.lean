module
prelude
import GraphInputsRow16Part00005Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0005
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 48
 (.branch 24
 (.branch 12
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(16, 12578220673280), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00005.record000_result⟩)
 (.branch 2
 (.leaf ⟨(16, 12580250722560), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00005.record001_result⟩)
 (.leaf ⟨(16, 12582448594944), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00005.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(16, 12584461797632), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00005.record003_result⟩)
 (.branch 5
 (.leaf ⟨(16, 12625467408384), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00005.record004_result⟩)
 (.leaf ⟨(16, 12692043600128), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00005.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(16, 12724255854848), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00005.record006_result⟩)
 (.branch 8
 (.leaf ⟨(16, 12757541912576), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00005.record007_result⟩)
 (.leaf ⟨(16, 12821966422016), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00005.record008_result⟩)))
 (.branch 10
 (.leaf ⟨(16, 12830824726528), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00005.record009_result⟩)
 (.branch 11
 (.leaf ⟨(16, 12831088967680), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00005.record010_result⟩)
 (.leaf ⟨(16, 12846650425344), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00005.record011_result⟩)))))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf ⟨(16, 12854178676736), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00005.record012_result⟩)
 (.branch 14
 (.leaf ⟨(16, 12856259051520), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00005.record013_result⟩)
 (.leaf ⟨(16, 12860419801088), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00005.record014_result⟩)))
 (.branch 16
 (.leaf ⟨(16, 12865381597184), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00005.record015_result⟩)
 (.branch 17
 (.leaf ⟨(16, 12866157543424), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00005.record016_result⟩)
 (.leaf ⟨(16, 12866380431360), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00005.record017_result⟩))))
 (.branch 21
 (.branch 19
 (.leaf ⟨(16, 12877863845888), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00005.record018_result⟩)
 (.branch 20
 (.leaf ⟨(16, 12878862680064), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00005.record019_result⟩)
 (.leaf ⟨(16, 12889494716416), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00005.record020_result⟩)))
 (.branch 22
 (.leaf ⟨(16, 12898592097024), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00005.record021_result⟩)
 (.branch 23
 (.leaf ⟨(16, 12915235291136), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00005.record022_result⟩)
 (.leaf ⟨(16, 13060330815488), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00005.record023_result⟩))))))
 (.branch 36
 (.branch 30
 (.branch 27
 (.branch 25
 (.leaf ⟨(16, 13062411190272), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00005.record024_result⟩)
 (.branch 26
 (.leaf ⟨(16, 13066571939840), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00005.record025_result⟩)
 (.leaf ⟨(16, 13072136208384), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00005.record026_result⟩)))
 (.branch 28
 (.leaf ⟨(16, 13095646855168), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00005.record027_result⟩)
 (.branch 29
 (.leaf ⟨(16, 13104347874048), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00005.record028_result⟩)
 (.leaf ⟨(16, 13127859109888), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00005.record029_result⟩))))
 (.branch 33
 (.branch 31
 (.leaf ⟨(16, 13130005544960), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00005.record030_result⟩)
 (.branch 32
 (.leaf ⟨(16, 13134298415104), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00005.record031_result⟩)
 (.leaf ⟨(16, 13137642258432), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00005.record032_result⟩)))
 (.branch 34
 (.leaf ⟨(16, 13168772710400), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00005.record033_result⟩)
 (.branch 35
 (.leaf ⟨(16, 13172958298112), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00005.record034_result⟩)
 (.leaf ⟨(16, 13387218092032), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00005.record035_result⟩)))))
 (.branch 42
 (.branch 39
 (.branch 37
 (.leaf ⟨(16, 13387224334336), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00005.record036_result⟩)
 (.branch 38
 (.leaf ⟨(16, 13393663639552), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00005.record037_result⟩)
 (.leaf ⟨(16, 13394431197440), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00005.record038_result⟩)))
 (.branch 40
 (.leaf ⟨(16, 13441716748544), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00005.record039_result⟩)
 (.branch 41
 (.leaf ⟨(16, 13441716813824), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00005.record040_result⟩)
 (.leaf ⟨(16, 13446009683968), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00005.record041_result⟩))))
 (.branch 45
 (.branch 43
 (.leaf ⟨(16, 13450306715648), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00005.record042_result⟩)
 (.branch 44
 (.leaf ⟨(16, 13454595424256), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00005.record043_result⟩)
 (.leaf ⟨(16, 13458628214784), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00005.record044_result⟩)))
 (.branch 46
 (.leaf ⟨(16, 13459086409984), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00005.record045_result⟩)
 (.branch 47
 (.leaf ⟨(16, 13459097919488), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00005.record046_result⟩)
 (.leaf ⟨(16, 13459156697088), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00005.record047_result⟩)))))))
 (.branch 72
 (.branch 60
 (.branch 54
 (.branch 51
 (.branch 49
 (.leaf ⟨(16, 13459165020160), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00005.record048_result⟩)
 (.branch 50
 (.leaf ⟨(16, 13462780576000), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00005.record049_result⟩)
 (.leaf ⟨(16, 13462788964352), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00005.record050_result⟩)))
 (.branch 52
 (.leaf ⟨(16, 13462921084928), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00005.record051_result⟩)
 (.branch 53
 (.leaf ⟨(16, 13462978756864), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00005.record052_result⟩)
 (.leaf ⟨(16, 13463181099264), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00005.record053_result⟩))))
 (.branch 57
 (.branch 55
 (.leaf ⟨(16, 13463185326080), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00005.record054_result⟩)
 (.branch 56
 (.leaf ⟨(16, 13463247159552), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00005.record055_result⟩)
 (.leaf ⟨(16, 13463258669056), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00005.record056_result⟩)))
 (.branch 58
 (.leaf ⟨(16, 13463515627520), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00005.record057_result⟩)
 (.branch 59
 (.leaf ⟨(16, 13463523950592), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00005.record058_result⟩)
 (.leaf ⟨(16, 13465067520000), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00005.record059_result⟩)))))
 (.branch 66
 (.branch 63
 (.branch 61
 (.leaf ⟨(16, 13465339043840), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00005.record060_result⟩)
 (.branch 62
 (.leaf ⟨(16, 13531601715456), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00005.record061_result⟩)
 (.leaf ⟨(16, 13600355844096), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00005.record062_result⟩)))
 (.branch 64
 (.leaf ⟨(16, 13602502279168), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00005.record063_result⟩)
 (.branch 65
 (.leaf ⟨(16, 13634479603968), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00005.record064_result⟩)
 (.leaf ⟨(16, 13635247685632), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00005.record065_result⟩))))
 (.branch 69
 (.branch 67
 (.leaf ⟨(16, 13647472525568), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00005.record066_result⟩)
 (.branch 68
 (.leaf ⟨(16, 13647600484608), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00005.record067_result⟩)
 (.leaf ⟨(16, 13647604646144), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00005.record068_result⟩)))
 (.branch 70
 (.leaf ⟨(16, 13647604711424), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00005.record069_result⟩)
 (.branch 71
 (.leaf ⟨(16, 13647673827584), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00005.record070_result⟩)
 (.leaf ⟨(16, 13671083311360), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00005.record071_result⟩))))))
 (.branch 84
 (.branch 78
 (.branch 75
 (.branch 73
 (.leaf ⟨(16, 13671087538176), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00005.record072_result⟩)
 (.branch 74
 (.leaf ⟨(16, 13671094820864), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00005.record073_result⟩)
 (.leaf ⟨(16, 13681963401216), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00005.record074_result⟩)))
 (.branch 76
 (.leaf ⟨(16, 13822895161376), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00005.record075_result⟩)
 (.branch 77
 (.leaf ⟨(16, 13823968903184), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00005.record076_result⟩)
 (.leaf ⟨(16, 13874157912320), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00005.record077_result⟩))))
 (.branch 81
 (.branch 79
 (.leaf ⟨(16, 13874166300672), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00005.record078_result⟩)
 (.branch 80
 (.leaf ⟨(16, 13874694782976), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00005.record079_result⟩)
 (.leaf ⟨(16, 13874703106048), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00005.record080_result⟩)))
 (.branch 82
 (.leaf ⟨(16, 13922719531264), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00005.record081_result⟩)
 (.branch 83
 (.leaf ⟨(16, 13922719596544), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00005.record082_result⟩)
 (.leaf ⟨(16, 13927012466688), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00005.record083_result⟩)))))
 (.branch 90
 (.branch 87
 (.branch 85
 (.leaf ⟨(16, 13931573739520), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00005.record084_result⟩)
 (.branch 86
 (.leaf ⟨(16, 13934362894592), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00005.record085_result⟩)
 (.leaf ⟨(16, 13934558019584), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00005.record086_result⟩)))
 (.branch 88
 (.leaf ⟨(16, 13936510435328), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00005.record087_result⟩)
 (.branch 89
 (.leaf ⟨(16, 13937038917632), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00005.record088_result⟩)
 (.leaf ⟨(16, 13937047240704), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00005.record089_result⟩))))
 (.branch 93
 (.branch 91
 (.leaf ⟨(16, 13939049005312), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00005.record090_result⟩)
 (.branch 92
 (.leaf ⟨(16, 13939060514816), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00005.record091_result⟩)
 (.leaf ⟨(16, 13939119292416), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00005.record092_result⟩)))
 (.branch 94
 (.leaf ⟨(16, 13939127615488), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00005.record093_result⟩)
 (.branch 95
 (.leaf ⟨(16, 13940159479808), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00005.record094_result⟩)
 (.leaf ⟨(16, 13940167802880), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00005.record095_result⟩))))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (408 + i))) 0 96 :=
  interval_of_check _ 0 96 (by decide +kernel)

public theorem complete : Block 408 504 :=
  block_of_table results 408 96 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0005
