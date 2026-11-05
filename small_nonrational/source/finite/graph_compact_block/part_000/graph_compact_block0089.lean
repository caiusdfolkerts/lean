module
prelude
import GraphInputsRow23Part00011Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0089
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 50
 (.branch 25
 (.branch 12
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(23, 19093952397312), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00011.record000_result⟩)
 (.branch 2
 (.leaf ⟨(23, 19244853002496), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00011.record001_result⟩)
 (.leaf ⟨(23, 19246999437568), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00011.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(23, 19280284647680), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00011.record003_result⟩)
 (.branch 5
 (.leaf ⟨(23, 19281857282304), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00011.record004_result⟩)
 (.leaf ⟨(23, 19294748442624), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00011.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(23, 19297959706880), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00011.record006_result⟩)
 (.branch 8
 (.leaf ⟨(23, 19329041072128), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00011.record007_result⟩)
 (.leaf ⟨(23, 19330171961600), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00011.record008_result⟩)))
 (.branch 10
 (.leaf ⟨(23, 19366280233216), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00011.record009_result⟩)
 (.branch 11
 (.leaf ⟨(23, 19366817103872), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00011.record010_result⟩)
 (.leaf ⟨(23, 19366825426944), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00011.record011_result⟩)))))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf ⟨(23, 19426816622592), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00011.record012_result⟩)
 (.branch 14
 (.leaf ⟨(23, 19434865492224), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00011.record013_result⟩)
 (.leaf ⟨(23, 19435402362880), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00011.record014_result⟩)))
 (.branch 16
 (.leaf ⟨(23, 19435410685952), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00011.record015_result⟩)
 (.branch 17
 (.leaf ⟨(23, 19435534483456), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00011.record016_result⟩)
 (.leaf ⟨(23, 19469762101248), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00011.record017_result⟩))))
 (.branch 21
 (.branch 19
 (.leaf ⟨(23, 19503723380736), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00011.record018_result⟩)
 (.branch 20
 (.leaf ⟨(23, 19504260186112), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00011.record019_result⟩)
 (.leaf ⟨(23, 19512581685248), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00011.record020_result⟩)))
 (.branch 23
 (.branch 22
 (.leaf ⟨(23, 19534796849152), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00011.record021_result⟩)
 (.leaf ⟨(23, 19564251381760), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00011.record022_result⟩))
 (.branch 24
 (.leaf ⟨(23, 19564259704832), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00011.record023_result⟩)
 (.leaf ⟨(23, 19572837057152), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00011.record024_result⟩))))))
 (.branch 37
 (.branch 31
 (.branch 28
 (.branch 26
 (.leaf ⟨(23, 19573914992640), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00011.record025_result⟩)
 (.branch 27
 (.leaf ⟨(23, 19586326233344), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00011.record026_result⟩)
 (.leaf ⟨(23, 19588947443712), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00011.record027_result⟩)))
 (.branch 29
 (.leaf ⟨(23, 19592068005888), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00011.record028_result⟩)
 (.branch 30
 (.leaf ⟨(23, 19610889912576), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00011.record029_result⟩)
 (.leaf ⟨(23, 19611627044864), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00011.record030_result⟩))))
 (.branch 34
 (.branch 32
 (.leaf ⟨(23, 19619561898240), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00011.record031_result⟩)
 (.branch 33
 (.leaf ⟨(23, 19619574188032), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00011.record032_result⟩)
 (.leaf ⟨(23, 19623978270976), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00011.record033_result⟩)))
 (.branch 35
 (.leaf ⟨(23, 19623982532608), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00011.record034_result⟩)
 (.branch 36
 (.leaf ⟨(23, 19624263483392), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00011.record035_result⟩)
 (.leaf ⟨(23, 19632572399616), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00011.record036_result⟩)))))
 (.branch 43
 (.branch 40
 (.branch 38
 (.leaf ⟨(23, 19633109204992), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00011.record037_result⟩)
 (.branch 39
 (.leaf ⟨(23, 19637261860864), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00011.record038_result⟩)
 (.leaf ⟨(23, 19645318889472), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00011.record039_result⟩)))
 (.branch 41
 (.leaf ⟨(23, 19645987815424), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00011.record040_result⟩)
 (.branch 42
 (.leaf ⟨(23, 19649752203264), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00011.record041_result⟩)
 (.leaf ⟨(23, 19650280685568), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00011.record042_result⟩))))
 (.branch 46
 (.branch 44
 (.leaf ⟨(23, 19701694464000), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00011.record043_result⟩)
 (.branch 45
 (.leaf ⟨(23, 19709743398912), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00011.record044_result⟩)
 (.leaf ⟨(23, 19710412324864), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00011.record045_result⟩)))
 (.branch 48
 (.branch 47
 (.leaf ⟨(23, 19718337462272), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00011.record046_result⟩)
 (.leaf ⟨(23, 19718865944576), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00011.record047_result⟩))
 (.branch 49
 (.leaf ⟨(23, 19724775784704), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00011.record048_result⟩)
 (.leaf ⟨(23, 19729209163776), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00011.record049_result⟩)))))))
 (.branch 75
 (.branch 62
 (.branch 56
 (.branch 53
 (.branch 51
 (.leaf ⟨(23, 19729745969152), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00011.record050_result⟩)
 (.branch 52
 (.leaf ⟨(23, 19733369913344), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00011.record051_result⟩)
 (.leaf ⟨(23, 19733906718720), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00011.record052_result⟩)))
 (.branch 54
 (.leaf ⟨(23, 19741955653632), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00011.record053_result⟩)
 (.branch 55
 (.leaf ⟨(23, 19742228217856), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00011.record054_result⟩)
 (.leaf ⟨(23, 19742624579584), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00011.record055_result⟩))))
 (.branch 59
 (.branch 57
 (.leaf ⟨(23, 19748328898560), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00011.record056_result⟩)
 (.branch 58
 (.leaf ⟨(23, 19878595534976), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00011.record057_result⟩)
 (.leaf ⟨(23, 19901406281984), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00011.record058_result⟩)))
 (.branch 60
 (.leaf ⟨(23, 19901414670336), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00011.record059_result⟩)
 (.branch 61
 (.leaf ⟨(23, 19905707540480), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00011.record060_result⟩)
 (.leaf ⟨(23, 19907787915264), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00011.record061_result⟩)))))
 (.branch 68
 (.branch 65
 (.branch 63
 (.leaf ⟨(23, 20038845267968), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00011.record062_result⟩)
 (.branch 64
 (.leaf ⟨(23, 20175747318016), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00011.record063_result⟩)
 (.leaf ⟨(23, 20176015785984), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00011.record064_result⟩)))
 (.branch 66
 (.leaf ⟨(23, 20176284188672), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00011.record065_result⟩)
 (.branch 67
 (.leaf ⟨(23, 20192927186944), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00011.record066_result⟩)
 (.leaf ⟨(23, 20193195589632), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00011.record067_result⟩))))
 (.branch 71
 (.branch 69
 (.leaf ⟨(23, 20199436713984), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00011.record068_result⟩)
 (.branch 70
 (.leaf ⟨(23, 20278893674496), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00011.record069_result⟩)
 (.leaf ⟨(23, 20346675663104), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00011.record070_result⟩)))
 (.branch 73
 (.branch 72
 (.leaf ⟨(23, 20381100474624), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00011.record071_result⟩)
 (.leaf ⟨(23, 20381368877312), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00011.record072_result⟩))
 (.branch 74
 (.leaf ⟨(23, 20381377265664), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00011.record073_result⟩)
 (.leaf ⟨(23, 20385670135808), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00011.record074_result⟩))))))
 (.branch 87
 (.branch 81
 (.branch 78
 (.branch 76
 (.leaf ⟨(23, 20388881400064), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00011.record075_result⟩)
 (.branch 77
 (.leaf ⟨(23, 20393991634944), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00011.record076_result⟩)
 (.leaf ⟨(23, 20412123582720), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00011.record077_result⟩)))
 (.branch 79
 (.leaf ⟨(23, 20415661506816), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00011.record078_result⟩)
 (.branch 80
 (.leaf ⟨(23, 20415669895168), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00011.record079_result⟩)
 (.leaf ⟨(23, 20419962765312), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00011.record080_result⟩))))
 (.branch 84
 (.branch 82
 (.leaf ⟨(23, 20423174029568), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00011.record081_result⟩)
 (.branch 83
 (.leaf ⟨(23, 20428143755520), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00011.record082_result⟩)
 (.leaf ⟨(23, 20428152143872), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00011.record083_result⟩)))
 (.branch 85
 (.leaf ⟨(23, 20428284264448), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00011.record084_result⟩)
 (.branch 86
 (.leaf ⟨(23, 20428350324736), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00011.record085_result⟩)
 (.leaf ⟨(23, 20428544311424), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00011.record086_result⟩)))))
 (.branch 93
 (.branch 90
 (.branch 88
 (.leaf ⟨(23, 20429683589248), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00011.record087_result⟩)
 (.branch 89
 (.leaf ⟨(23, 20496869523456), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00011.record088_result⟩)
 (.leaf ⟨(23, 20525787185408), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00011.record089_result⟩)))
 (.branch 91
 (.leaf ⟨(23, 20526059814912), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00011.record090_result⟩)
 (.branch 92
 (.leaf ⟨(23, 20526456176640), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00011.record091_result⟩)
 (.leaf ⟨(23, 20622688682240), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00011.record092_result⟩))))
 (.branch 96
 (.branch 94
 (.leaf ⟨(23, 20634304282624), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00011.record093_result⟩)
 (.branch 95
 (.leaf ⟨(23, 20687922168064), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00011.record094_result⟩)
 (.leaf ⟨(23, 20688190636032), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00011.record095_result⟩)))
 (.branch 98
 (.branch 97
 (.leaf ⟨(23, 20688198959104), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00011.record096_result⟩)
 (.leaf ⟨(23, 20688459038720), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00011.record097_result⟩))
 (.branch 99
 (.leaf ⟨(23, 20688591159296), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00011.record098_result⟩)
 (.leaf ⟨(23, 20690271010816), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00011.record099_result⟩))))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (6612 + i))) 0 100 :=
  interval_of_check _ 0 100 (by decide +kernel)

public theorem complete : Block 6612 6712 :=
  block_of_table results 6612 100 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0089
