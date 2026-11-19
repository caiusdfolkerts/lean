module
prelude
import GraphInputsRow19Part00015Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0055
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 50
 (.branch 25
 (.branch 12
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(19, 18894142054464), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00015.record000_result⟩)
 (.branch 2
 (.leaf ⟨(19, 18904874303744), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00015.record001_result⟩)
 (.leaf ⟨(19, 18913468432384), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00015.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(19, 18916454776896), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00015.record003_result⟩)
 (.branch 5
 (.leaf ⟨(19, 18920749678848), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00015.record004_result⟩)
 (.leaf ⟨(19, 18921156509696), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00015.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(19, 18921278161152), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00015.record006_result⟩)
 (.branch 8
 (.leaf ⟨(19, 18921280307200), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00015.record007_result⟩)
 (.leaf ⟨(19, 18921286549504), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00015.record008_result⟩)))
 (.branch 10
 (.leaf ⟨(19, 18921585443072), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00015.record009_result⟩)
 (.branch 11
 (.leaf ⟨(19, 18921589669888), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00015.record010_result⟩)
 (.leaf ⟨(19, 18921822896384), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00015.record011_result⟩)))))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf ⟨(19, 18921822961664), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00015.record012_result⟩)
 (.branch 14
 (.leaf ⟨(19, 18922058334208), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00015.record013_result⟩)
 (.leaf ⟨(19, 18922061439040), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00015.record014_result⟩)))
 (.branch 16
 (.leaf ⟨(19, 18922318348544), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00015.record015_result⟩)
 (.branch 17
 (.leaf ⟨(19, 18922320494592), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00015.record016_result⟩)
 (.leaf ⟨(19, 18922326736896), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00015.record017_result⟩))))
 (.branch 21
 (.branch 19
 (.leaf ⟨(19, 18924910493696), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00015.record018_result⟩)
 (.branch 20
 (.leaf ⟨(19, 18925884620800), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00015.record019_result⟩)
 (.leaf ⟨(19, 18926354309184), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00015.record020_result⟩)))
 (.branch 23
 (.branch 22
 (.leaf ⟨(19, 18936805540096), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00015.record021_result⟩)
 (.leaf ⟨(19, 18941420322824), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00015.record022_result⟩))
 (.branch 24
 (.leaf ⟨(19, 18955976769792), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00015.record023_result⟩)
 (.leaf ⟨(19, 18955980931328), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00015.record024_result⟩))))))
 (.branch 37
 (.branch 31
 (.branch 28
 (.branch 26
 (.leaf ⟨(19, 18955980996608), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00015.record025_result⟩)
 (.branch 27
 (.leaf ⟨(19, 18955984962816), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00015.record026_result⟩)
 (.leaf ⟨(19, 18956115197952), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00015.record027_result⟩)))
 (.branch 29
 (.leaf ⟨(19, 18956117083392), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00015.record028_result⟩)
 (.branch 30
 (.leaf ⟨(19, 18956383600640), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00015.record029_result⟩)
 (.leaf ⟨(19, 18956521832449), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00015.record030_result⟩))))
 (.branch 34
 (.branch 32
 (.leaf ⟨(19, 18956777685760), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00015.record031_result⟩)
 (.branch 33
 (.leaf ⟨(19, 18956786074112), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00015.record032_result⟩)
 (.leaf ⟨(19, 18960275947520), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00015.record033_result⟩)))
 (.branch 35
 (.leaf ⟨(19, 18962356322304), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00015.record034_result⟩)
 (.branch 36
 (.leaf ⟨(19, 18962423422976), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00015.record035_result⟩)
 (.leaf ⟨(19, 18962424268032), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00015.record036_result⟩)))))
 (.branch 43
 (.branch 40
 (.branch 38
 (.leaf ⟨(19, 18962826027008), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00015.record037_result⟩)
 (.branch 39
 (.leaf ⟨(19, 18962895077377), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00015.record038_result⟩)
 (.leaf ⟨(19, 18974203003008), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00015.record039_result⟩)))
 (.branch 41
 (.leaf ⟨(19, 19006645944576), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00015.record040_result⟩)
 (.branch 42
 (.leaf ⟨(19, 19015240007936), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00015.record041_result⟩)
 (.leaf ⟨(19, 19015240073216), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00015.record042_result⟩))))
 (.branch 46
 (.branch 44
 (.leaf ⟨(19, 19015374274560), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00015.record043_result⟩)
 (.branch 45
 (.leaf ⟨(19, 19015638515712), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00015.record044_result⟩)
 (.leaf ⟨(19, 19015776878592), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00015.record045_result⟩)))
 (.branch 48
 (.branch 47
 (.leaf ⟨(19, 19015836696576), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00015.record046_result⟩)
 (.leaf ⟨(19, 19016674476288), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00015.record047_result⟩))
 (.branch 49
 (.leaf ⟨(19, 19016678703104), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00015.record048_result⟩)
 (.leaf ⟨(19, 19022496743552), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00015.record049_result⟩)))))))
 (.branch 75
 (.branch 62
 (.branch 56
 (.branch 53
 (.branch 51
 (.leaf ⟨(19, 19023825748224), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00015.record050_result⟩)
 (.branch 52
 (.leaf ⟨(19, 19027986563072), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00015.record051_result⟩)
 (.leaf ⟨(19, 19028192010304), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00015.record052_result⟩)))
 (.branch 54
 (.leaf ⟨(19, 19028719452224), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00015.record053_result⟩)
 (.branch 55
 (.leaf ⟨(19, 19028721549312), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00015.record054_result⟩)
 (.leaf ⟨(19, 19031171104768), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00015.record055_result⟩))))
 (.branch 59
 (.branch 57
 (.leaf ⟨(19, 19031173120256), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00015.record056_result⟩)
 (.branch 58
 (.leaf ⟨(19, 19031173185536), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00015.record057_result⟩)
 (.leaf ⟨(19, 19031180451904), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00015.record058_result⟩)))
 (.branch 60
 (.leaf ⟨(19, 19039126601984), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00015.record059_result⟩)
 (.branch 61
 (.leaf ⟨(19, 19045572198464), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00015.record060_result⟩)
 (.leaf ⟨(19, 19050434461952), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00015.record061_result⟩)))))
 (.branch 68
 (.branch 65
 (.branch 63
 (.leaf ⟨(19, 19050438623488), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00015.record062_result⟩)
 (.branch 64
 (.leaf ⟨(19, 19050438688768), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00015.record063_result⟩)
 (.leaf ⟨(19, 19050440704256), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00015.record064_result⟩)))
 (.branch 66
 (.leaf ⟨(19, 19050638885120), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00015.record065_result⟩)
 (.branch 67
 (.leaf ⟨(19, 19050638950400), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00015.record066_result⟩)
 (.leaf ⟨(19, 19050671980544), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00015.record067_result⟩))))
 (.branch 71
 (.branch 69
 (.leaf ⟨(19, 19050907353088), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00015.record068_result⟩)
 (.branch 70
 (.leaf ⟨(19, 19051167367424), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00015.record069_result⟩)
 (.leaf ⟨(19, 19051169513472), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00015.record070_result⟩)))
 (.branch 73
 (.branch 72
 (.leaf ⟨(19, 19051175755776), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00015.record071_result⟩)
 (.leaf ⟨(19, 19058327027712), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00015.record072_result⟩))
 (.branch 74
 (.leaf ⟨(19, 19062349414400), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00015.record073_result⟩)
 (.leaf ⟨(19, 19062748880960), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00015.record074_result⟩))))))
 (.branch 87
 (.branch 81
 (.branch 78
 (.branch 76
 (.leaf ⟨(19, 19063319314688), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00015.record075_result⟩)
 (.branch 77
 (.leaf ⟨(19, 19063319379968), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00015.record076_result⟩)
 (.leaf ⟨(19, 19064153456640), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00015.record077_result⟩)))
 (.branch 79
 (.leaf ⟨(19, 19072362266880), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00015.record078_result⟩)
 (.branch 80
 (.leaf ⟨(19, 19074508701952), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00015.record079_result⟩)
 (.leaf ⟨(19, 19078801572096), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00015.record080_result⟩))))
 (.branch 84
 (.branch 82
 (.leaf ⟨(19, 19078807863360), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00015.record081_result⟩)
 (.branch 83
 (.leaf ⟨(19, 19097985220609), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00015.record082_result⟩)
 (.leaf ⟨(19, 19098511606336), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00015.record083_result⟩)))
 (.branch 85
 (.leaf ⟨(19, 19098513703424), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00015.record084_result⟩)
 (.branch 86
 (.leaf ⟨(19, 19099789000704), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00015.record085_result⟩)
 (.leaf ⟨(19, 19099792966912), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00015.record086_result⟩)))))
 (.branch 93
 (.branch 90
 (.branch 88
 (.leaf ⟨(19, 19099799258176), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00015.record087_result⟩)
 (.branch 89
 (.leaf ⟨(19, 19099859027200), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00015.record088_result⟩)
 (.leaf ⟨(19, 19099933474817), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00015.record089_result⟩)))
 (.branch 91
 (.leaf ⟨(19, 19099991147776), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00015.record090_result⟩)
 (.branch 92
 (.leaf ⟨(19, 19099996528704), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00015.record091_result⟩)
 (.leaf ⟨(19, 19099996545024), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00015.record092_result⟩))))
 (.branch 96
 (.branch 94
 (.leaf ⟨(19, 19100065595393), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00015.record093_result⟩)
 (.branch 95
 (.leaf ⟨(19, 19119224209408), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00015.record094_result⟩)
 (.leaf ⟨(19, 19119257239552), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00015.record095_result⟩)))
 (.branch 98
 (.branch 97
 (.leaf ⟨(19, 19127743824128), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00015.record096_result⟩)
 (.leaf ⟨(19, 19127743889408), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00015.record097_result⟩))
 (.branch 99
 (.leaf ⟨(19, 19127814111232), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00015.record098_result⟩)
 (.leaf ⟨(19, 19127847141376), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00015.record099_result⟩))))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (3565 + i))) 0 100 :=
  interval_of_check _ 0 100 (by decide +kernel)

public theorem complete : Block 3565 3665 :=
  block_of_table results 3565 100 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0055
