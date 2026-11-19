module
prelude
import GraphInputsRow23Part00007Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0085
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 50
 (.branch 25
 (.branch 12
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(23, 12650570321920), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00007.record000_result⟩)
 (.branch 2
 (.leaf ⟨(23, 12654359937024), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00007.record001_result⟩)
 (.leaf ⟨(23, 12654619951360), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00007.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(23, 12654624178176), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00007.record003_result⟩)
 (.branch 5
 (.leaf ⟨(23, 12654628339712), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00007.record004_result⟩)
 (.leaf ⟨(23, 12654731071488), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00007.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(23, 12663052570624), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00007.record006_result⟩)
 (.branch 8
 (.leaf ⟨(23, 12663209885824), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00007.record007_result⟩)
 (.leaf ⟨(23, 12663214080000), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00007.record008_result⟩)))
 (.branch 10
 (.leaf ⟨(23, 12663443177600), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00007.record009_result⟩)
 (.branch 11
 (.leaf ⟨(23, 12722255724544), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00007.record010_result⟩)
 (.leaf ⟨(23, 12722259365888), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00007.record011_result⟩)))))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf ⟨(23, 12723312295936), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00007.record012_result⟩)
 (.branch 14
 (.leaf ⟨(23, 12786411831296), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00007.record013_result⟩)
 (.leaf ⟨(23, 12786683875328), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00007.record014_result⟩)))
 (.branch 16
 (.leaf ⟨(23, 12790976745472), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00007.record015_result⟩)
 (.branch 17
 (.leaf ⟨(23, 12792293818368), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00007.record016_result⟩)
 (.leaf ⟨(23, 12795513470976), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00007.record017_result⟩))))
 (.branch 21
 (.branch 19
 (.leaf ⟨(23, 12799405461760), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00007.record018_result⟩)
 (.branch 20
 (.leaf ⟨(23, 12799562485760), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00007.record019_result⟩)
 (.leaf ⟨(23, 12864240746496), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00007.record020_result⟩)))
 (.branch 23
 (.branch 22
 (.leaf ⟨(23, 12923842363648), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00007.record021_result⟩)
 (.leaf ⟨(23, 12923854393344), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00007.record022_result⟩))
 (.branch 24
 (.leaf ⟨(23, 12924110798976), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00007.record023_result⟩)
 (.leaf ⟨(23, 12928147263488), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00007.record024_result⟩))))))
 (.branch 37
 (.branch 31
 (.branch 28
 (.branch 26
 (.leaf ⟨(23, 12928405749888), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00007.record025_result⟩)
 (.branch 27
 (.leaf ⟨(23, 12928411504640), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00007.record026_result⟩)
 (.leaf ⟨(23, 12936844415104), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00007.record027_result⟩)))
 (.branch 29
 (.leaf ⟨(23, 13125705596928), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00007.record028_result⟩)
 (.branch 30
 (.leaf ⟨(23, 13125713920000), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00007.record029_result⟩)
 (.leaf ⟨(23, 13125973999616), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00007.record030_result⟩))))
 (.branch 34
 (.branch 32
 (.leaf ⟨(23, 13126225627136), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00007.record031_result⟩)
 (.branch 33
 (.leaf ⟨(23, 13134303592448), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00007.record032_result⟩)
 (.leaf ⟨(23, 13134546995200), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00007.record033_result⟩)))
 (.branch 35
 (.leaf ⟨(23, 13134563639808), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00007.record034_result⟩)
 (.branch 36
 (.leaf ⟨(23, 13234484641792), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00007.record035_result⟩)
 (.leaf ⟨(23, 13238777511936), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00007.record036_result⟩)))))
 (.branch 43
 (.branch 40
 (.branch 38
 (.leaf ⟨(23, 13247363252224), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00007.record037_result⟩)
 (.branch 39
 (.leaf ⟨(23, 13273136201728), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00007.record038_result⟩)
 (.leaf ⟨(23, 13274176389120), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00007.record039_result⟩)))
 (.branch 41
 (.leaf ⟨(23, 13281726070912), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00007.record040_result⟩)
 (.branch 42
 (.leaf ⟨(23, 13281930518560), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00007.record041_result⟩)
 (.leaf ⟨(23, 13308501655552), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00007.record042_result⟩))))
 (.branch 46
 (.branch 44
 (.leaf ⟨(23, 13308774121472), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00007.record043_result⟩)
 (.branch 45
 (.leaf ⟨(23, 13338600898560), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00007.record044_result⟩)
 (.leaf ⟨(23, 13342895849472), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00007.record045_result⟩)))
 (.branch 48
 (.branch 47
 (.leaf ⟨(23, 13350445531264), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00007.record046_result⟩)
 (.leaf ⟨(23, 13350445563904), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00007.record047_result⟩))
 (.branch 49
 (.leaf ⟨(23, 13369765560576), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00007.record048_result⟩)
 (.leaf ⟨(23, 13377221115904), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00007.record049_result⟩)))))))
 (.branch 75
 (.branch 62
 (.branch 56
 (.branch 53
 (.branch 51
 (.leaf ⟨(23, 13377359380480), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00007.record050_result⟩)
 (.branch 52
 (.leaf ⟨(23, 13377483112704), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00007.record051_result⟩)
 (.leaf ⟨(23, 13383681228800), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00007.record052_result⟩)))
 (.branch 54
 (.leaf ⟨(23, 13385680879616), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00007.record053_result⟩)
 (.branch 55
 (.leaf ⟨(23, 13385871687936), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00007.record054_result⟩)
 (.leaf ⟨(23, 13388230959104), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00007.record055_result⟩))))
 (.branch 59
 (.branch 57
 (.leaf ⟨(23, 13523310641280), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00007.record056_result⟩)
 (.branch 58
 (.leaf ⟨(23, 13660749594624), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00007.record057_result⟩)
 (.leaf ⟨(23, 13890486870016), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00007.record058_result⟩)))
 (.branch 60
 (.leaf ⟨(23, 13899936104448), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00007.record059_result⟩)
 (.branch 61
 (.leaf ⟨(23, 13900405809152), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00007.record060_result⟩)
 (.leaf ⟨(23, 13929392701440), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00007.record061_result⟩)))))
 (.branch 68
 (.branch 65
 (.branch 63
 (.leaf ⟨(23, 13937978441728), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00007.record062_result⟩)
 (.branch 64
 (.leaf ⟨(23, 13937986764800), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00007.record063_result⟩)
 (.leaf ⟨(23, 13976630001664), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00007.record064_result⟩)))
 (.branch 66
 (.leaf ⟨(23, 14027929423904), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00007.record065_result⟩)
 (.branch 67
 (.leaf ⟨(23, 14346870620416), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00007.record066_result⟩)
 (.leaf ⟨(23, 14372579778560), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00007.record067_result⟩))))
 (.branch 71
 (.branch 69
 (.leaf ⟨(23, 14381442146304), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00007.record068_result⟩)
 (.branch 70
 (.leaf ⟨(23, 14449960304640), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00007.record069_result⟩)
 (.leaf ⟨(23, 14450027405312), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00007.record070_result⟩)))
 (.branch 73
 (.branch 72
 (.leaf ⟨(23, 14450150097152), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00007.record071_result⟩)
 (.leaf ⟨(23, 14485584674816), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00007.record072_result⟩))
 (.branch 74
 (.leaf ⟨(23, 14487608360960), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00007.record073_result⟩)
 (.leaf ⟨(23, 14522090848256), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00007.record074_result⟩))))))
 (.branch 87
 (.branch 81
 (.branch 78
 (.branch 76
 (.leaf ⟨(23, 14571853086976), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00007.record075_result⟩)
 (.branch 77
 (.leaf ⟨(23, 14573390270496), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00007.record076_result⟩)
 (.leaf ⟨(23, 14577683140640), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00007.record077_result⟩)))
 (.branch 79
 (.leaf ⟨(23, 14588460941440), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00007.record078_result⟩)
 (.branch 80
 (.leaf ⟨(23, 14604048564480), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00007.record079_result⟩)
 (.leaf ⟨(23, 14604052791296), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00007.record080_result⟩))))
 (.branch 84
 (.branch 82
 (.leaf ⟨(23, 14616457379840), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00007.record081_result⟩)
 (.branch 83
 (.leaf ⟨(23, 14621748527104), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00007.record082_result⟩)
 (.leaf ⟨(23, 14623428378624), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00007.record083_result⟩)))
 (.branch 85
 (.leaf ⟨(23, 14623700942848), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00007.record084_result⟩)
 (.branch 86
 (.leaf ⟨(23, 14623965184000), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00007.record085_result⟩)
 (.leaf ⟨(23, 14751207849984), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00007.record086_result⟩)))))
 (.branch 93
 (.branch 90
 (.branch 88
 (.leaf ⟨(23, 14759793590272), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00007.record087_result⟩)
 (.branch 89
 (.leaf ⟨(23, 14760462516224), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00007.record088_result⟩)
 (.leaf ⟨(23, 14768387653632), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00007.record089_result⟩)))
 (.branch 91
 (.leaf ⟨(23, 14768916135936), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00007.record090_result⟩)
 (.branch 92
 (.leaf ⟨(23, 14972532883456), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00007.record091_result⟩)
 (.leaf ⟨(23, 14973069688832), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00007.record092_result⟩))))
 (.branch 96
 (.branch 94
 (.leaf ⟨(23, 15037494198272), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00007.record093_result⟩)
 (.branch 95
 (.leaf ⟨(23, 15075410771968), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00007.record094_result⟩)
 (.leaf ⟨(23, 15110240206848), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00007.record095_result⟩)))
 (.branch 98
 (.branch 97
 (.leaf ⟨(23, 15166343217152), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00007.record096_result⟩)
 (.leaf ⟨(23, 15178552901632), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00007.record097_result⟩))
 (.branch 99
 (.leaf ⟨(23, 15212845531136), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00007.record098_result⟩)
 (.leaf ⟨(23, 15213580517376), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00007.record099_result⟩))))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (6238 + i))) 0 100 :=
  interval_of_check _ 0 100 (by decide +kernel)

public theorem complete : Block 6238 6338 :=
  block_of_table results 6238 100 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0085
