module
prelude
import GraphInputsRow27Part00015Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0418
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 50
 (.branch 25
 (.branch 12
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(27, 33126320455680), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00015.record000_result⟩)
 (.branch 2
 (.leaf ⟨(27, 33158515933184), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00015.record001_result⟩)
 (.leaf ⟨(27, 33195132256256), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00015.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(27, 33206070935552), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00015.record003_result⟩)
 (.branch 5
 (.leaf ⟨(27, 33206648700928), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00015.record004_result⟩)
 (.leaf ⟨(27, 33207111122944), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00015.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(27, 33230456619008), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00015.record006_result⟩)
 (.branch 8
 (.leaf ⟨(27, 33241436389376), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00015.record007_result⟩)
 (.leaf ⟨(27, 33294638170112), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00015.record008_result⟩)))
 (.branch 10
 (.leaf ⟨(27, 33294693435400), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00015.record009_result⟩)
 (.branch 11
 (.leaf ⟨(27, 33295733621768), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00015.record010_result⟩)
 (.leaf ⟨(27, 33295750397953), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00015.record011_result⟩)))))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf ⟨(27, 33545073524736), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00015.record012_result⟩)
 (.branch 14
 (.leaf ⟨(27, 33574049349632), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00015.record013_result⟩)
 (.leaf ⟨(27, 33613790904320), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00015.record014_result⟩)))
 (.branch 16
 (.leaf ⟨(27, 33677124313344), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00015.record015_result⟩)
 (.branch 17
 (.leaf ⟨(27, 33678215413760), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00015.record016_result⟩)
 (.leaf ⟨(27, 33681335128320), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00015.record017_result⟩))))
 (.branch 21
 (.branch 19
 (.leaf ⟨(27, 33687073718272), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00015.record018_result⟩)
 (.branch 20
 (.leaf ⟨(27, 33742623145984), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00015.record019_result⟩)
 (.leaf ⟨(27, 33742631469056), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00015.record020_result⟩)))
 (.branch 23
 (.branch 22
 (.leaf ⟨(27, 33750423707648), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00015.record021_result⟩)
 (.leaf ⟨(27, 34086020808704), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00015.record022_result⟩))
 (.branch 24
 (.leaf ⟨(27, 34086022889472), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00015.record023_result⟩)
 (.leaf ⟨(27, 34086228336704), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00015.record024_result⟩))))))
 (.branch 37
 (.branch 31
 (.branch 28
 (.branch 26
 (.leaf ⟨(27, 34086228353024), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00015.record025_result⟩)
 (.branch 27
 (.leaf ⟨(27, 34087163662592), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00015.record026_result⟩)
 (.leaf ⟨(27, 34087163727872), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00015.record027_result⟩)))
 (.branch 29
 (.leaf ⟨(27, 34087171526672), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00015.record028_result⟩)
 (.branch 30
 (.leaf ⟨(27, 34087180177664), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00015.record029_result⟩)
 (.leaf ⟨(27, 34087180242944), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00015.record030_result⟩))))
 (.branch 34
 (.branch 32
 (.leaf ⟨(27, 34087188301840), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00015.record031_result⟩)
 (.branch 33
 (.leaf ⟨(27, 34087302074432), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00015.record032_result⟩)
 (.leaf ⟨(27, 34087303647248), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00015.record033_result⟩)))
 (.branch 35
 (.leaf ⟨(27, 34087320422416), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00015.record034_result⟩)
 (.branch 36
 (.leaf ⟨(27, 34088253719040), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00015.record035_result⟩)
 (.leaf ⟨(27, 34088262041601), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00015.record036_result⟩)))))
 (.branch 43
 (.branch 40
 (.branch 38
 (.leaf ⟨(27, 34088358645824), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00015.record037_result⟩)
 (.branch 39
 (.leaf ⟨(27, 34088394162177), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00015.record038_result⟩)
 (.leaf ⟨(27, 34090398023936), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00015.record039_result⟩)))
 (.branch 41
 (.leaf ⟨(27, 34093561546768), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00015.record040_result⟩)
 (.branch 42
 (.leaf ⟨(27, 34094007193616), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00015.record041_result⟩)
 (.leaf ⟨(27, 34094023968784), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00015.record042_result⟩))))
 (.branch 46
 (.branch 44
 (.leaf ⟨(27, 34095097708545), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00015.record043_result⟩)
 (.branch 45
 (.leaf ⟨(27, 34119375655168), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00015.record044_result⟩)
 (.leaf ⟨(27, 34119514067008), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00015.record045_result⟩)))
 (.branch 48
 (.branch 47
 (.leaf ⟨(27, 34123792123920), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00015.record046_result⟩)
 (.leaf ⟨(27, 34123809292289), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00015.record047_result⟩))
 (.branch 49
 (.leaf ⟨(27, 34124794494976), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00015.record048_result⟩)
 (.leaf ⟨(27, 34124865863681), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00015.record049_result⟩)))))))
 (.branch 75
 (.branch 62
 (.branch 56
 (.branch 53
 (.branch 51
 (.leaf ⟨(27, 34127952873488), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00015.record050_result⟩)
 (.branch 52
 (.leaf ⟨(27, 34155878973696), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00015.record051_result⟩)
 (.leaf ⟨(27, 34194419941376), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00015.record052_result⟩)))
 (.branch 54
 (.leaf ⟨(27, 34195732692992), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00015.record053_result⟩)
 (.branch 55
 (.leaf ⟨(27, 34196261175296), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00015.record054_result⟩)
 (.leaf ⟨(27, 34222385664256), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00015.record055_result⟩))))
 (.branch 59
 (.branch 57
 (.leaf ⟨(27, 34222391955520), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00015.record056_result⟩)
 (.branch 58
 (.leaf ⟨(27, 34223943852096), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00015.record057_result⟩)
 (.leaf ⟨(27, 34239548622864), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00015.record058_result⟩)))
 (.branch 60
 (.leaf ⟨(27, 34240604422144), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00015.record059_result⟩)
 (.branch 61
 (.leaf ⟨(27, 34497227923520), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00015.record060_result⟩)
 (.leaf ⟨(27, 34497228980224), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00015.record061_result⟩)))))
 (.branch 68
 (.branch 65
 (.branch 63
 (.leaf ⟨(27, 34497230800896), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00015.record062_result⟩)
 (.branch 64
 (.leaf ⟨(27, 34497278249024), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00015.record063_result⟩)
 (.leaf ⟨(27, 34498318305344), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00015.record064_result⟩)))
 (.branch 66
 (.leaf ⟨(27, 34498320402432), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00015.record065_result⟩)
 (.branch 67
 (.leaf ⟨(27, 34498334949952), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00015.record066_result⟩)
 (.leaf ⟨(27, 34498452390408), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00015.record067_result⟩))))
 (.branch 71
 (.branch 69
 (.leaf ⟨(27, 34531556067328), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00015.record068_result⟩)
 (.branch 70
 (.leaf ⟨(27, 34531671410696), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00015.record069_result⟩)
 (.leaf ⟨(27, 34531688055304), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00015.record070_result⟩)))
 (.branch 73
 (.branch 72
 (.leaf ⟨(27, 34634667491328), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00015.record071_result⟩)
 (.leaf ⟨(27, 34634671132672), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00015.record072_result⟩))
 (.branch 74
 (.leaf ⟨(27, 34634679191568), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00015.record073_result⟩)
 (.leaf ⟨(27, 34634910142480), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00015.record074_result⟩))))))
 (.branch 87
 (.branch 81
 (.branch 78
 (.branch 76
 (.leaf ⟨(27, 34634910402576), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00015.record075_result⟩)
 (.branch 77
 (.leaf ⟨(27, 34635752931329), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00015.record076_result⟩)
 (.leaf ⟨(27, 34635845795840), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00015.record077_result⟩)))
 (.branch 79
 (.leaf ⟨(27, 34635853598720), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00015.record078_result⟩)
 (.branch 80
 (.leaf ⟨(27, 34635984142337), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00015.record079_result⟩)
 (.leaf ⟨(27, 34637873185024), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00015.record080_result⟩))))
 (.branch 84
 (.branch 82
 (.leaf ⟨(27, 34638009532416), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00015.record081_result⟩)
 (.branch 83
 (.leaf ⟨(27, 34638017855488), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00015.record082_result⟩)
 (.leaf ⟨(27, 34638240743424), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00015.record083_result⟩)))
 (.branch 85
 (.leaf ⟨(27, 34639196983552), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00015.record084_result⟩)
 (.branch 86
 (.leaf ⟨(27, 34639205371904), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00015.record085_result⟩)
 (.leaf ⟨(27, 34639213498624), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00015.record086_result⟩)))))
 (.branch 93
 (.branch 90
 (.branch 88
 (.leaf ⟨(27, 34639716814864), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00015.record087_result⟩)
 (.branch 89
 (.leaf ⟨(27, 34640286974720), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00015.record088_result⟩)
 (.leaf ⟨(27, 34640790290960), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00015.record089_result⟩)))
 (.branch 91
 (.leaf ⟨(27, 34641092837632), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00015.record090_result⟩)
 (.branch 92
 (.leaf ⟨(27, 34641864560640), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00015.record091_result⟩)
 (.leaf ⟨(27, 34670085439744), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00015.record092_result⟩))))
 (.branch 96
 (.branch 94
 (.leaf ⟨(27, 34673288315136), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00015.record093_result⟩)
 (.branch 95
 (.leaf ⟨(27, 34673556783104), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00015.record094_result⟩)
 (.leaf ⟨(27, 34673565106176), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00015.record095_result⟩)))
 (.branch 98
 (.branch 97
 (.leaf ⟨(27, 34674076553216), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00015.record096_result⟩)
 (.leaf ⟨(27, 34674344886528), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00015.record097_result⟩))
 (.branch 99
 (.leaf ⟨(27, 34674382536704), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00015.record098_result⟩)
 (.leaf ⟨(27, 34674655100928), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00015.record099_result⟩))))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (19173 + i))) 0 100 :=
  interval_of_check _ 0 100 (by decide +kernel)

public theorem complete : Block 19173 19273 :=
  block_of_table results 19173 100 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0418
