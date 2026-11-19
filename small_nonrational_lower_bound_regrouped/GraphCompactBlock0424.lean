module
prelude
import GraphInputsRow28Part00004Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0424
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 50
 (.branch 25
 (.branch 12
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(28, 12731629502464), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00004.record000_result⟩)
 (.branch 2
 (.leaf ⟨(28, 12732166307840), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00004.record001_result⟩)
 (.leaf ⟨(28, 12738910814208), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00004.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(28, 12739678830592), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00004.record003_result⟩)
 (.branch 5
 (.leaf ⟨(28, 12786403442688), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00004.record004_result⟩)
 (.leaf ⟨(28, 12792165826560), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00004.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(28, 12794707710208), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00004.record006_result⟩)
 (.branch 8
 (.leaf ⟨(28, 12794749583360), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00004.record007_result⟩)
 (.leaf ⟨(28, 12800214761472), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00004.record008_result⟩)))
 (.branch 10
 (.leaf ⟨(28, 12800487325696), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00004.record009_result⟩)
 (.branch 11
 (.leaf ⟨(28, 12800751566848), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00004.record010_result⟩)
 (.leaf ⟨(28, 12803335323648), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00004.record011_result⟩)))))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf ⟨(28, 12804103340032), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00004.record012_result⟩)
 (.branch 14
 (.leaf ⟨(28, 12876312150016), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00004.record013_result⟩)
 (.leaf ⟨(28, 12920473813248), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00004.record014_result⟩)))
 (.branch 16
 (.leaf ⟨(28, 12932184342528), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00004.record015_result⟩)
 (.branch 17
 (.leaf ⟨(28, 12932952358912), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00004.record016_result⟩)
 (.leaf ⟨(28, 12937653682176), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00004.record017_result⟩))))
 (.branch 21
 (.branch 19
 (.leaf ⟨(28, 12937922084864), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00004.record018_result⟩)
 (.branch 20
 (.leaf ⟨(28, 12940774244352), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00004.record019_result⟩)
 (.leaf ⟨(28, 12945067114496), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00004.record020_result⟩)))
 (.branch 23
 (.branch 22
 (.leaf ⟨(28, 13013751070720), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00004.record021_result⟩)
 (.leaf ⟨(28, 13125441093632), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00004.record022_result⟩))
 (.branch 24
 (.leaf ⟨(28, 13134035156992), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00004.record023_result⟩)
 (.leaf ⟨(28, 13134563639296), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00004.record024_result⟩))))))
 (.branch 37
 (.branch 31
 (.branch 28
 (.branch 26
 (.leaf ⟨(28, 13142620897280), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00004.record025_result⟩)
 (.branch 27
 (.leaf ⟨(28, 13151189991424), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00004.record026_result⟩)
 (.leaf ⟨(28, 13234207785216), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00004.record027_result⟩)))
 (.branch 29
 (.leaf ⟨(28, 13234216173568), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00004.record028_result⟩)
 (.branch 30
 (.leaf ⟨(28, 13234674368768), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00004.record029_result⟩)
 (.leaf ⟨(28, 13234685878272), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00004.record030_result⟩))))
 (.branch 34
 (.branch 32
 (.leaf ⟨(28, 13238509043712), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00004.record031_result⟩)
 (.branch 33
 (.leaf ⟨(28, 13238769058048), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00004.record032_result⟩)
 (.leaf ⟨(28, 13238773284864), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00004.record033_result⟩)))
 (.branch 35
 (.leaf ⟨(28, 13238835118336), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00004.record034_result⟩)
 (.branch 36
 (.leaf ⟨(28, 13238846627840), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00004.record035_result⟩)
 (.leaf ⟨(28, 13272859345152), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00004.record036_result⟩)))))
 (.branch 43
 (.branch 40
 (.branch 38
 (.leaf ⟨(28, 13272867733504), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00004.record037_result⟩)
 (.branch 39
 (.leaf ⟨(28, 13273127747840), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00004.record038_result⟩)
 (.leaf ⟨(28, 13273139257344), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00004.record039_result⟩)))
 (.branch 41
 (.leaf ⟨(28, 13273329049856), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00004.record040_result⟩)
 (.branch 42
 (.leaf ⟨(28, 13274402267392), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00004.record041_result⟩)
 (.leaf ⟨(28, 13281453473792), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00004.record042_result⟩))))
 (.branch 46
 (.branch 44
 (.leaf ⟨(28, 13289434652704), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00004.record043_result⟩)
 (.branch 45
 (.leaf ⟨(28, 13317355667456), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00004.record044_result⟩)
 (.leaf ⟨(28, 13317363990528), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00004.record045_result⟩)))
 (.branch 48
 (.branch 47
 (.leaf ⟨(28, 13341452992512), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00004.record046_result⟩)
 (.leaf ⟨(28, 13341856636928), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00004.record047_result⟩))
 (.branch 49
 (.leaf ⟨(28, 13342987526400), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00004.record048_result⟩)
 (.leaf ⟨(28, 13350034505984), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00004.record049_result⟩)))))))
 (.branch 75
 (.branch 62
 (.branch 56
 (.branch 53
 (.branch 51
 (.leaf ⟨(28, 13350038732800), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00004.record050_result⟩)
 (.branch 52
 (.leaf ⟨(28, 13350046015488), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00004.record051_result⟩)
 (.leaf ⟨(28, 13350178136064), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00004.record052_result⟩)))
 (.branch 54
 (.leaf ⟨(28, 13350235808000), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00004.record053_result⟩)
 (.branch 55
 (.leaf ⟨(28, 13353859162144), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00004.record054_result⟩)
 (.leaf ⟨(28, 13377346732800), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00004.record055_result⟩))))
 (.branch 59
 (.branch 57
 (.leaf ⟨(28, 13377355186176), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00004.record056_result⟩)
 (.branch 58
 (.leaf ⟨(28, 13385940926464), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00004.record057_result⟩)
 (.leaf ⟨(28, 13385949249536), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00004.record058_result⟩)))
 (.branch 60
 (.leaf ⟨(28, 13388219482112), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00004.record059_result⟩)
 (.branch 61
 (.leaf ⟨(28, 13480158044416), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00004.record060_result⟩)
 (.leaf ⟨(28, 13522842976512), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00004.record061_result⟩)))))
 (.branch 68
 (.branch 65
 (.branch 63
 (.leaf ⟨(28, 13523111444480), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00004.record062_result⟩)
 (.branch 64
 (.leaf ⟨(28, 13523119767552), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00004.record063_result⟩)
 (.leaf ⟨(28, 13523379847168), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00004.record064_result⟩)))
 (.branch 66
 (.leaf ⟨(28, 13523511967744), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00004.record065_result⟩)
 (.branch 67
 (.leaf ⟨(28, 13525658402816), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00004.record066_result⟩)
 (.leaf ⟨(28, 13564313083904), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00004.record067_result⟩))))
 (.branch 71
 (.branch 69
 (.leaf ⟨(28, 13753862127872), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00004.record068_result⟩)
 (.branch 70
 (.leaf ⟨(28, 13754130530560), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00004.record069_result⟩)
 (.leaf ⟨(28, 13754142040064), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00004.record070_result⟩)))
 (.branch 73
 (.branch 72
 (.leaf ⟨(28, 13890478416128), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00004.record071_result⟩)
 (.leaf ⟨(28, 13890486804480), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00004.record072_result⟩))
 (.branch 74
 (.leaf ⟨(28, 13891543375872), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00004.record073_result⟩)
 (.leaf ⟨(28, 13892642145024), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00004.record074_result⟩))))))
 (.branch 87
 (.branch 81
 (.branch 78
 (.branch 76
 (.leaf ⟨(28, 13899319742496), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00004.record075_result⟩)
 (.branch 77
 (.leaf ⟨(28, 13900196151296), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00004.record076_result⟩)
 (.leaf ⟨(28, 13900204474368), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00004.record077_result⟩)))
 (.branch 79
 (.leaf ⟨(28, 13900393218592), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00004.record078_result⟩)
 (.branch 80
 (.leaf ⟨(28, 13900394332160), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00004.record079_result⟩)
 (.leaf ⟨(28, 13933431816192), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00004.record080_result⟩))))
 (.branch 84
 (.branch 82
 (.leaf ⟨(28, 13933440139264), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00004.record081_result⟩)
 (.branch 83
 (.leaf ⟨(28, 13941740732416), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00004.record082_result⟩)
 (.leaf ⟨(28, 13942277537792), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00004.record083_result⟩)))
 (.branch 85
 (.leaf ⟨(28, 14037635072000), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00004.record084_result⟩)
 (.branch 86
 (.leaf ⟨(28, 14037833252864), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00004.record085_result⟩)
 (.leaf ⟨(28, 14045348896768), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00004.record086_result⟩)))))
 (.branch 93
 (.branch 90
 (.branch 88
 (.leaf ⟨(28, 14182053380096), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00004.record087_result⟩)
 (.branch 89
 (.leaf ⟨(28, 14182788366336), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00004.record088_result⟩)
 (.leaf ⟨(28, 14299591377152), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00004.record089_result⟩)))
 (.branch 91
 (.leaf ⟨(28, 14299602886656), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00004.record090_result⟩)
 (.branch 92
 (.leaf ⟨(28, 14303895756800), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00004.record091_result⟩)
 (.leaf ⟨(28, 14347373936896), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00004.record092_result⟩))))
 (.branch 96
 (.branch 94
 (.leaf ⟨(28, 14371523141632), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00004.record093_result⟩)
 (.branch 95
 (.leaf ⟨(28, 14372646748160), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00004.record094_result⟩)
 (.leaf ⟨(28, 14380108881920), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00004.record095_result⟩)))
 (.branch 98
 (.branch 97
 (.leaf ⟨(28, 14448941338656), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00004.record096_result⟩)
 (.leaf ⟨(28, 14449958191104), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00004.record097_result⟩))
 (.branch 99
 (.leaf ⟨(28, 14450014814752), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00004.record098_result⟩)
 (.leaf ⟨(28, 14450015928320), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00004.record099_result⟩))))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (19704 + i))) 0 100 :=
  interval_of_check _ 0 100 (by decide +kernel)

public theorem complete : Block 19704 19804 :=
  block_of_table results 19704 100 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0424
