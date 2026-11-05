module
prelude
import GraphInputsRow19Part00020Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0060
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 49
 (.branch 24
 (.branch 12
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(19, 23280495886336), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00020.record000_result⟩)
 (.branch 2
 (.leaf ⟨(19, 23282086723840), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00020.record001_result⟩)
 (.leaf ⟨(19, 23282086789120), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00020.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(19, 23282088674560), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00020.record003_result⟩)
 (.branch 5
 (.leaf ⟨(19, 23283071254784), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00020.record004_result⟩)
 (.leaf ⟨(19, 23283077497088), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00020.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(19, 23283077562368), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00020.record006_result⟩)
 (.branch 8
 (.leaf ⟨(19, 23283580280896), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00020.record007_result⟩)
 (.leaf ⟨(19, 23283715538944), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00020.record008_result⟩)))
 (.branch 10
 (.leaf ⟨(19, 23284160856320), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00020.record009_result⟩)
 (.branch 11
 (.leaf ⟨(19, 23284637762624), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00020.record010_result⟩)
 (.leaf ⟨(19, 23284838040064), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00020.record011_result⟩)))))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf ⟨(19, 23298612731968), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00020.record012_result⟩)
 (.branch 14
 (.leaf ⟨(19, 23316379418624), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00020.record013_result⟩)
 (.leaf ⟨(19, 23316381304064), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00020.record014_result⟩)))
 (.branch 16
 (.leaf ⟨(19, 23348073725952), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00020.record015_result⟩)
 (.branch 17
 (.leaf ⟨(19, 23350277571328), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00020.record016_result⟩)
 (.leaf ⟨(19, 23350285959680), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00020.record017_result⟩))))
 (.branch 21
 (.branch 19
 (.leaf ⟨(19, 23353893192960), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00020.record018_result⟩)
 (.branch 20
 (.leaf ⟨(19, 23353893258240), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00020.record019_result⟩)
 (.leaf ⟨(19, 23354429932036), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00020.record020_result⟩)))
 (.branch 22
 (.leaf ⟨(19, 23367950352640), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00020.record021_result⟩)
 (.branch 23
 (.leaf ⟨(19, 23367954563136), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00020.record022_result⟩)
 (.leaf ⟨(19, 23372245303552), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00020.record023_result⟩))))))
 (.branch 36
 (.branch 30
 (.branch 27
 (.branch 25
 (.leaf ⟨(19, 23372249465088), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00020.record024_result⟩)
 (.branch 26
 (.leaf ⟨(19, 23372249530368), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00020.record025_result⟩)
 (.leaf ⟨(19, 23372251545856), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00020.record026_result⟩)))
 (.branch 28
 (.leaf ⟨(19, 23372449726720), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00020.record027_result⟩)
 (.branch 29
 (.leaf ⟨(19, 23372449792000), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00020.record028_result⟩)
 (.leaf ⟨(19, 23372482756864), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00020.record029_result⟩))))
 (.branch 33
 (.branch 31
 (.leaf ⟨(19, 23372482822144), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00020.record030_result⟩)
 (.branch 32
 (.leaf ⟨(19, 23372721299520), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00020.record031_result⟩)
 (.leaf ⟨(19, 23376604233984), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00020.record032_result⟩)))
 (.branch 34
 (.leaf ⟨(19, 23376610476288), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00020.record033_result⟩)
 (.branch 35
 (.leaf ⟨(19, 23376610541568), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00020.record034_result⟩)
 (.leaf ⟨(19, 23377013129280), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00020.record035_result⟩)))))
 (.branch 42
 (.branch 39
 (.branch 37
 (.leaf ⟨(19, 23377014169664), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00020.record036_result⟩)
 (.branch 38
 (.leaf ⟨(19, 23377138958592), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00020.record037_result⟩)
 (.leaf ⟨(19, 23377141104640), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00020.record038_result⟩)))
 (.branch 40
 (.leaf ⟨(19, 23377147346944), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00020.record039_result⟩)
 (.branch 41
 (.leaf ⟨(19, 23378690851072), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00020.record040_result⟩)
 (.leaf ⟨(19, 23385130156288), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00020.record041_result⟩))))
 (.branch 45
 (.branch 43
 (.leaf ⟨(19, 23385130221568), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00020.record042_result⟩)
 (.branch 44
 (.leaf ⟨(19, 23385136447552), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00020.record043_result⟩)
 (.leaf ⟨(19, 23385194201088), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00020.record044_result⟩)))
 (.branch 47
 (.branch 46
 (.leaf ⟨(19, 23385196216576), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00020.record045_result⟩)
 (.leaf ⟨(19, 23385196281856), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00020.record046_result⟩))
 (.branch 48
 (.leaf ⟨(19, 23385200443392), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00020.record047_result⟩)
 (.leaf ⟨(19, 23385203548224), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00020.record048_result⟩)))))))
 (.branch 74
 (.branch 61
 (.branch 55
 (.branch 52
 (.branch 50
 (.leaf ⟨(19, 23385334628416), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00020.record049_result⟩)
 (.branch 51
 (.leaf ⟨(19, 23385335668800), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00020.record050_result⟩)
 (.leaf ⟨(19, 23385468846080), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00020.record051_result⟩)))
 (.branch 53
 (.leaf ⟨(19, 23385863110720), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00020.record052_result⟩)
 (.branch 54
 (.leaf ⟨(19, 23385865207808), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00020.record053_result⟩)
 (.leaf ⟨(19, 23385963241536), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00020.record054_result⟩))))
 (.branch 58
 (.branch 56
 (.leaf ⟨(19, 23385964298240), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00020.record055_result⟩)
 (.branch 57
 (.leaf ⟨(19, 23387276591360), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00020.record056_result⟩)
 (.leaf ⟨(19, 23388044673024), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00020.record057_result⟩)))
 (.branch 59
 (.leaf ⟨(19, 23391569461504), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00020.record058_result⟩)
 (.branch 60
 (.leaf ⟨(19, 23391569526784), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00020.record059_result⟩)
 (.leaf ⟨(19, 23391575752768), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00020.record060_result⟩)))))
 (.branch 67
 (.branch 64
 (.branch 62
 (.leaf ⟨(19, 23391576793152), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00020.record061_result⟩)
 (.branch 63
 (.leaf ⟨(19, 23394789114112), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00020.record062_result⟩)
 (.leaf ⟨(19, 23400145830144), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00020.record063_result⟩)))
 (.branch 65
 (.leaf ⟨(19, 23400401682440), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00020.record064_result⟩)
 (.branch 66
 (.leaf ⟨(19, 23403833106688), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00020.record065_result⟩)
 (.leaf ⟨(19, 23407749054472), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00020.record066_result⟩))))
 (.branch 70
 (.branch 68
 (.leaf ⟨(19, 23408128106560), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00020.record067_result⟩)
 (.branch 69
 (.leaf ⟨(19, 23413016117504), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00020.record068_result⟩)
 (.leaf ⟨(19, 23416334794760), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00020.record069_result⟩)))
 (.branch 72
 (.branch 71
 (.leaf ⟨(19, 23419521548288), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00020.record070_result⟩)
 (.leaf ⟨(19, 23419659894848), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00020.record071_result⟩))
 (.branch 73
 (.leaf ⟨(19, 23419661845568), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00020.record072_result⟩)
 (.leaf ⟨(19, 23420324545024), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00020.record073_result⟩))))))
 (.branch 86
 (.branch 80
 (.branch 77
 (.branch 75
 (.leaf ⟨(19, 23420543205632), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00020.record074_result⟩)
 (.branch 76
 (.leaf ⟨(19, 23421599777024), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00020.record075_result⟩)
 (.leaf ⟨(19, 23421599842304), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00020.record076_result⟩)))
 (.branch 78
 (.leaf ⟨(19, 23421601857792), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00020.record077_result⟩)
 (.branch 79
 (.leaf ⟨(19, 23421601923072), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00020.record078_result⟩)
 (.leaf ⟨(19, 23421603808512), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00020.record079_result⟩))))
 (.branch 83
 (.branch 81
 (.leaf ⟨(19, 23421610099776), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00020.record080_result⟩)
 (.branch 82
 (.leaf ⟨(19, 23421801989376), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00020.record081_result⟩)
 (.leaf ⟨(19, 23421807370304), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00020.record082_result⟩)))
 (.branch 84
 (.leaf ⟨(19, 23421807386624), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00020.record083_result⟩)
 (.branch 85
 (.leaf ⟨(19, 23421808280640), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00020.record084_result⟩)
 (.leaf ⟨(19, 23421876436993), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00020.record085_result⟩)))))
 (.branch 92
 (.branch 89
 (.branch 87
 (.leaf ⟨(19, 23422402822720), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00020.record086_result⟩)
 (.branch 88
 (.leaf ⟨(19, 23422404919808), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00020.record087_result⟩)
 (.leaf ⟨(19, 23424805191680), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00020.record088_result⟩)))
 (.branch 90
 (.leaf ⟨(19, 23424811417664), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00020.record089_result⟩)
 (.branch 91
 (.leaf ⟨(19, 23424812458048), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00020.record090_result⟩)
 (.leaf ⟨(19, 23424838156544), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00020.record091_result⟩))))
 (.branch 95
 (.branch 93
 (.leaf ⟨(19, 23424838221824), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00020.record092_result⟩)
 (.branch 94
 (.leaf ⟨(19, 23424904216832), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00020.record093_result⟩)
 (.leaf ⟨(19, 23424904282112), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00020.record094_result⟩)))
 (.branch 97
 (.branch 96
 (.leaf ⟨(19, 23424905322496), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00020.record095_result⟩)
 (.leaf ⟨(19, 23424911548480), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00020.record096_result⟩))
 (.branch 98
 (.leaf ⟨(19, 23424922617856), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00020.record097_result⟩)
 (.leaf ⟨(19, 23424928063552), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00020.record098_result⟩))))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (4065 + i))) 0 99 :=
  interval_of_check _ 0 99 (by decide +kernel)

public theorem complete : Block 4065 4164 :=
  block_of_table results 4065 99 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0060
