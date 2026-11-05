module
prelude
import GraphInputsRow28Part00001Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0421
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 50
 (.branch 25
 (.branch 12
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(28, 3737428967424), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00001.record000_result⟩)
 (.branch 2
 (.leaf ⟨(28, 3923188449280), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00001.record001_result⟩)
 (.leaf ⟨(28, 3923196772352), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00001.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(28, 3926812328192), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00001.record003_result⟩)
 (.branch 5
 (.leaf ⟨(28, 3927084957696), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00001.record004_result⟩)
 (.leaf ⟨(28, 3927349198848), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00001.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(28, 3927357521920), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00001.record006_result⟩)
 (.branch 8
 (.leaf ⟨(28, 3929932890368), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00001.record007_result⟩)
 (.leaf ⟨(28, 3930700972032), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00001.record008_result⟩)))
 (.branch 10
 (.leaf ⟨(28, 3942815662336), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00001.record009_result⟩)
 (.branch 11
 (.leaf ⟨(28, 4067334226176), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00001.record010_result⟩)
 (.leaf ⟨(28, 4067879354368), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00001.record011_result⟩)))))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf ⟨(28, 4075924128000), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00001.record012_result⟩)
 (.branch 14
 (.leaf ⟨(28, 4076200853504), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00001.record013_result⟩)
 (.leaf ⟨(28, 4076729270784), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00001.record014_result⟩)))
 (.branch 16
 (.leaf ⟨(28, 4076737658880), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00001.record015_result⟩)
 (.branch 17
 (.leaf ⟨(28, 4136456749056), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00001.record016_result⟩)
 (.leaf ⟨(28, 4213635612672), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00001.record017_result⟩))))
 (.branch 21
 (.branch 19
 (.leaf ⟨(28, 4214172418048), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00001.record018_result⟩)
 (.branch 20
 (.leaf ⟨(28, 4217796362240), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00001.record019_result⟩)
 (.leaf ⟨(28, 4329345941760), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00001.record020_result⟩)))
 (.branch 23
 (.branch 22
 (.leaf ⟨(28, 4333643038720), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00001.record021_result⟩)
 (.leaf ⟨(28, 4333898891264), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00001.record022_result⟩))
 (.branch 24
 (.leaf ⟨(28, 4333915602944), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00001.record023_result⟩)
 (.leaf ⟨(28, 4334427570176), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00001.record024_result⟩))))))
 (.branch 37
 (.branch 31
 (.branch 28
 (.branch 26
 (.leaf ⟨(28, 4342212132864), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00001.record025_result⟩)
 (.branch 27
 (.leaf ⟨(28, 4342757195776), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00001.record026_result⟩)
 (.leaf ⟨(28, 4351078694912), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00001.record027_result⟩)))
 (.branch 29
 (.leaf ⟨(28, 4351607177216), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00001.record028_result⟩)
 (.branch 30
 (.leaf ⟨(28, 4359391936512), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00001.record029_result⟩)
 (.leaf ⟨(28, 4359928676352), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00001.record030_result⟩))))
 (.branch 34
 (.branch 32
 (.leaf ⟨(28, 4401378984192), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00001.record031_result⟩)
 (.branch 33
 (.leaf ⟨(28, 4442686505216), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00001.record032_result⟩)
 (.leaf ⟨(28, 4508377743616), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00001.record033_result⟩)))
 (.branch 35
 (.leaf ⟨(28, 4508386131968), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00001.record034_result⟩)
 (.branch 36
 (.leaf ⟨(28, 4512546881536), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00001.record035_result⟩)
 (.leaf ⟨(28, 4520868380672), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00001.record036_result⟩)))))
 (.branch 43
 (.branch 40
 (.branch 38
 (.leaf ⟨(28, 4523418460160), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00001.record037_result⟩)
 (.branch 39
 (.leaf ⟨(28, 4554084073728), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00001.record038_result⟩)
 (.leaf ⟨(28, 4691518832896), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00001.record039_result⟩)))
 (.branch 41
 (.leaf ⟨(28, 4720852738048), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00001.record040_result⟩)
 (.branch 42
 (.leaf ⟨(28, 4727016292608), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00001.record041_result⟩)
 (.leaf ⟨(28, 4727020519424), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00001.record042_result⟩))))
 (.branch 46
 (.branch 44
 (.leaf ⟨(28, 4727429414912), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00001.record043_result⟩)
 (.branch 45
 (.leaf ⟨(28, 5026529476864), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00001.record044_result⟩)
 (.leaf ⟨(28, 5026793718016), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00001.record045_result⟩)))
 (.branch 48
 (.branch 47
 (.leaf ⟨(28, 5026802106368), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00001.record046_result⟩)
 (.leaf ⟨(28, 5026991898880), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00001.record047_result⟩))
 (.branch 49
 (.leaf ⟨(28, 5035581800704), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00001.record048_result⟩)
 (.leaf ⟨(28, 5035593310208), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00001.record049_result⟩)))))))
 (.branch 75
 (.branch 62
 (.branch 56
 (.branch 53
 (.branch 51
 (.leaf ⟨(28, 5043097444608), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00001.record050_result⟩)
 (.branch 52
 (.leaf ⟨(28, 5104100999424), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00001.record051_result⟩)
 (.leaf ⟨(28, 5104105226240), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00001.record052_result⟩)))
 (.branch 54
 (.leaf ⟨(28, 5104178569216), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00001.record053_result⟩)
 (.branch 55
 (.leaf ⟨(28, 5107521954048), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00001.record054_result⟩)
 (.leaf ⟨(28, 5137340891136), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00001.record055_result⟩))))
 (.branch 59
 (.branch 57
 (.leaf ⟨(28, 5139066847488), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00001.record056_result⟩)
 (.branch 58
 (.leaf ⟨(28, 5141889613824), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00001.record057_result⟩)
 (.leaf ⟨(28, 5241349087232), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00001.record058_result⟩)))
 (.branch 60
 (.leaf ⟨(28, 5279324372992), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00001.record059_result⟩)
 (.branch 61
 (.leaf ⟨(28, 5279332696064), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00001.record060_result⟩)
 (.leaf ⟨(28, 5317974819360), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00001.record061_result⟩)))))
 (.branch 68
 (.branch 65
 (.branch 63
 (.leaf ⟨(28, 5317975932928), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00001.record062_result⟩)
 (.branch 64
 (.leaf ⟨(28, 5413944754176), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00001.record063_result⟩)
 (.leaf ⟨(28, 5516394766400), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00001.record064_result⟩)))
 (.branch 66
 (.leaf ⟨(28, 5572262952960), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00001.record065_result⟩)
 (.branch 67
 (.leaf ⟨(28, 5585203396864), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00001.record066_result⟩)
 (.leaf ⟨(28, 5607356694784), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00001.record067_result⟩))))
 (.branch 71
 (.branch 69
 (.leaf ⟨(28, 5620640055296), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00001.record068_result⟩)
 (.branch 70
 (.leaf ⟨(28, 5652739530816), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00001.record069_result⟩)
 (.leaf ⟨(28, 5791306235904), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00001.record070_result⟩)))
 (.branch 73
 (.branch 72
 (.leaf ⟨(28, 5829088509952), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00001.record071_result⟩)
 (.leaf ⟨(28, 5833373057024), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00001.record072_result⟩))
 (.branch 74
 (.leaf ⟨(28, 5882234601472), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00001.record073_result⟩)
 (.leaf ⟨(28, 5899414405120), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00001.record074_result⟩))))))
 (.branch 87
 (.branch 81
 (.branch 78
 (.branch 76
 (.leaf ⟨(28, 5899942887424), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00001.record075_result⟩)
 (.branch 77
 (.leaf ⟨(28, 6087856160768), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00001.record076_result⟩)
 (.leaf ⟨(28, 6100065779968), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00001.record077_result⟩)))
 (.branch 79
 (.leaf ⟨(28, 6100338409472), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00001.record078_result⟩)
 (.branch 80
 (.leaf ⟨(28, 6100602650624), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00001.record079_result⟩)
 (.leaf ⟨(28, 6100610973696), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00001.record080_result⟩))))
 (.branch 84
 (.branch 82
 (.leaf ⟨(28, 6103954423808), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00001.record081_result⟩)
 (.branch 83
 (.leaf ⟨(28, 6305574027264), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00001.record082_result⟩)
 (.leaf ⟨(28, 6329440206848), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00001.record083_result⟩)))
 (.branch 85
 (.leaf ⟨(28, 6340514709760), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00001.record084_result⟩)
 (.branch 86
 (.leaf ⟨(28, 6340651057152), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00001.record085_result⟩)
 (.leaf ⟨(28, 6340659380224), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00001.record086_result⟩)))))
 (.branch 93
 (.branch 90
 (.branch 88
 (.leaf ⟨(28, 6341263360000), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00001.record087_result⟩)
 (.branch 89
 (.leaf ⟨(28, 6341554897152), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00001.record088_result⟩)
 (.leaf ⟨(28, 6378831741440), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00001.record089_result⟩)))
 (.branch 91
 (.leaf ⟨(28, 6378840129536), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00001.record090_result⟩)
 (.branch 92
 (.leaf ⟨(28, 6379377000448), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00001.record091_result⟩)
 (.leaf ⟨(28, 6379905482752), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00001.record092_result⟩))))
 (.branch 96
 (.branch 94
 (.leaf ⟨(28, 6417494835200), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00001.record093_result⟩)
 (.branch 95
 (.leaf ⟨(28, 6433886240768), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00001.record094_result⟩)
 (.leaf ⟨(28, 6434423046144), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00001.record095_result⟩)))
 (.branch 98
 (.branch 97
 (.leaf ⟨(28, 6442471981056), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00001.record096_result⟩)
 (.leaf ⟨(28, 6443256512512), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00001.record097_result⟩))
 (.branch 99
 (.leaf ⟨(28, 6451041075200), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00001.record098_result⟩)
 (.leaf ⟨(28, 6451586138112), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00001.record099_result⟩))))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (19404 + i))) 0 100 :=
  interval_of_check _ 0 100 (by decide +kernel)

public theorem complete : Block 19404 19504 :=
  block_of_table results 19404 100 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0421
