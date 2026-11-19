module
prelude
import GraphInputsRow27Part00009Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0412
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 50
 (.branch 25
 (.branch 12
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(27, 20824291674240), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00009.record000_result⟩)
 (.branch 2
 (.leaf ⟨(27, 20824440504320), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00009.record001_result⟩)
 (.leaf ⟨(27, 20839250659456), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00009.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(27, 20930862612480), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00009.record003_result⟩)
 (.branch 5
 (.leaf ⟨(27, 20935157563392), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00009.record004_result⟩)
 (.leaf ⟨(27, 20938649243712), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00009.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(27, 21007368716289), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00009.record006_result⟩)
 (.branch 8
 (.leaf ⟨(27, 21111452467200), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00009.record007_result⟩)
 (.leaf ⟨(27, 21119641845760), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00009.record008_result⟩)))
 (.branch 10
 (.leaf ⟨(27, 21119773966336), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00009.record009_result⟩)
 (.branch 11
 (.leaf ⟨(27, 21120234307584), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00009.record010_result⟩)
 (.leaf ⟨(27, 21123934715904), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00009.record011_result⟩)))))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf ⟨(27, 21124395057152), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00009.record012_result⟩)
 (.branch 14
 (.leaf ⟨(27, 21127515619328), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00009.record013_result⟩)
 (.leaf ⟨(27, 21235603867776), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00009.record014_result⟩)))
 (.branch 16
 (.leaf ⟨(27, 21256936259584), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00009.record015_result⟩)
 (.branch 17
 (.leaf ⟨(27, 21257068216960), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00009.record016_result⟩)
 (.leaf ⟨(27, 21316594311232), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00009.record017_result⟩))))
 (.branch 21
 (.branch 19
 (.leaf ⟨(27, 21333137178688), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00009.record018_result⟩)
 (.branch 20
 (.leaf ⟨(27, 21333271396352), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00009.record019_result⟩)
 (.leaf ⟨(27, 21333273477120), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00009.record020_result⟩)))
 (.branch 23
 (.branch 22
 (.leaf ⟨(27, 21350953517632), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00009.record021_result⟩)
 (.leaf ⟨(27, 21367462445120), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00009.record022_result⟩))
 (.branch 24
 (.leaf ⟨(27, 21367598743552), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00009.record023_result⟩)
 (.leaf ⟨(27, 21374062100480), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00009.record024_result⟩))))))
 (.branch 37
 (.branch 31
 (.branch 28
 (.branch 26
 (.leaf ⟨(27, 21374068342784), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00009.record025_result⟩)
 (.branch 27
 (.leaf ⟨(27, 21374192075008), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00009.record026_result⟩)
 (.leaf ⟨(27, 21374200463360), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00009.record027_result⟩)))
 (.branch 29
 (.leaf ⟨(27, 21374307680512), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00009.record028_result⟩)
 (.branch 30
 (.leaf ⟨(27, 21374317889536), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00009.record029_result⟩)
 (.leaf ⟨(27, 21374710333504), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00009.record030_result⟩))))
 (.branch 34
 (.branch 32
 (.leaf ⟨(27, 21376266143744), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00009.record031_result⟩)
 (.branch 33
 (.leaf ⟨(27, 21376340656128), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00009.record032_result⟩)
 (.leaf ⟨(27, 21376346898432), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00009.record033_result⟩)))
 (.branch 35
 (.leaf ⟨(27, 21376398264320), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00009.record034_result⟩)
 (.branch 36
 (.leaf ⟨(27, 21378602369792), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00009.record035_result⟩)
 (.leaf ⟨(27, 21379005022784), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00009.record036_result⟩)))))
 (.branch 43
 (.branch 40
 (.branch 38
 (.leaf ⟨(27, 21380548804864), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00009.record037_result⟩)
 (.branch 39
 (.leaf ⟨(27, 21380559013888), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00009.record038_result⟩)
 (.leaf ⟨(27, 21380901912640), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00009.record039_result⟩)))
 (.branch 41
 (.leaf ⟨(27, 21380904009728), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00009.record040_result⟩)
 (.branch 42
 (.leaf ⟨(27, 21380951457856), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00009.record041_result⟩)
 (.leaf ⟨(27, 21381018558528), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00009.record042_result⟩))))
 (.branch 46
 (.branch 44
 (.leaf ⟨(27, 21383165772352), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00009.record043_result⟩)
 (.branch 45
 (.leaf ⟨(27, 21401822175296), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00009.record044_result⟩)
 (.leaf ⟨(27, 21401889292288), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00009.record045_result⟩)))
 (.branch 48
 (.branch 47
 (.leaf ⟨(27, 21401891373056), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00009.record046_result⟩)
 (.leaf ⟨(27, 21402023363072), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00009.record047_result⟩))
 (.branch 49
 (.leaf ⟨(27, 21446158024704), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00009.record048_result⟩)
 (.leaf ⟨(27, 21446663344192), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00009.record049_result⟩)))))))
 (.branch 75
 (.branch 62
 (.branch 56
 (.branch 53
 (.branch 51
 (.leaf ⟨(27, 21450717216768), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00009.record050_result⟩)
 (.branch 52
 (.leaf ⟨(27, 21450723442752), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00009.record051_result⟩)
 (.leaf ⟨(27, 21450824093760), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00009.record052_result⟩)))
 (.branch 54
 (.leaf ⟨(27, 21454045319184), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00009.record053_result⟩)
 (.branch 55
 (.leaf ⟨(27, 21513785409536), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00009.record054_result⟩)
 (.leaf ⟨(27, 21514309077008), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00009.record055_result⟩))))
 (.branch 59
 (.branch 57
 (.leaf ⟨(27, 21515382816769), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00009.record056_result⟩)
 (.branch 58
 (.leaf ⟨(27, 21519543566337), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00009.record057_result⟩)
 (.leaf ⟨(27, 21587187206160), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00009.record058_result⟩)))
 (.branch 60
 (.leaf ⟨(27, 21595508705296), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00009.record059_result⟩)
 (.branch 61
 (.leaf ⟨(27, 21921668595712), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00009.record060_result⟩)
 (.leaf ⟨(27, 21921676658688), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00009.record061_result⟩)))))
 (.branch 68
 (.branch 65
 (.branch 63
 (.leaf ⟨(27, 21921798570240), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00009.record062_result⟩)
 (.branch 64
 (.leaf ⟨(27, 21921806958592), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00009.record063_result⟩)
 (.leaf ⟨(27, 21921808779264), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00009.record064_result⟩)))
 (.branch 66
 (.leaf ⟨(27, 21921915996416), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00009.record065_result⟩)
 (.branch 67
 (.leaf ⟨(27, 21922318649408), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00009.record066_result⟩)
 (.leaf ⟨(27, 21926076614912), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00009.record067_result⟩))))
 (.branch 71
 (.branch 69
 (.leaf ⟨(27, 21926085003264), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00009.record068_result⟩)
 (.branch 70
 (.leaf ⟨(27, 21926093259520), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00009.record069_result⟩)
 (.leaf ⟨(27, 21926613352968), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00009.record070_result⟩)))
 (.branch 73
 (.branch 72
 (.leaf ⟨(27, 21930245752832), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00009.record071_result⟩)
 (.leaf ⟨(27, 21930640017472), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00009.record072_result⟩))
 (.branch 74
 (.leaf ⟨(27, 21930656662080), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00009.record073_result⟩)
 (.leaf ⟨(27, 21930774102536), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00009.record074_result⟩))))))
 (.branch 87
 (.branch 81
 (.branch 78
 (.branch 76
 (.leaf ⟨(27, 21951577850372), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00009.record075_result⟩)
 (.branch 77
 (.leaf ⟨(27, 22250694656000), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00009.record076_result⟩)
 (.leaf ⟨(27, 22259274153984), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00009.record077_result⟩)))
 (.branch 79
 (.leaf ⟨(27, 22396444672000), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00009.record078_result⟩)
 (.branch 80
 (.leaf ⟨(27, 22396981477376), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00009.record079_result⟩)
 (.leaf ⟨(27, 22465029931008), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00009.record080_result⟩))))
 (.branch 84
 (.branch 82
 (.leaf ⟨(27, 22465038254080), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00009.record081_result⟩)
 (.branch 83
 (.leaf ⟨(27, 22482619744256), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00009.record082_result⟩)
 (.leaf ⟨(27, 22697371242560), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00009.record083_result⟩)))
 (.branch 85
 (.leaf ⟨(27, 22730657251328), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00009.record084_result⟩)
 (.branch 86
 (.leaf ⟨(27, 22732871827456), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00009.record085_result⟩)
 (.leaf ⟨(27, 22739236749312), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00009.record086_result⟩)))))
 (.branch 93
 (.branch 90
 (.branch 88
 (.leaf ⟨(27, 22804942553088), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00009.record087_result⟩)
 (.branch 89
 (.leaf ⟨(27, 22869769879552), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00009.record088_result⟩)
 (.leaf ⟨(27, 22876407267328), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00009.record089_result⟩)))
 (.branch 91
 (.leaf ⟨(27, 22876944072704), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00009.record090_result⟩)
 (.branch 92
 (.leaf ⟨(27, 22937688080384), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00009.record091_result⟩)
 (.leaf ⟨(27, 22948354195456), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00009.record092_result⟩))))
 (.branch 96
 (.branch 94
 (.leaf ⟨(27, 22948816617472), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00009.record093_result⟩)
 (.branch 95
 (.leaf ⟨(27, 22956143034368), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00009.record094_result⟩)
 (.leaf ⟨(27, 22962582339584), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00009.record095_result⟩)))
 (.branch 98
 (.branch 97
 (.leaf ⟨(27, 22980325343232), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00009.record096_result⟩)
 (.leaf ⟨(27, 22995818004480), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00009.record097_result⟩))
 (.branch 99
 (.leaf ⟨(27, 22995859161344), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00009.record098_result⟩)
 (.leaf ⟨(27, 23014716669952), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00009.record099_result⟩))))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (18573 + i))) 0 100 :=
  interval_of_check _ 0 100 (by decide +kernel)

public theorem complete : Block 18573 18673 :=
  block_of_table results 18573 100 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0412
