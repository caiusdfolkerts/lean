module
prelude
import GraphInputsRow28Part00006Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0426
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 50
 (.branch 25
 (.branch 12
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(28, 17198122795524), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00006.record000_result⟩)
 (.branch 2
 (.leaf ⟨(28, 17198122991616), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00006.record001_result⟩)
 (.leaf ⟨(28, 17198399619072), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00006.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(28, 17198928101376), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00006.record003_result⟩)
 (.branch 5
 (.leaf ⟨(28, 17205680930816), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00006.record004_result⟩)
 (.leaf ⟨(28, 17257723854848), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00006.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(28, 17274895335424), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00006.record006_result⟩)
 (.branch 8
 (.leaf ⟨(28, 17326452244480), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00006.record007_result⟩)
 (.leaf ⟨(28, 17334505340928), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00006.record008_result⟩)))
 (.branch 10
 (.leaf ⟨(28, 17335561912320), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00006.record009_result⟩)
 (.branch 11
 (.leaf ⟨(28, 17343078076416), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00006.record010_result⟩)
 (.leaf ⟨(28, 17454768128000), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00006.record011_result⟩)))))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf ⟨(28, 17459318882304), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00006.record012_result⟩)
 (.branch 14
 (.leaf ⟨(28, 17480517025792), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00006.record013_result⟩)
 (.leaf ⟨(28, 17532593373184), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00006.record014_result⟩)))
 (.branch 16
 (.leaf ⟨(28, 17549236371456), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00006.record015_result⟩)
 (.branch 17
 (.leaf ⟨(28, 17595518500992), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00006.record016_result⟩)
 (.leaf ⟨(28, 17595584561280), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00006.record017_result⟩))))
 (.branch 21
 (.branch 19
 (.leaf ⟨(28, 17630180245504), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00006.record018_result⟩)
 (.branch 20
 (.leaf ⟨(28, 17632128499712), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00006.record019_result⟩)
 (.leaf ⟨(28, 17632260620288), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00006.record020_result⟩)))
 (.branch 23
 (.branch 22
 (.leaf ⟨(28, 17632262635776), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00006.record021_result⟩)
 (.leaf ⟨(28, 17632732389440), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00006.record022_result⟩))
 (.branch 24
 (.leaf ⟨(28, 17636555571200), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00006.record023_result⟩)
 (.leaf ⟨(28, 17636819812352), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00006.record024_result⟩))))))
 (.branch 37
 (.branch 31
 (.branch 28
 (.branch 26
 (.leaf ⟨(28, 17636826038336), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00006.record025_result⟩)
 (.branch 27
 (.leaf ⟨(28, 17636893139008), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00006.record026_result⟩)
 (.leaf ⟨(28, 17670914195712), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00006.record027_result⟩)))
 (.branch 29
 (.leaf ⟨(28, 17671987413248), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00006.record028_result⟩)
 (.branch 30
 (.leaf ⟨(28, 17701984763904), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00006.record029_result⟩)
 (.leaf ⟨(28, 17702525599745), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00006.record030_result⟩))))
 (.branch 34
 (.branch 32
 (.leaf ⟨(28, 17702525665280), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00006.record031_result⟩)
 (.branch 33
 (.leaf ⟨(28, 17704149925888), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00006.record032_result⟩)
 (.leaf ⟨(28, 17704414167040), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00006.record033_result⟩)))
 (.branch 35
 (.leaf ⟨(28, 17704421433408), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00006.record034_result⟩)
 (.branch 36
 (.leaf ⟨(28, 17706686349313), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00006.record035_result⟩)
 (.leaf ⟨(28, 17706686414848), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00006.record036_result⟩)))))
 (.branch 43
 (.branch 40
 (.branch 38
 (.leaf ⟨(28, 17715276316672), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00006.record037_result⟩)
 (.branch 39
 (.leaf ⟨(28, 17715410518016), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00006.record038_result⟩)
 (.leaf ⟨(28, 17739902107712), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00006.record039_result⟩)))
 (.branch 41
 (.leaf ⟨(28, 17748223606848), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00006.record040_result⟩)
 (.branch 42
 (.leaf ⟨(28, 17775403728897), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00006.record041_result⟩)
 (.leaf ⟨(28, 17775403794432), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00006.record042_result⟩))))
 (.branch 46
 (.branch 44
 (.leaf ⟨(28, 17777484169216), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00006.record043_result⟩)
 (.branch 45
 (.leaf ⟨(28, 17783725228033), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00006.record044_result⟩)
 (.leaf ⟨(28, 17783993696256), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00006.record045_result⟩)))
 (.branch 48
 (.branch 47
 (.leaf ⟨(28, 17783995777024), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00006.record046_result⟩)
 (.leaf ⟨(28, 17818288406528), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00006.record047_result⟩))
 (.branch 49
 (.leaf ⟨(28, 17921558462592), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00006.record048_result⟩)
 (.leaf ⟨(28, 18152188551232), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00006.record049_result⟩)))))))
 (.branch 75
 (.branch 62
 (.branch 56
 (.branch 53
 (.branch 51
 (.leaf ⟨(28, 18252273090560), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00006.record050_result⟩)
 (.branch 52
 (.leaf ⟨(28, 18252281413632), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00006.record051_result⟩)
 (.leaf ⟨(28, 18270860116224), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00006.record052_result⟩)))
 (.branch 54
 (.leaf ⟨(28, 18271608766464), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00006.record053_result⟩)
 (.branch 55
 (.leaf ⟨(28, 18298251001856), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00006.record054_result⟩)
 (.leaf ⟨(28, 18331486666752), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00006.record055_result⟩))))
 (.branch 59
 (.branch 57
 (.leaf ⟨(28, 18336033275904), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00006.record056_result⟩)
 (.branch 58
 (.leaf ⟨(28, 18340317822976), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00006.record057_result⟩)
 (.leaf ⟨(28, 18406359171072), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00006.record058_result⟩)))
 (.branch 60
 (.leaf ⟨(28, 18406887653376), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00006.record059_result⟩)
 (.branch 61
 (.leaf ⟨(28, 18507820466176), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00006.record060_result⟩)
 (.leaf ⟨(28, 18531047440384), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00006.record061_result⟩)))))
 (.branch 68
 (.branch 65
 (.branch 63
 (.leaf ⟨(28, 18580834893824), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00006.record062_result⟩)
 (.branch 64
 (.leaf ⟨(28, 18697649397824), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00006.record063_result⟩)
 (.leaf ⟨(28, 18701942267968), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00006.record064_result⟩)))
 (.branch 66
 (.leaf ⟨(28, 18710528008256), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00006.record065_result⟩)
 (.branch 67
 (.leaf ⟨(28, 18769569652800), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00006.record066_result⟩)
 (.leaf ⟨(28, 18778155393088), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00006.record067_result⟩))))
 (.branch 71
 (.branch 69
 (.leaf ⟨(28, 18801894686720), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00006.record068_result⟩)
 (.branch 70
 (.leaf ⟨(28, 18885654872064), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00006.record069_result⟩)
 (.leaf ⟨(28, 19014503890944), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00006.record070_result⟩)))
 (.branch 73
 (.branch 72
 (.leaf ⟨(28, 19027512541184), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00006.record071_result⟩)
 (.leaf ⟨(28, 19057442062336), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00006.record072_result⟩))
 (.branch 74
 (.leaf ⟨(28, 19061871230976), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00006.record073_result⟩)
 (.leaf ⟨(28, 19281857282048), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00006.record074_result⟩))))))
 (.branch 87
 (.branch 81
 (.branch 78
 (.branch 76
 (.leaf ⟨(28, 19328632160256), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00006.record075_result⟩)
 (.branch 77
 (.leaf ⟨(28, 19469900447744), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00006.record076_result⟩)
 (.leaf ⟨(28, 19572841250816), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00006.record077_result⟩)))
 (.branch 79
 (.leaf ⟨(28, 19611625980416), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00006.record078_result⟩)
 (.branch 80
 (.leaf ⟨(28, 19611628077056), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00006.record079_result⟩)
 (.leaf ⟨(28, 19623726612480), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00006.record080_result⟩))))
 (.branch 84
 (.branch 82
 (.leaf ⟨(28, 19624511143936), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00006.record081_result⟩)
 (.branch 83
 (.leaf ⟨(28, 19641162268672), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00006.record082_result⟩)
 (.leaf ⟨(28, 19878988759168), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00006.record083_result⟩)))
 (.branch 85
 (.leaf ⟨(28, 19947708235840), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00006.record084_result⟩)
 (.branch 86
 (.leaf ⟨(28, 20019514736640), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00006.record085_result⟩)
 (.leaf ⟨(28, 20079777947712), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00006.record086_result⟩)))))
 (.branch 93
 (.branch 90
 (.branch 88
 (.leaf ⟨(28, 20420825251840), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00006.record087_result⟩)
 (.branch 89
 (.leaf ⟨(28, 20466328666112), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00006.record088_result⟩)
 (.leaf ⟨(28, 20534913925120), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00006.record089_result⟩)))
 (.branch 91
 (.leaf ⟨(28, 20567126179840), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00006.record090_result⟩)
 (.branch 92
 (.leaf ⟨(28, 20732083961856), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00006.record091_result⟩)
 (.leaf ⟨(28, 20732612444160), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00006.record092_result⟩))))
 (.branch 96
 (.branch 94
 (.leaf ⟨(28, 20740669702144), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00006.record093_result⟩)
 (.branch 95
 (.leaf ⟨(28, 20744830451712), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00006.record094_result⟩)
 (.leaf ⟨(28, 20749255442432), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00006.record095_result⟩)))
 (.branch 98
 (.branch 97
 (.leaf ⟨(28, 20828720726016), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00006.record096_result⟩)
 (.leaf ⟨(28, 20965014700032), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00006.record097_result⟩))
 (.branch 99
 (.leaf ⟨(28, 21015950262272), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00006.record098_result⟩)
 (.leaf ⟨(28, 21446017482752), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00006.record099_result⟩))))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (19904 + i))) 0 100 :=
  interval_of_check _ 0 100 (by decide +kernel)

public theorem complete : Block 19904 20004 :=
  block_of_table results 19904 100 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0426
