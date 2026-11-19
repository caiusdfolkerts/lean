module
prelude
import GraphInputsRow19Part00011Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0051
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 50
 (.branch 25
 (.branch 12
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(19, 16781956612096), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00011.record000_result⟩)
 (.branch 2
 (.leaf ⟨(19, 16805542297600), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00011.record001_result⟩)
 (.leaf ⟨(19, 16807622672384), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00011.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(19, 16817347690496), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00011.record003_result⟩)
 (.branch 5
 (.leaf ⟨(19, 16840856707328), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00011.record004_result⟩)
 (.leaf ⟨(19, 16849450835968), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00011.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(19, 16873070592000), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00011.record006_result⟩)
 (.branch 8
 (.leaf ⟨(19, 16906153165376), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00011.record007_result⟩)
 (.leaf ⟨(19, 16918564577280), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00011.record008_result⟩)))
 (.branch 10
 (.leaf ⟨(19, 16918565617664), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00011.record009_result⟩)
 (.branch 11
 (.leaf ⟨(19, 16939504402688), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00011.record010_result⟩)
 (.leaf ⟨(19, 16973799178240), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00011.record011_result⟩)))))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf ⟨(19, 16973866278912), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00011.record012_result⟩)
 (.branch 14
 (.leaf ⟨(19, 16975996848128), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00011.record013_result⟩)
 (.leaf ⟨(19, 16976135211008), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00011.record014_result⟩)))
 (.branch 16
 (.leaf ⟨(19, 16976137159688), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00011.record015_result⟩)
 (.branch 17
 (.leaf ⟨(19, 16978282678304), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00011.record016_result⟩)
 (.leaf ⟨(19, 16978283594760), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00011.record017_result⟩))))
 (.branch 21
 (.branch 19
 (.leaf ⟨(19, 16982370027776), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00011.record018_result⟩)
 (.branch 20
 (.leaf ⟨(19, 17003775656992), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00011.record019_result⟩)
 (.leaf ⟨(19, 17003776705536), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00011.record020_result⟩)))
 (.branch 23
 (.branch 22
 (.leaf ⟨(19, 17003842634244), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00011.record021_result⟩)
 (.leaf ⟨(19, 17010236883200), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00011.record022_result⟩))
 (.branch 24
 (.leaf ⟨(19, 17010373230592), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00011.record023_result⟩)
 (.leaf ⟨(19, 17010381553664), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00011.record024_result⟩))))))
 (.branch 37
 (.branch 31
 (.branch 28
 (.branch 26
 (.leaf ⟨(19, 17010620956672), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00011.record025_result⟩)
 (.branch 27
 (.leaf ⟨(19, 17014533980160), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00011.record026_result⟩)
 (.leaf ⟨(19, 17014806544384), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00011.record027_result⟩)))
 (.branch 29
 (.leaf ⟨(19, 17015318511616), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00011.record028_result⟩)
 (.branch 30
 (.leaf ⟨(19, 17023103074304), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00011.record029_result⟩)
 (.leaf ⟨(19, 17023639879680), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00011.record030_result⟩))))
 (.branch 34
 (.branch 32
 (.leaf ⟨(19, 17040282877952), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00011.record031_result⟩)
 (.branch 33
 (.leaf ⟨(19, 17045959803136), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00011.record032_result⟩)
 (.leaf ⟨(19, 17045963964672), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00011.record033_result⟩)))
 (.branch 35
 (.leaf ⟨(19, 17045964029952), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00011.record034_result⟩)
 (.branch 36
 (.leaf ⟨(19, 17051576471808), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00011.record035_result⟩)
 (.leaf ⟨(19, 17052399108352), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00011.record036_result⟩)))))
 (.branch 43
 (.branch 40
 (.branch 38
 (.leaf ⟨(19, 17052405415936), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00011.record037_result⟩)
 (.branch 39
 (.leaf ⟨(19, 17052439941376), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00011.record038_result⟩)
 (.leaf ⟨(19, 17052669657088), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00011.record039_result⟩)))
 (.branch 41
 (.leaf ⟨(19, 17053851324432), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00011.record040_result⟩)
 (.branch 42
 (.leaf ⟨(19, 17061025681664), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00011.record041_result⟩)
 (.leaf ⟨(19, 17081374933248), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00011.record042_result⟩))))
 (.branch 46
 (.branch 44
 (.leaf ⟨(19, 17081379160064), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00011.record043_result⟩)
 (.branch 45
 (.leaf ⟨(19, 17082435666176), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00011.record044_result⟩)
 (.leaf ⟨(19, 17082435731456), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00011.record045_result⟩)))
 (.branch 48
 (.branch 47
 (.leaf ⟨(19, 17082464928000), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00011.record046_result⟩)
 (.leaf ⟨(19, 17082473316352), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00011.record047_result⟩))
 (.branch 49
 (.leaf ⟨(19, 17082964541696), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00011.record048_result⟩)
 (.leaf ⟨(19, 17085938352128), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00011.record049_result⟩)))))))
 (.branch 75
 (.branch 62
 (.branch 56
 (.branch 53
 (.branch 51
 (.leaf ⟨(19, 17085939847424), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00011.record050_result⟩)
 (.branch 52
 (.leaf ⟨(19, 17086063577104), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00011.record051_result⟩)
 (.leaf ⟨(19, 17086766186496), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00011.record052_result⟩)))
 (.branch 54
 (.leaf ⟨(19, 17086856888576), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00011.record053_result⟩)
 (.branch 55
 (.leaf ⟨(19, 17087026200832), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00011.record054_result⟩)
 (.leaf ⟨(19, 17087030427648), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00011.record055_result⟩))))
 (.branch 59
 (.branch 57
 (.leaf ⟨(19, 17087125291264), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00011.record056_result⟩)
 (.branch 58
 (.leaf ⟨(19, 17087137320960), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00011.record057_result⟩)
 (.leaf ⟨(19, 17090480705792), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00011.record058_result⟩)))
 (.branch 60
 (.leaf ⟨(19, 17090786427136), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00011.record059_result⟩)
 (.branch 61
 (.leaf ⟨(19, 17091323297792), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00011.record060_result⟩)
 (.leaf ⟨(19, 17091331620864), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00011.record061_result⟩)))))
 (.branch 68
 (.branch 65
 (.branch 63
 (.leaf ⟨(19, 17091554508800), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00011.record062_result⟩)
 (.branch 64
 (.leaf ⟨(19, 17091595862016), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00011.record063_result⟩)
 (.leaf ⟨(19, 17103669199104), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00011.record064_result⟩)))
 (.branch 66
 (.leaf ⟨(19, 17103805546496), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00011.record065_result⟩)
 (.branch 67
 (.leaf ⟨(19, 17103813869568), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00011.record066_result⟩)
 (.leaf ⟨(19, 17103945990144), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00011.record067_result⟩))))
 (.branch 71
 (.branch 69
 (.leaf ⟨(19, 17104036757504), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00011.record068_result⟩)
 (.branch 70
 (.leaf ⟨(19, 17104573562880), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00011.record069_result⟩)
 (.leaf ⟨(19, 17106888851712), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00011.record070_result⟩)))
 (.branch 73
 (.branch 72
 (.leaf ⟨(19, 17107157319680), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00011.record071_result⟩)
 (.leaf ⟨(19, 17107165642752), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00011.record072_result⟩))
 (.branch 74
 (.leaf ⟨(19, 17107660574720), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00011.record073_result⟩)
 (.leaf ⟨(19, 17111443669008), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00011.record074_result⟩))))))
 (.branch 87
 (.branch 81
 (.branch 78
 (.branch 76
 (.leaf ⟨(19, 17120016664592), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00011.record075_result⟩)
 (.branch 77
 (.leaf ⟨(19, 17146872660224), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00011.record076_result⟩)
 (.leaf ⟨(19, 17146881048576), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00011.record077_result⟩)))
 (.branch 79
 (.leaf ⟨(19, 17154401698048), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00011.record078_result⟩)
 (.branch 80
 (.leaf ⟨(19, 17154653585664), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00011.record079_result⟩)
 (.leaf ⟨(19, 17154657812480), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00011.record080_result⟩))))
 (.branch 84
 (.branch 82
 (.leaf ⟨(19, 17154665615360), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00011.record081_result⟩)
 (.branch 83
 (.leaf ⟨(19, 17154682390528), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00011.record082_result⟩)
 (.leaf ⟨(19, 17154904953088), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00011.record083_result⟩)))
 (.branch 85
 (.leaf ⟨(19, 17171296583936), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00011.record084_result⟩)
 (.branch 86
 (.leaf ⟨(19, 17171333840896), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00011.record085_result⟩)
 (.leaf ⟨(19, 17171342163968), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00011.record086_result⟩)))))
 (.branch 93
 (.branch 90
 (.branch 88
 (.leaf ⟨(19, 17171565051904), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00011.record087_result⟩)
 (.branch 89
 (.leaf ⟨(19, 17171573374976), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00011.record088_result⟩)
 (.leaf ⟨(19, 17172084822016), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00011.record089_result⟩)))
 (.branch 91
 (.leaf ⟨(19, 17172101857280), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00011.record090_result⟩)
 (.branch 92
 (.leaf ⟨(19, 17172629946368), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00011.record091_result⟩)
 (.leaf ⟨(19, 17182180249856), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00011.record092_result⟩))))
 (.branch 96
 (.branch 94
 (.leaf ⟨(19, 17182312370432), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00011.record093_result⟩)
 (.branch 95
 (.leaf ⟨(19, 17183662964992), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00011.record094_result⟩)
 (.leaf ⟨(19, 17183667191808), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00011.record095_result⟩)))
 (.branch 98
 (.branch 97
 (.leaf ⟨(19, 17187960061952), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00011.record096_result⟩)
 (.leaf ⟨(19, 17187968385024), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00011.record097_result⟩))
 (.branch 99
 (.leaf ⟨(19, 17188232626176), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00011.record098_result⟩)
 (.leaf ⟨(19, 17189015916800), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00011.record099_result⟩))))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (3196 + i))) 0 100 :=
  interval_of_check _ 0 100 (by decide +kernel)

public theorem complete : Block 3196 3296 :=
  block_of_table results 3196 100 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0051
