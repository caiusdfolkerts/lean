module
prelude
import GraphInputsRow28Part00007Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0427
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 48
 (.branch 24
 (.branch 12
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(28, 21513508520192), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00007.record000_result⟩)
 (.branch 2
 (.leaf ⟨(28, 21528125112320), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00007.record001_result⟩)
 (.leaf ⟨(28, 21530708869120), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00007.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(28, 21660065333248), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00007.record003_result⟩)
 (.branch 5
 (.leaf ⟨(28, 21668386832384), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00007.record004_result⟩)
 (.leaf ⟨(28, 21668915314688), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00007.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(28, 21672547581952), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00007.record006_result⟩)
 (.branch 8
 (.leaf ⟨(28, 21805549125632), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00007.record007_result⟩)
 (.leaf ⟨(28, 21857227046912), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00007.record008_result⟩)))
 (.branch 10
 (.leaf ⟨(28, 21878699720704), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00007.record009_result⟩)
 (.branch 11
 (.leaf ⟨(28, 21926084870144), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00007.record010_result⟩)
 (.leaf ⟨(28, 21934934851584), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00007.record011_result⟩)))))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf ⟨(28, 21947417100288), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00007.record012_result⟩)
 (.branch 14
 (.leaf ⟨(28, 21951577849856), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00007.record013_result⟩)
 (.leaf ⟨(28, 21993567043840), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00007.record014_result⟩)))
 (.branch 16
 (.leaf ⟨(28, 21993765224704), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00007.record015_result⟩)
 (.branch 17
 (.leaf ⟨(28, 22043462483968), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00007.record016_result⟩)
 (.leaf ⟨(28, 22077408051456), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00007.record017_result⟩))))
 (.branch 21
 (.branch 19
 (.leaf ⟨(28, 22146538553344), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00007.record018_result⟩)
 (.branch 20
 (.leaf ⟨(28, 22179774218240), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00007.record019_result⟩)
 (.leaf ⟨(28, 22182166069248), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00007.record020_result⟩)))
 (.branch 22
 (.leaf ⟨(28, 22627569696768), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00007.record021_result⟩)
 (.branch 23
 (.leaf ⟨(28, 22669651083264), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00007.record022_result⟩)
 (.leaf ⟨(28, 22734075592704), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00007.record023_result⟩))))))
 (.branch 36
 (.branch 30
 (.branch 27
 (.branch 25
 (.leaf ⟨(28, 22737699536896), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00007.record024_result⟩)
 (.branch 26
 (.leaf ⟨(28, 22862924611584), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00007.record025_result⟩)
 (.leaf ⟨(28, 22875134296064), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00007.record026_result⟩)))
 (.branch 28
 (.leaf ⟨(28, 22875803222016), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00007.record027_result⟩)
 (.branch 29
 (.leaf ⟨(28, 22910161911808), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00007.record028_result⟩)
 (.leaf ⟨(28, 22978144305152), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00007.record029_result⟩))))
 (.branch 33
 (.branch 31
 (.leaf ⟨(28, 23091380494400), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00007.record030_result⟩)
 (.branch 32
 (.leaf ⟨(28, 23383682072576), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00007.record031_result⟩)
 (.leaf ⟨(28, 23421264068608), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00007.record032_result⟩)))
 (.branch 34
 (.leaf ⟨(28, 23424888012800), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00007.record033_result⟩)
 (.branch 35
 (.leaf ⟨(28, 23455622758400), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00007.record034_result⟩)
 (.leaf ⟨(28, 23459180642304), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00007.record035_result⟩)))))
 (.branch 42
 (.branch 39
 (.branch 37
 (.leaf ⟨(28, 23768894275584), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00007.record036_result⟩)
 (.branch 38
 (.leaf ⟨(28, 23971017785344), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00007.record037_result⟩)
 (.leaf ⟨(28, 23974650052608), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00007.record038_result⟩)))
 (.branch 40
 (.leaf ⟨(28, 24043763793920), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00007.record039_result⟩)
 (.branch 41
 (.leaf ⟨(28, 24054107013120), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00007.record040_result⟩)
 (.leaf ⟨(28, 24091016822784), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00007.record041_result⟩))))
 (.branch 45
 (.branch 43
 (.leaf ⟨(28, 24108188303360), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00007.record042_result⟩)
 (.branch 44
 (.leaf ⟨(28, 24190623686720), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00007.record043_result⟩)
 (.leaf ⟨(28, 24194793373952), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00007.record044_result⟩)))
 (.branch 46
 (.leaf ⟨(28, 24208080912512), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00007.record045_result⟩)
 (.branch 47
 (.leaf ⟨(28, 24229189844992), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00007.record046_result⟩)
 (.leaf ⟨(28, 24276901068800), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00007.record047_result⟩)))))))
 (.branch 72
 (.branch 60
 (.branch 54
 (.branch 51
 (.branch 49
 (.leaf ⟨(28, 24298777641216), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00007.record048_result⟩)
 (.branch 50
 (.leaf ⟨(28, 24299054366720), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00007.record049_result⟩)
 (.leaf ⟨(28, 24312337661952), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00007.record050_result⟩)))
 (.branch 52
 (.leaf ⟨(28, 24345754746880), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00007.record051_result⟩)
 (.branch 53
 (.leaf ⟨(28, 24417695432704), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00007.record052_result⟩)
 (.leaf ⟨(28, 24421253316608), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00007.record053_result⟩))))
 (.branch 57
 (.branch 55
 (.leaf ⟨(28, 24473277833280), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00007.record054_result⟩)
 (.branch 56
 (.leaf ⟨(28, 24512185761792), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00007.record055_result⟩)
 (.leaf ⟨(28, 24573932208128), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00007.record056_result⟩)))
 (.branch 58
 (.leaf ⟨(28, 24591103688704), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00007.record057_result⟩)
 (.branch 59
 (.leaf ⟨(28, 24742404882432), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00007.record058_result⟩)
 (.leaf ⟨(28, 24742413205504), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00007.record059_result⟩)))))
 (.branch 66
 (.branch 63
 (.branch 61
 (.leaf ⟨(28, 24745488187648), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00007.record060_result⟩)
 (.branch 62
 (.leaf ⟨(28, 24746259910656), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00007.record061_result⟩)
 (.leaf ⟨(28, 24778471903232), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00007.record062_result⟩)))
 (.branch 64
 (.leaf ⟨(28, 24779545379328), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00007.record063_result⟩)
 (.branch 65
 (.leaf ⟨(28, 24792300257280), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00007.record064_result⟩)
 (.leaf ⟨(28, 24826592886784), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00007.record065_result⟩))))
 (.branch 69
 (.branch 67
 (.leaf ⟨(28, 24868137467904), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00007.record066_result⟩)
 (.branch 68
 (.leaf ⟨(28, 24868665950208), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00007.record067_result⟩)
 (.leaf ⟨(28, 24933090459648), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00007.record068_result⟩)))
 (.branch 70
 (.leaf ⟨(28, 24936722726912), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00007.record069_result⟩)
 (.branch 71
 (.leaf ⟨(28, 25020369797120), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00007.record070_result⟩)
 (.leaf ⟨(28, 25032348663808), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00007.record071_result⟩))))))
 (.branch 84
 (.branch 78
 (.branch 75
 (.branch 73
 (.leaf ⟨(28, 25125583847424), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00007.record072_result⟩)
 (.branch 74
 (.leaf ⟨(28, 25126112329728), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00007.record073_result⟩)
 (.leaf ⟨(28, 25134169587712), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00007.record074_result⟩)))
 (.branch 76
 (.leaf ⟨(28, 25142738681856), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00007.record075_result⟩)
 (.branch 77
 (.leaf ⟨(28, 25153614446592), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00007.record076_result⟩)
 (.leaf ⟨(28, 25177167495168), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00007.record077_result⟩))))
 (.branch 81
 (.branch 79
 (.leaf ⟨(28, 25190260015104), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00007.record078_result⟩)
 (.branch 80
 (.leaf ⟨(28, 25199109996544), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00007.record079_result⟩)
 (.leaf ⟨(28, 25211592245248), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00007.record080_result⟩)))
 (.branch 82
 (.leaf ⟨(28, 25215752994816), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00007.record081_result⟩)
 (.branch 83
 (.leaf ⟨(28, 25327560622336), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00007.record082_result⟩)
 (.leaf ⟨(28, 25396418510848), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00007.record083_result⟩)))))
 (.branch 90
 (.branch 87
 (.branch 85
 (.leaf ⟨(28, 25405276815360), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00007.record084_result⟩)
 (.branch 86
 (.leaf ⟨(28, 25413598314496), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00007.record085_result⟩)
 (.leaf ⟨(28, 25414126796800), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00007.record086_result⟩)))
 (.branch 88
 (.leaf ⟨(28, 25417759064064), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00007.record087_result⟩)
 (.branch 89
 (.leaf ⟨(28, 25465003769856), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00007.record088_result⟩)
 (.leaf ⟨(28, 25482183573504), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00007.record089_result⟩))))
 (.branch 93
 (.branch 91
 (.leaf ⟨(28, 25482712055808), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00007.record090_result⟩)
 (.branch 92
 (.leaf ⟨(28, 25497216024576), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00007.record091_result⟩)
 (.leaf ⟨(28, 25602438529024), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00007.record092_result⟩)))
 (.branch 95
 (.branch 94
 (.leaf ⟨(28, 25611032592384), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00007.record093_result⟩)
 (.leaf ⟨(28, 25611561074688), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00007.record094_result⟩))
 (.branch 96
 (.leaf ⟨(28, 25623911202816), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00007.record095_result⟩)
 (.leaf ⟨(28, 25634650783744), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00007.record096_result⟩))))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (20004 + i))) 0 97 :=
  interval_of_check _ 0 97 (by decide +kernel)

public theorem complete : Block 20004 20101 :=
  block_of_table results 20004 97 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0427
