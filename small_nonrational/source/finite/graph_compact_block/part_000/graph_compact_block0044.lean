module
prelude
import GraphInputsRow19Part00004Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0044
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 50
 (.branch 25
 (.branch 12
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(19, 8599812243456), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00004.record000_result⟩)
 (.branch 2
 (.leaf ⟨(19, 8601355685888), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00004.record001_result⟩)
 (.leaf ⟨(19, 8605549985792), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00004.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(19, 8605772873728), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00004.record003_result⟩)
 (.branch 5
 (.leaf ⟨(19, 8609677185024), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00004.record004_result⟩)
 (.leaf ⟨(19, 8616847376640), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00004.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(19, 8616983724032), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00004.record006_result⟩)
 (.branch 8
 (.leaf ⟨(19, 8616992047104), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00004.record007_result⟩)
 (.leaf ⟨(19, 8617256288256), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00004.record008_result⟩)))
 (.branch 10
 (.leaf ⟨(19, 8617388408832), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00004.record009_result⟩)
 (.branch 11
 (.leaf ⟨(19, 8617887564032), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00004.record010_result⟩)
 (.leaf ⟨(19, 8618023911424), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00004.record011_result⟩)))))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf ⟨(19, 8618032234496), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00004.record012_result⟩)
 (.branch 14
 (.leaf ⟨(19, 8618255122432), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00004.record013_result⟩)
 (.leaf ⟨(19, 8618428596224), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00004.record014_result⟩)))
 (.branch 16
 (.leaf ⟨(19, 8618791927808), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00004.record015_result⟩)
 (.branch 17
 (.leaf ⟨(19, 8629407188992), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00004.record016_result⟩)
 (.leaf ⟨(19, 8633567938560), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00004.record017_result⟩))))
 (.branch 21
 (.branch 19
 (.leaf ⟨(19, 8641889437696), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00004.record018_result⟩)
 (.branch 20
 (.leaf ⟨(19, 8654627733504), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00004.record019_result⟩)
 (.leaf ⟨(19, 8654636056576), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00004.record020_result⟩)))
 (.branch 23
 (.branch 22
 (.leaf ⟨(19, 8682448420864), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00004.record021_result⟩)
 (.leaf ⟨(19, 8682456743936), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00004.record022_result⟩))
 (.branch 24
 (.leaf ⟨(19, 8697980158208), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00004.record023_result⟩)
 (.leaf ⟨(19, 8727533289472), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00004.record024_result⟩))))))
 (.branch 37
 (.branch 31
 (.branch 28
 (.branch 26
 (.leaf ⟨(19, 8729676284160), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00004.record025_result⟩)
 (.branch 27
 (.leaf ⟨(19, 8729684672512), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00004.record026_result⟩)
 (.leaf ⟨(19, 8730081034240), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00004.record027_result⟩)))
 (.branch 29
 (.leaf ⟨(19, 8730192412928), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00004.record028_result⟩)
 (.branch 30
 (.leaf ⟨(19, 8730204702720), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00004.record029_result⟩)
 (.leaf ⟨(19, 8730733248768), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00004.record030_result⟩))))
 (.branch 34
 (.branch 32
 (.leaf ⟨(19, 8731005878272), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00004.record031_result⟩)
 (.branch 33
 (.leaf ⟨(19, 8731270119424), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00004.record032_result⟩)
 (.leaf ⟨(19, 8731945535488), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00004.record033_result⟩)))
 (.branch 35
 (.leaf ⟨(19, 8732004385024), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00004.record034_result⟩)
 (.branch 36
 (.leaf ⟨(19, 8732227469312), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00004.record035_result⟩)
 (.leaf ⟨(19, 8732234743809), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00004.record036_result⟩)))))
 (.branch 43
 (.branch 40
 (.branch 38
 (.leaf ⟨(19, 8733086253056), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00004.record037_result⟩)
 (.branch 39
 (.leaf ⟨(19, 8733350494208), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00004.record038_result⟩)
 (.leaf ⟨(19, 8733358817280), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00004.record039_result⟩)))
 (.branch 41
 (.leaf ⟨(19, 8735166627840), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00004.record040_result⟩)
 (.branch 42
 (.leaf ⟨(19, 8735703433216), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00004.record041_result⟩)
 (.leaf ⟨(19, 8740838309888), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00004.record042_result⟩))))
 (.branch 46
 (.branch 44
 (.leaf ⟨(19, 8744767326208), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00004.record043_result⟩)
 (.branch 45
 (.leaf ⟨(19, 8745096578056), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00004.record044_result⟩)
 (.leaf ⟨(19, 8745696395520), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00004.record045_result⟩)))
 (.branch 48
 (.branch 47
 (.leaf ⟨(19, 8747913117696), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00004.record046_result⟩)
 (.leaf ⟨(19, 8748185681920), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00004.record047_result⟩))
 (.branch 49
 (.leaf ⟨(19, 8766049288448), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00004.record048_result⟩)
 (.leaf ⟨(19, 8766586159104), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00004.record049_result⟩)))))))
 (.branch 75
 (.branch 62
 (.branch 56
 (.branch 53
 (.branch 51
 (.leaf ⟨(19, 8766594482176), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00004.record050_result⟩)
 (.branch 52
 (.leaf ⟨(19, 8766833885184), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00004.record051_result⟩)
 (.leaf ⟨(19, 8775180222464), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00004.record052_result⟩)))
 (.branch 54
 (.leaf ⟨(19, 8778932060416), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00004.record053_result⟩)
 (.branch 55
 (.leaf ⟨(19, 8779316133888), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00004.record054_result⟩)
 (.leaf ⟨(19, 8779473092608), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00004.record055_result⟩))))
 (.branch 59
 (.branch 57
 (.leaf ⟨(19, 8783208284416), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00004.record056_result⟩)
 (.branch 58
 (.leaf ⟨(19, 8783229157376), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00004.record057_result⟩)
 (.leaf ⟨(19, 8783501721600), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00004.record058_result⟩)))
 (.branch 60
 (.leaf ⟨(19, 8784013427200), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00004.record059_result⟩)
 (.branch 61
 (.leaf ⟨(19, 8784013688832), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00004.record060_result⟩)
 (.leaf ⟨(19, 8792335056896), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00004.record061_result⟩)))))
 (.branch 68
 (.branch 65
 (.branch 63
 (.leaf ⟨(19, 8920452071680), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00004.record062_result⟩)
 (.branch 64
 (.leaf ⟨(19, 8920452136960), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00004.record063_result⟩)
 (.leaf ⟨(19, 8926897651840), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00004.record064_result⟩)))
 (.branch 66
 (.leaf ⟨(19, 8983572217856), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00004.record065_result⟩)
 (.branch 67
 (.leaf ⟨(19, 8989037395968), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00004.record066_result⟩)
 (.leaf ⟨(19, 8991322161280), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00004.record067_result⟩))))
 (.branch 71
 (.branch 69
 (.leaf ⟨(19, 9023534416000), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00004.record068_result⟩)
 (.branch 70
 (.leaf ⟨(19, 9056565690368), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00004.record069_result⟩)
 (.leaf ⟨(19, 9056770080896), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00004.record070_result⟩)))
 (.branch 73
 (.branch 72
 (.leaf ⟨(19, 9065407250432), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00004.record071_result⟩)
 (.leaf ⟨(19, 9126610518016), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00004.record072_result⟩))
 (.branch 74
 (.leaf ⟨(19, 9133421019392), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00004.record073_result⟩)
 (.leaf ⟨(19, 9133553139968), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00004.record074_result⟩))))))
 (.branch 87
 (.branch 81
 (.branch 78
 (.branch 76
 (.leaf ⟨(19, 9168481697920), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00004.record075_result⟩)
 (.branch 77
 (.leaf ⟨(19, 9202846138369), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00004.record076_result⟩)
 (.leaf ⟨(19, 9232906207360), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00004.record077_result⟩)))
 (.branch 79
 (.leaf ⟨(19, 9536528285696), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00004.record078_result⟩)
 (.branch 80
 (.leaf ⟨(19, 9536534495360), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00004.record079_result⟩)
 (.leaf ⟨(19, 9545369845760), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00004.record080_result⟩))))
 (.branch 84
 (.branch 82
 (.leaf ⟨(19, 9600069804288), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00004.record081_result⟩)
 (.branch 83
 (.leaf ⟨(19, 9614699593728), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00004.record082_result⟩)
 (.leaf ⟨(19, 9682804572672), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00004.record083_result⟩)))
 (.branch 85
 (.leaf ⟨(19, 9682808733697), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00004.record084_result⟩)
 (.branch 86
 (.leaf ⟨(19, 9805825581312), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00004.record085_result⟩)
 (.leaf ⟨(19, 9820851732480), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00004.record086_result⟩)))))
 (.branch 93
 (.branch 90
 (.branch 88
 (.leaf ⟨(19, 9822932107264), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00004.record087_result⟩)
 (.branch 89
 (.leaf ⟨(19, 9953361281152), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00004.record088_result⟩)
 (.leaf ⟨(19, 10017769013376), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00004.record089_result⟩)))
 (.branch 91
 (.leaf ⟨(19, 10041207914496), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00004.record090_result⟩)
 (.branch 92
 (.leaf ⟨(19, 10095195865088), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00004.record091_result⟩)
 (.leaf ⟨(19, 10129488494592), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00004.record092_result⟩))))
 (.branch 96
 (.branch 94
 (.leaf ⟨(19, 10162724159488), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00004.record093_result⟩)
 (.branch 95
 (.leaf ⟨(19, 10164182941696), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00004.record094_result⟩)
 (.leaf ⟨(19, 10164589560896), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00004.record095_result⟩)))
 (.branch 98
 (.branch 97
 (.leaf ⟨(19, 10167136550912), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00004.record096_result⟩)
 (.leaf ⟨(19, 10230765789312), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00004.record097_result⟩))
 (.branch 99
 (.leaf ⟨(19, 10232426168832), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00004.record098_result⟩)
 (.leaf ⟨(19, 10485504246016), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00004.record099_result⟩))))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (2498 + i))) 0 100 :=
  interval_of_check _ 0 100 (by decide +kernel)

public theorem complete : Block 2498 2598 :=
  block_of_table results 2498 100 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0044
