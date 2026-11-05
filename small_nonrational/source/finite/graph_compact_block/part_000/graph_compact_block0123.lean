module
prelude
import GraphInputsRow24Part00007Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0123
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 44
 (.branch 22
 (.branch 11
 (.branch 5
 (.branch 2
 (.branch 1
 (.leaf ⟨(24, 3647913164800), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00007.record000_result⟩)
 (.leaf ⟨(24, 3664886399232), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00007.record001_result⟩))
 (.branch 3
 (.leaf ⟨(24, 3664894787584), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00007.record002_result⟩)
 (.branch 4
 (.leaf ⟨(24, 3665022746624), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00007.record003_result⟩)
 (.leaf ⟨(24, 3665026908160), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00007.record004_result⟩))))
 (.branch 8
 (.branch 6
 (.leaf ⟨(24, 3665092968448), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00007.record005_result⟩)
 (.branch 7
 (.leaf ⟨(24, 3665487216768), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00007.record006_result⟩)
 (.leaf ⟨(24, 3669187657728), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00007.record007_result⟩)))
 (.branch 9
 (.leaf ⟨(24, 3672370118656), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00007.record008_result⟩)
 (.branch 10
 (.leaf ⟨(24, 3672374280192), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00007.record009_result⟩)
 (.leaf ⟨(24, 3716432298240), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00007.record010_result⟩)))))
 (.branch 16
 (.branch 13
 (.branch 12
 (.leaf ⟨(24, 3758509588480), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00007.record011_result⟩)
 (.leaf ⟨(24, 3758769602816), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00007.record012_result⟩))
 (.branch 14
 (.leaf ⟨(24, 3758780071936), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00007.record013_result⟩)
 (.branch 15
 (.leaf ⟨(24, 3775412601088), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00007.record014_result⟩)
 (.leaf ⟨(24, 3775681069056), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00007.record015_result⟩))))
 (.branch 19
 (.branch 17
 (.leaf ⟨(24, 3775689392128), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00007.record016_result⟩)
 (.branch 18
 (.leaf ⟨(24, 3776083673088), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00007.record017_result⟩)
 (.leaf ⟨(24, 3776217874432), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00007.record018_result⟩)))
 (.branch 20
 (.leaf ⟨(24, 3781880217856), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00007.record019_result⟩)
 (.branch 21
 (.leaf ⟨(24, 3782400280704), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00007.record020_result⟩)
 (.leaf ⟨(24, 3784423014656), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00007.record021_result⟩))))))
 (.branch 33
 (.branch 27
 (.branch 24
 (.branch 23
 (.leaf ⟨(24, 3784480655488), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00007.record022_result⟩)
 (.leaf ⟨(24, 3786420584704), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00007.record023_result⟩))
 (.branch 25
 (.leaf ⟨(24, 3786428973056), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00007.record024_result⟩)
 (.branch 26
 (.leaf ⟨(24, 3786821107968), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00007.record025_result⟩)
 (.leaf ⟨(24, 3790713454848), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00007.record026_result⟩))))
 (.branch 30
 (.branch 28
 (.leaf ⟨(24, 3790721843200), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00007.record027_result⟩)
 (.branch 29
 (.leaf ⟨(24, 3790981857536), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00007.record028_result⟩)
 (.leaf ⟨(24, 3790992326656), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00007.record029_result⟩)))
 (.branch 31
 (.leaf ⟨(24, 3791116058880), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00007.record030_result⟩)
 (.branch 32
 (.leaf ⟨(24, 3793262493952), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00007.record031_result⟩)
 (.leaf ⟨(24, 3796962904192), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00007.record032_result⟩)))))
 (.branch 38
 (.branch 35
 (.branch 34
 (.leaf ⟨(24, 3799307583488), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00007.record033_result⟩)
 (.leaf ⟨(24, 3806147395648), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00007.record034_result⟩))
 (.branch 36
 (.leaf ⟨(24, 3809705230592), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00007.record035_result⟩)
 (.branch 37
 (.leaf ⟨(24, 3809841577984), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00007.record036_result⟩)
 (.leaf ⟨(24, 3809849901056), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00007.record037_result⟩))))
 (.branch 41
 (.branch 39
 (.leaf ⟨(24, 3809973698560), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00007.record038_result⟩)
 (.branch 40
 (.leaf ⟨(24, 3809982021632), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00007.record039_result⟩)
 (.leaf ⟨(24, 3810442362880), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00007.record040_result⟩)))
 (.branch 42
 (.leaf ⟨(24, 3854240415872), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00007.record041_result⟩)
 (.branch 43
 (.leaf ⟨(24, 3866957545488), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00007.record042_result⟩)
 (.leaf ⟨(24, 3867121107072), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00007.record043_result⟩)))))))
 (.branch 66
 (.branch 55
 (.branch 49
 (.branch 46
 (.branch 45
 (.leaf ⟨(24, 3921867800704), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00007.record044_result⟩)
 (.leaf ⟨(24, 3926162718976), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00007.record045_result⟩))
 (.branch 47
 (.leaf ⟨(24, 3926162751616), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00007.record046_result⟩)
 (.branch 48
 (.leaf ⟨(24, 3926164340752), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00007.record047_result⟩)
 (.leaf ⟨(24, 4004396498944), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00007.record048_result⟩))))
 (.branch 52
 (.branch 50
 (.leaf ⟨(24, 4004398514432), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00007.record049_result⟩)
 (.branch 51
 (.leaf ⟨(24, 4008022380608), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00007.record050_result⟩)
 (.leaf ⟨(24, 4068017766400), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00007.record051_result⟩)))
 (.branch 53
 (.leaf ⟨(24, 4076731400448), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00007.record052_result⟩)
 (.branch 54
 (.leaf ⟨(24, 4076741853185), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00007.record053_result⟩)
 (.leaf ⟨(24, 4127759368208), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00007.record054_result⟩)))))
 (.branch 60
 (.branch 57
 (.branch 56
 (.leaf ⟨(24, 4128023609360), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00007.record055_result⟩)
 (.leaf ⟨(24, 4329482551552), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00007.record056_result⟩))
 (.branch 58
 (.leaf ⟨(24, 4329486713088), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00007.record057_result⟩)
 (.branch 59
 (.leaf ⟨(24, 4329486778368), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00007.record058_result⟩)
 (.leaf ⟨(24, 4329886976256), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00007.record059_result⟩))))
 (.branch 63
 (.branch 61
 (.leaf ⟨(24, 4329889349760), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00007.record060_result⟩)
 (.branch 62
 (.leaf ⟨(24, 4329891170432), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00007.record061_result⟩)
 (.leaf ⟨(24, 4330010707976), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00007.record062_result⟩)))
 (.branch 64
 (.leaf ⟨(24, 4333898959104), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00007.record063_result⟩)
 (.branch 65
 (.leaf ⟨(24, 4333899024384), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00007.record064_result⟩)
 (.leaf ⟨(24, 4333911474432), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00007.record065_result⟩))))))
 (.branch 77
 (.branch 71
 (.branch 68
 (.branch 67
 (.leaf ⟨(24, 4333915668992), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00007.record066_result⟩)
 (.leaf ⟨(24, 4333919862784), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00007.record067_result⟩))
 (.branch 69
 (.leaf ⟨(24, 4334167394432), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00007.record068_result⟩)
 (.branch 70
 (.leaf ⟨(24, 4334171456520), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00007.record069_result⟩)
 (.leaf ⟨(24, 4334188232705), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00007.record070_result⟩))))
 (.branch 74
 (.branch 72
 (.leaf ⟨(24, 4338319950080), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00007.record071_result⟩)
 (.branch 73
 (.leaf ⟨(24, 4338472747264), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00007.record072_result⟩)
 (.leaf ⟨(24, 4338476974080), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00007.record073_result⟩)))
 (.branch 75
 (.leaf ⟨(24, 4338483216384), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00007.record074_result⟩)
 (.branch 76
 (.leaf ⟨(24, 4338600642560), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00007.record075_result⟩)
 (.leaf ⟨(24, 4338722554112), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00007.record076_result⟩)))))
 (.branch 83
 (.branch 80
 (.branch 78
 (.leaf ⟨(24, 4342350414080), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00007.record077_result⟩)
 (.branch 79
 (.leaf ⟨(24, 4342887284736), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00007.record078_result⟩)
 (.leaf ⟨(24, 4342895607808), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00007.record079_result⟩)))
 (.branch 81
 (.leaf ⟨(24, 4346649643136), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00007.record080_result⟩)
 (.branch 82
 (.leaf ⟨(24, 4347050066952), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00007.record081_result⟩)
 (.leaf ⟨(24, 4347066843137), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00007.record082_result⟩))))
 (.branch 86
 (.branch 84
 (.leaf ⟨(24, 4359530283008), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00007.record083_result⟩)
 (.branch 85
 (.leaf ⟨(24, 4359668760576), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00007.record084_result⟩)
 (.leaf ⟨(24, 4359802847232), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00007.record085_result⟩)))
 (.branch 87
 (.leaf ⟨(24, 4522401366272), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00007.record086_result⟩)
 (.branch 88
 (.leaf ⟨(24, 4522405593088), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00007.record087_result⟩)
 (.leaf ⟨(24, 4728169693184), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00007.record088_result⟩))))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (8115 + i))) 0 89 :=
  interval_of_check _ 0 89 (by decide +kernel)

public theorem complete : Block 8115 8204 :=
  block_of_table results 8115 89 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0123
