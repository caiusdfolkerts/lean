module
prelude
import GraphInputsRow26Part00006Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0322
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 45
 (.branch 22
 (.branch 11
 (.branch 5
 (.branch 2
 (.branch 1
 (.leaf ⟨(26, 3226063602688), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00006.record000_result⟩)
 (.leaf ⟨(26, 3226191528576), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00006.record001_result⟩))
 (.branch 3
 (.leaf ⟨(26, 3229903798528), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00006.record002_result⟩)
 (.branch 4
 (.leaf ⟨(26, 3230105100544), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00006.record003_result⟩)
 (.leaf ⟨(26, 3232101468416), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00006.record004_result⟩))))
 (.branch 8
 (.branch 6
 (.leaf ⟨(26, 3232522928128), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00006.record005_result⟩)
 (.branch 7
 (.leaf ⟨(26, 3232527057024), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00006.record006_result⟩)
 (.leaf ⟨(26, 3232529137792), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00006.record007_result⟩)))
 (.branch 9
 (.leaf ⟨(26, 3234405122048), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00006.record008_result⟩)
 (.branch 10
 (.leaf ⟨(26, 3234669297920), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00006.record009_result⟩)
 (.leaf ⟨(26, 3234669363200), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00006.record010_result⟩)))))
 (.branch 16
 (.branch 13
 (.branch 12
 (.leaf ⟨(26, 3234673492096), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00006.record011_result⟩)
 (.leaf ⟨(26, 3234726938752), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00006.record012_result⟩))
 (.branch 14
 (.leaf ⟨(26, 3238962168064), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00006.record013_result⟩)
 (.branch 15
 (.leaf ⟨(26, 3238962233344), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00006.record014_result⟩)
 (.leaf ⟨(26, 3238964314112), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00006.record015_result⟩))))
 (.branch 19
 (.branch 17
 (.leaf ⟨(26, 3238965354496), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00006.record016_result⟩)
 (.branch 18
 (.leaf ⟨(26, 3238968443008), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00006.record017_result⟩)
 (.leaf ⟨(26, 3240968126464), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00006.record018_result⟩)))
 (.branch 20
 (.leaf ⟨(26, 3243316871169), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00006.record019_result⟩)
 (.branch 21
 (.leaf ⟨(26, 3247209187456), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00006.record020_result⟩)
 (.leaf ⟨(26, 3247341308032), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00006.record021_result⟩))))))
 (.branch 33
 (.branch 27
 (.branch 24
 (.branch 23
 (.leaf ⟨(26, 3247407368320), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00006.record022_result⟩)
 (.leaf ⟨(26, 3247554183296), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00006.record023_result⟩))
 (.branch 25
 (.leaf ⟨(26, 3247554215936), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00006.record024_result⟩)
 (.branch 26
 (.leaf ⟨(26, 3338945003648), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00006.record025_result⟩)
 (.leaf ⟨(26, 3454439342208), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00006.record026_result⟩))))
 (.branch 30
 (.branch 28
 (.leaf ⟨(26, 3483900149760), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00006.record027_result⟩)
 (.branch 29
 (.leaf ⟨(26, 3483902165248), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00006.record028_result⟩)
 (.leaf ⟨(26, 3527311261952), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00006.record029_result⟩)))
 (.branch 31
 (.leaf ⟨(26, 3527311327232), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00006.record030_result⟩)
 (.branch 32
 (.leaf ⟨(26, 3527455866880), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00006.record031_result⟩)
 (.leaf ⟨(26, 3527856390144), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00006.record032_result⟩)))))
 (.branch 39
 (.branch 36
 (.branch 34
 (.leaf ⟨(26, 3591874101376), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00006.record033_result⟩)
 (.branch 35
 (.leaf ⟨(26, 3664886399232), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00006.record034_result⟩)
 (.leaf ⟨(26, 3664894787584), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00006.record035_result⟩)))
 (.branch 37
 (.leaf ⟨(26, 3665018519808), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00006.record036_result⟩)
 (.branch 38
 (.leaf ⟨(26, 3665022746624), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00006.record037_result⟩)
 (.leaf ⟨(26, 3665026908160), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00006.record038_result⟩))))
 (.branch 42
 (.branch 40
 (.leaf ⟨(26, 3665092968448), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00006.record039_result⟩)
 (.branch 41
 (.leaf ⟨(26, 3665286955136), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00006.record040_result⟩)
 (.leaf ⟨(26, 3669187657728), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00006.record041_result⟩)))
 (.branch 43
 (.leaf ⟨(26, 3750188025984), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00006.record042_result⟩)
 (.branch 44
 (.leaf ⟨(26, 3758509588480), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00006.record043_result⟩)
 (.leaf ⟨(26, 3758769602816), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00006.record044_result⟩)))))))
 (.branch 67
 (.branch 56
 (.branch 50
 (.branch 47
 (.branch 46
 (.leaf ⟨(26, 3758780071936), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00006.record045_result⟩)
 (.leaf ⟨(26, 3775412601088), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00006.record046_result⟩))
 (.branch 48
 (.leaf ⟨(26, 3775681069056), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00006.record047_result⟩)
 (.branch 49
 (.leaf ⟨(26, 3775689392128), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00006.record048_result⟩)
 (.leaf ⟨(26, 3776083673088), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00006.record049_result⟩))))
 (.branch 53
 (.branch 51
 (.leaf ⟨(26, 3776217874432), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00006.record050_result⟩)
 (.branch 52
 (.leaf ⟨(26, 3782400280704), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00006.record051_result⟩)
 (.leaf ⟨(26, 3784423014656), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00006.record052_result⟩)))
 (.branch 54
 (.leaf ⟨(26, 3786420584704), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00006.record053_result⟩)
 (.branch 55
 (.leaf ⟨(26, 3786428973056), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00006.record054_result⟩)
 (.leaf ⟨(26, 3790713454848), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00006.record055_result⟩)))))
 (.branch 61
 (.branch 58
 (.branch 57
 (.leaf ⟨(26, 3790721843200), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00006.record056_result⟩)
 (.leaf ⟨(26, 3790981857536), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00006.record057_result⟩))
 (.branch 59
 (.leaf ⟨(26, 3790992326656), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00006.record058_result⟩)
 (.branch 60
 (.leaf ⟨(26, 3791116058880), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00006.record059_result⟩)
 (.leaf ⟨(26, 3796962904192), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00006.record060_result⟩))))
 (.branch 64
 (.branch 62
 (.leaf ⟨(26, 3799307583488), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00006.record061_result⟩)
 (.branch 63
 (.leaf ⟨(26, 3809841577984), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00006.record062_result⟩)
 (.leaf ⟨(26, 3809849901056), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00006.record063_result⟩)))
 (.branch 65
 (.leaf ⟨(26, 3809973698560), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00006.record064_result⟩)
 (.branch 66
 (.leaf ⟨(26, 3809982021632), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00006.record065_result⟩)
 (.leaf ⟨(26, 3849520234880), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00006.record066_result⟩))))))
 (.branch 78
 (.branch 72
 (.branch 69
 (.branch 68
 (.leaf ⟨(26, 3852873568640), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00006.record067_result⟩)
 (.leaf ⟨(26, 3854240415872), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00006.record068_result⟩))
 (.branch 70
 (.leaf ⟨(26, 3866957545488), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00006.record069_result⟩)
 (.branch 71
 (.leaf ⟨(26, 3921582131472), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00006.record070_result⟩)
 (.leaf ⟨(26, 3921867800704), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00006.record071_result⟩))))
 (.branch 75
 (.branch 73
 (.leaf ⟨(26, 3926162751616), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00006.record072_result⟩)
 (.branch 74
 (.leaf ⟨(26, 3934752653440), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00006.record073_result⟩)
 (.leaf ⟨(26, 4004396498944), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00006.record074_result⟩)))
 (.branch 76
 (.leaf ⟨(26, 4004398514432), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00006.record075_result⟩)
 (.branch 77
 (.leaf ⟨(26, 4076731400448), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00006.record076_result⟩)
 (.leaf ⟨(26, 4128023609360), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00006.record077_result⟩)))))
 (.branch 84
 (.branch 81
 (.branch 79
 (.leaf ⟨(26, 4140908462096), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00006.record078_result⟩)
 (.branch 80
 (.leaf ⟨(26, 4329465645064), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00006.record079_result⟩)
 (.leaf ⟨(26, 4329889349760), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00006.record080_result⟩)))
 (.branch 82
 (.leaf ⟨(26, 4333626393608), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00006.record081_result⟩)
 (.branch 83
 (.leaf ⟨(26, 4333899024384), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00006.record082_result⟩)
 (.leaf ⟨(26, 4338472747264), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00006.record083_result⟩))))
 (.branch 87
 (.branch 85
 (.leaf ⟨(26, 4338476974080), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00006.record084_result⟩)
 (.branch 86
 (.leaf ⟨(26, 4338483216384), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00006.record085_result⟩)
 (.leaf ⟨(26, 4342350414080), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00006.record086_result⟩)))
 (.branch 88
 (.leaf ⟨(26, 4342887284736), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00006.record087_result⟩)
 (.branch 89
 (.leaf ⟨(26, 4342895607808), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00006.record088_result⟩)
 (.leaf ⟨(26, 4346649643136), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00006.record089_result⟩))))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (14384 + i))) 0 90 :=
  interval_of_check _ 0 90 (by decide +kernel)

public theorem complete : Block 14384 14474 :=
  block_of_table results 14384 90 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0322
