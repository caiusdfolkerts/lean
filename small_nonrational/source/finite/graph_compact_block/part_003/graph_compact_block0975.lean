module
prelude
import GraphInputsSix0Part00010Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0975
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 50
 (.branch 25
 (.branch 12
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(32, 3849421144448), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00010.record000_result⟩)
 (.branch 2
 (.leaf ⟨(32, 3849518154112), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00010.record001_result⟩)
 (.leaf ⟨(32, 3849520234880), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00010.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(32, 3852741448064), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00010.record003_result⟩)
 (.branch 5
 (.leaf ⟨(32, 3852873568640), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00010.record004_result⟩)
 (.leaf ⟨(32, 3853839859968), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00010.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(32, 3853971980544), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00010.record006_result⟩)
 (.branch 8
 (.leaf ⟨(32, 3854236221696), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00010.record007_result⟩)
 (.leaf ⟨(32, 3854240415872), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00010.record008_result⟩)))
 (.branch 10
 (.leaf ⟨(32, 3854343176208), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00010.record009_result⟩)
 (.branch 11
 (.leaf ⟨(32, 3857436922240), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00010.record010_result⟩)
 (.leaf ⟨(32, 3858535366784), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00010.record011_result⟩)))))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf ⟨(32, 3866957545488), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00010.record012_result⟩)
 (.branch 14
 (.leaf ⟨(32, 3867121074432), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00010.record013_result⟩)
 (.leaf ⟨(32, 3867121107072), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00010.record014_result⟩)))
 (.branch 16
 (.leaf ⟨(32, 3921577969936), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00010.record015_result⟩)
 (.branch 17
 (.leaf ⟨(32, 3921582131472), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00010.record016_result⟩)
 (.leaf ⟨(32, 3921599365376), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00010.record017_result⟩))))
 (.branch 21
 (.branch 19
 (.leaf ⟨(32, 3921867800704), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00010.record018_result⟩)
 (.branch 20
 (.leaf ⟨(32, 3921871470608), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00010.record019_result⟩)
 (.leaf ⟨(32, 3922924372096), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00010.record020_result⟩)))
 (.branch 23
 (.branch 22
 (.leaf ⟨(32, 3923196805376), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00010.record021_result⟩)
 (.leaf ⟨(32, 3923196870656), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00010.record022_result⟩))
 (.branch 24
 (.leaf ⟨(32, 3926162718976), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00010.record023_result⟩)
 (.leaf ⟨(32, 3926162751616), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00010.record024_result⟩))))))
 (.branch 37
 (.branch 31
 (.branch 28
 (.branch 26
 (.leaf ⟨(32, 3926164340752), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00010.record025_result⟩)
 (.branch 27
 (.leaf ⟨(32, 3927089152256), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00010.record026_result⟩)
 (.leaf ⟨(32, 3927219290368), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00010.record027_result⟩)))
 (.branch 29
 (.leaf ⟨(32, 3927219323008), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00010.record028_result⟩)
 (.branch 30
 (.leaf ⟨(32, 3927357554944), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00010.record029_result⟩)
 (.leaf ⟨(32, 3927357620224), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00010.record030_result⟩))))
 (.branch 34
 (.branch 32
 (.leaf ⟨(32, 3927491756288), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00010.record031_result⟩)
 (.branch 33
 (.leaf ⟨(32, 3930712969472), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00010.record032_result⟩)
 (.leaf ⟨(32, 3934750081040), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00010.record033_result⟩)))
 (.branch 35
 (.leaf ⟨(32, 3934752653440), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00010.record034_result⟩)
 (.branch 36
 (.leaf ⟨(32, 3943597871168), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00010.record035_result⟩)
 (.leaf ⟨(32, 3990184624384), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00010.record036_result⟩)))))
 (.branch 43
 (.branch 40
 (.branch 38
 (.leaf ⟨(32, 3995806531840), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00010.record037_result⟩)
 (.branch 39
 (.leaf ⟨(32, 3996074934528), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00010.record038_result⟩)
 (.leaf ⟨(32, 3996074999808), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00010.record039_result⟩)))
 (.branch 41
 (.leaf ⟨(32, 3996077015296), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00010.record040_result⟩)
 (.branch 42
 (.leaf ⟨(32, 3999298228480), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00010.record041_result⟩)
 (.leaf ⟨(32, 4004392272128), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00010.record042_result⟩))))
 (.branch 46
 (.branch 44
 (.leaf ⟨(32, 4004396433664), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00010.record043_result⟩)
 (.branch 45
 (.leaf ⟨(32, 4004396498944), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00010.record044_result⟩)
 (.leaf ⟨(32, 4004398514432), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00010.record045_result⟩)))
 (.branch 48
 (.branch 47
 (.leaf ⟨(32, 4004801167424), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00010.record046_result⟩)
 (.leaf ⟨(32, 4008022380608), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00010.record047_result⟩))
 (.branch 49
 (.leaf ⟨(32, 4067745136896), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00010.record048_result⟩)
 (.leaf ⟨(32, 4068009378048), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00010.record049_result⟩)))))))
 (.branch 75
 (.branch 62
 (.branch 56
 (.branch 53
 (.branch 51
 (.leaf ⟨(32, 4068017766400), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00010.record050_result⟩)
 (.branch 52
 (.leaf ⟨(32, 4076731400448), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00010.record051_result⟩)
 (.leaf ⟨(32, 4076741853185), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00010.record052_result⟩)))
 (.branch 54
 (.leaf ⟨(32, 4127627247632), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00010.record053_result⟩)
 (.branch 55
 (.leaf ⟨(32, 4127759368208), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00010.record054_result⟩)
 (.leaf ⟨(32, 4128023609360), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00010.record055_result⟩))))
 (.branch 59
 (.branch 57
 (.leaf ⟨(32, 4136468746496), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00010.record056_result⟩)
 (.branch 58
 (.leaf ⟨(32, 4140908462096), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00010.record057_result⟩)
 (.leaf ⟨(32, 4329344254208), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00010.record058_result⟩)))
 (.branch 60
 (.leaf ⟨(32, 4329346074880), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00010.record059_result⟩)
 (.branch 61
 (.leaf ⟨(32, 4329346138120), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00010.record060_result⟩)
 (.leaf ⟨(32, 4329465645064), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00010.record061_result⟩)))))
 (.branch 68
 (.branch 65
 (.branch 63
 (.leaf ⟨(32, 4329482551552), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00010.record062_result⟩)
 (.branch 64
 (.leaf ⟨(32, 4329486713088), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00010.record063_result⟩)
 (.leaf ⟨(32, 4329486778368), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00010.record064_result⟩)))
 (.branch 66
 (.leaf ⟨(32, 4329490614528), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00010.record065_result⟩)
 (.branch 67
 (.leaf ⟨(32, 4329886976256), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00010.record066_result⟩)
 (.leaf ⟨(32, 4329889349760), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00010.record067_result⟩))))
 (.branch 71
 (.branch 69
 (.leaf ⟨(32, 4329889382400), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00010.record068_result⟩)
 (.branch 70
 (.leaf ⟨(32, 4329891170432), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00010.record069_result⟩)
 (.leaf ⟨(32, 4330010707976), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00010.record070_result⟩)))
 (.branch 73
 (.branch 72
 (.leaf ⟨(32, 4333626393608), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00010.record071_result⟩)
 (.leaf ⟨(32, 4333898959104), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00010.record072_result⟩))
 (.branch 74
 (.leaf ⟨(32, 4333899024384), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00010.record073_result⟩)
 (.leaf ⟨(32, 4333911474432), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00010.record074_result⟩))))))
 (.branch 87
 (.branch 81
 (.branch 78
 (.branch 76
 (.leaf ⟨(32, 4333915668992), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00010.record075_result⟩)
 (.branch 77
 (.leaf ⟨(32, 4333919862784), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00010.record076_result⟩)
 (.leaf ⟨(32, 4334167394432), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00010.record077_result⟩)))
 (.branch 79
 (.leaf ⟨(32, 4334171456520), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00010.record078_result⟩)
 (.branch 80
 (.leaf ⟨(32, 4334188232705), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00010.record079_result⟩)
 (.leaf ⟨(32, 4334427603200), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00010.record080_result⟩))))
 (.branch 84
 (.branch 82
 (.leaf ⟨(32, 4334439892992), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00010.record081_result⟩)
 (.branch 83
 (.leaf ⟨(32, 4338204344576), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00010.record082_result⟩)
 (.leaf ⟨(32, 4338212732928), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00010.record083_result⟩)))
 (.branch 85
 (.leaf ⟨(32, 4338319950080), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00010.record084_result⟩)
 (.branch 86
 (.leaf ⟨(32, 4338472747264), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00010.record085_result⟩)
 (.leaf ⟨(32, 4338476974080), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00010.record086_result⟩)))))
 (.branch 93
 (.branch 90
 (.branch 88
 (.leaf ⟨(32, 4338483216384), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00010.record087_result⟩)
 (.branch 89
 (.leaf ⟨(32, 4338588352768), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00010.record088_result⟩)
 (.leaf ⟨(32, 4338600642560), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00010.record089_result⟩)))
 (.branch 91
 (.leaf ⟨(32, 4338722554112), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00010.record090_result⟩)
 (.branch 92
 (.leaf ⟨(32, 4342350414080), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00010.record091_result⟩)
 (.leaf ⟨(32, 4342623043584), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00010.record092_result⟩))))
 (.branch 96
 (.branch 94
 (.leaf ⟨(32, 4342887284736), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00010.record093_result⟩)
 (.branch 95
 (.leaf ⟨(32, 4342895607808), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00010.record094_result⟩)
 (.leaf ⟨(32, 4343017243392), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00010.record095_result⟩)))
 (.branch 98
 (.branch 97
 (.leaf ⟨(32, 4346645448960), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00010.record096_result⟩)
 (.leaf ⟨(32, 4346649643136), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00010.record097_result⟩))
 (.branch 99
 (.leaf ⟨(32, 4347050066952), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00010.record098_result⟩)
 (.leaf ⟨(32, 4347066843137), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00010.record099_result⟩))))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (27786 + i))) 0 100 :=
  interval_of_check _ 0 100 (by decide +kernel)

public theorem complete : Block 27786 27886 :=
  block_of_table results 27786 100 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0975
