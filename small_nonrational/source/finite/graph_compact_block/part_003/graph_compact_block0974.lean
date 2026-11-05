module
prelude
import GraphInputsSix0Part00009Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0974
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 50
 (.branch 25
 (.branch 12
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(32, 3238962233344), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00009.record000_result⟩)
 (.branch 2
 (.leaf ⟨(32, 3238964314112), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00009.record001_result⟩)
 (.leaf ⟨(32, 3238965354496), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00009.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(32, 3238968443008), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00009.record003_result⟩)
 (.branch 5
 (.leaf ⟨(32, 3239019808896), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00009.record004_result⟩)
 (.leaf ⟨(32, 3240959738112), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00009.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(32, 3240968126464), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00009.record006_result⟩)
 (.branch 8
 (.leaf ⟨(32, 3241236496385), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00009.record007_result⟩)
 (.leaf ⟨(32, 3243316871169), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00009.record008_result⟩)))
 (.branch 10
 (.leaf ⟨(32, 3247209187456), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00009.record009_result⟩)
 (.branch 11
 (.leaf ⟨(32, 3247337113856), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00009.record010_result⟩)
 (.leaf ⟨(32, 3247341308032), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00009.record011_result⟩)))))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf ⟨(32, 3247407368320), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00009.record012_result⟩)
 (.branch 14
 (.leaf ⟨(32, 3247552102528), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00009.record013_result⟩)
 (.leaf ⟨(32, 3247554183296), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00009.record014_result⟩)))
 (.branch 16
 (.leaf ⟨(32, 3247554215936), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00009.record015_result⟩)
 (.branch 17
 (.leaf ⟨(32, 3338945003648), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00009.record016_result⟩)
 (.leaf ⟨(32, 3343239954560), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00009.record017_result⟩))))
 (.branch 21
 (.branch 19
 (.leaf ⟨(32, 3351561453696), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00009.record018_result⟩)
 (.branch 20
 (.leaf ⟨(32, 3373237633152), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00009.record019_result⟩)
 (.leaf ⟨(32, 3377532584064), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00009.record020_result⟩)))
 (.branch 23
 (.branch 22
 (.leaf ⟨(32, 3385719881856), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00009.record021_result⟩)
 (.leaf ⟨(32, 3385854083200), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00009.record022_result⟩))
 (.branch 24
 (.leaf ⟨(32, 3385920143488), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00009.record023_result⟩)
 (.leaf ⟨(32, 3414914302208), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00009.record024_result⟩))))))
 (.branch 37
 (.branch 31
 (.branch 28
 (.branch 26
 (.leaf ⟨(32, 3415182704896), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00009.record025_result⟩)
 (.branch 27
 (.leaf ⟨(32, 3415182770176), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00009.record026_result⟩)
 (.leaf ⟨(32, 3415316906240), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00009.record027_result⟩)))
 (.branch 29
 (.leaf ⟨(32, 3428201807936), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00009.record028_result⟩)
 (.branch 30
 (.leaf ⟨(32, 3454439342208), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00009.record029_result⟩)
 (.leaf ⟨(32, 3483631681792), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00009.record030_result⟩))))
 (.branch 34
 (.branch 32
 (.leaf ⟨(32, 3483900084480), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00009.record031_result⟩)
 (.branch 33
 (.leaf ⟨(32, 3483900149760), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00009.record032_result⟩)
 (.leaf ⟨(32, 3483902165248), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00009.record033_result⟩)))
 (.branch 35
 (.leaf ⟨(32, 3492626317376), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00009.record034_result⟩)
 (.branch 36
 (.leaf ⟨(32, 3526986047552), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00009.record035_result⟩)
 (.leaf ⟨(32, 3527311261952), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00009.record036_result⟩)))))
 (.branch 43
 (.branch 40
 (.branch 38
 (.leaf ⟨(32, 3527311327232), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00009.record037_result⟩)
 (.branch 39
 (.leaf ⟨(32, 3527447478528), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00009.record038_result⟩)
 (.leaf ⟨(32, 3527455866880), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00009.record039_result⟩)))
 (.branch 41
 (.leaf ⟨(32, 3527856390144), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00009.record040_result⟩)
 (.branch 42
 (.leaf ⟨(32, 3591874101376), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00009.record041_result⟩)
 (.leaf ⟨(32, 3621066440960), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00009.record042_result⟩))))
 (.branch 46
 (.branch 44
 (.leaf ⟨(32, 3621072683264), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00009.record043_result⟩)
 (.branch 45
 (.leaf ⟨(32, 3643362296064), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00009.record044_result⟩)
 (.leaf ⟨(32, 3646715109632), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00009.record045_result⟩)))
 (.branch 48
 (.branch 47
 (.leaf ⟨(32, 3647842877696), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00009.record046_result⟩)
 (.leaf ⟨(32, 3647913099520), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00009.record047_result⟩))
 (.branch 49
 (.leaf ⟨(32, 3647913164800), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00009.record048_result⟩)
 (.leaf ⟨(32, 3648115474560), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00009.record049_result⟩)))))))
 (.branch 75
 (.branch 62
 (.branch 56
 (.branch 53
 (.branch 51
 (.leaf ⟨(32, 3648117555328), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00009.record050_result⟩)
 (.branch 52
 (.leaf ⟨(32, 3664886399232), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00009.record051_result⟩)
 (.leaf ⟨(32, 3664894787584), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00009.record052_result⟩)))
 (.branch 54
 (.leaf ⟨(32, 3665018519808), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00009.record053_result⟩)
 (.branch 55
 (.leaf ⟨(32, 3665022746624), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00009.record054_result⟩)
 (.leaf ⟨(32, 3665026908160), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00009.record055_result⟩))))
 (.branch 59
 (.branch 57
 (.leaf ⟨(32, 3665092968448), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00009.record056_result⟩)
 (.branch 58
 (.leaf ⟨(32, 3665286955136), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00009.record057_result⟩)
 (.leaf ⟨(32, 3665487216768), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00009.record058_result⟩)))
 (.branch 60
 (.leaf ⟨(32, 3669187657728), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00009.record059_result⟩)
 (.branch 61
 (.leaf ⟨(32, 3672370118656), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00009.record060_result⟩)
 (.leaf ⟨(32, 3672374280192), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00009.record061_result⟩)))))
 (.branch 68
 (.branch 65
 (.branch 63
 (.leaf ⟨(32, 3716432298240), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00009.record062_result⟩)
 (.branch 64
 (.leaf ⟨(32, 3749667963136), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00009.record063_result⟩)
 (.leaf ⟨(32, 3750188025984), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00009.record064_result⟩)))
 (.branch 66
 (.leaf ⟨(32, 3758501200128), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00009.record065_result⟩)
 (.branch 67
 (.leaf ⟨(32, 3758509588480), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00009.record066_result⟩)
 (.leaf ⟨(32, 3758769602816), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00009.record067_result⟩))))
 (.branch 71
 (.branch 69
 (.leaf ⟨(32, 3758780071936), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00009.record068_result⟩)
 (.branch 70
 (.leaf ⟨(32, 3758903804160), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00009.record069_result⟩)
 (.leaf ⟨(32, 3771788705856), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00009.record070_result⟩)))
 (.branch 73
 (.branch 72
 (.leaf ⟨(32, 3775412601088), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00009.record071_result⟩)
 (.leaf ⟨(32, 3775681069056), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00009.record072_result⟩))
 (.branch 74
 (.leaf ⟨(32, 3775689392128), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00009.record073_result⟩)
 (.leaf ⟨(32, 3776083673088), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00009.record074_result⟩))))))
 (.branch 87
 (.branch 81
 (.branch 78
 (.branch 76
 (.leaf ⟨(32, 3776217874432), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00009.record075_result⟩)
 (.branch 77
 (.leaf ⟨(32, 3781880217856), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00009.record076_result⟩)
 (.leaf ⟨(32, 3782400280704), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00009.record077_result⟩)))
 (.branch 79
 (.leaf ⟨(32, 3784026652928), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00009.record078_result⟩)
 (.branch 80
 (.leaf ⟨(32, 3784423014656), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00009.record079_result⟩)
 (.leaf ⟨(32, 3784480655488), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00009.record080_result⟩))))
 (.branch 84
 (.branch 82
 (.leaf ⟨(32, 3786420584704), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00009.record081_result⟩)
 (.branch 83
 (.leaf ⟨(32, 3786428973056), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00009.record082_result⟩)
 (.leaf ⟨(32, 3786821107968), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00009.record083_result⟩)))
 (.branch 85
 (.leaf ⟨(32, 3786831577088), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00009.record084_result⟩)
 (.branch 86
 (.leaf ⟨(32, 3790713454848), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00009.record085_result⟩)
 (.leaf ⟨(32, 3790721843200), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00009.record086_result⟩)))))
 (.branch 93
 (.branch 90
 (.branch 88
 (.leaf ⟨(32, 3790981857536), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00009.record087_result⟩)
 (.branch 89
 (.leaf ⟨(32, 3790992326656), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00009.record088_result⟩)
 (.leaf ⟨(32, 3791116058880), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00009.record089_result⟩)))
 (.branch 91
 (.leaf ⟨(32, 3793262493952), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00009.record090_result⟩)
 (.branch 92
 (.leaf ⟨(32, 3796962904192), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00009.record091_result⟩)
 (.leaf ⟨(32, 3799307583488), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00009.record092_result⟩))))
 (.branch 96
 (.branch 94
 (.leaf ⟨(32, 3806147395648), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00009.record093_result⟩)
 (.branch 95
 (.leaf ⟨(32, 3809705230592), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00009.record094_result⟩)
 (.leaf ⟨(32, 3809841577984), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00009.record095_result⟩)))
 (.branch 98
 (.branch 97
 (.leaf ⟨(32, 3809849901056), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00009.record096_result⟩)
 (.leaf ⟨(32, 3809973698560), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00009.record097_result⟩))
 (.branch 99
 (.leaf ⟨(32, 3809982021632), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00009.record098_result⟩)
 (.leaf ⟨(32, 3810442362880), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00009.record099_result⟩))))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (27686 + i))) 0 100 :=
  interval_of_check _ 0 100 (by decide +kernel)

public theorem complete : Block 27686 27786 :=
  block_of_table results 27686 100 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0974
