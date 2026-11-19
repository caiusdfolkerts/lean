module
prelude
import GraphInputsRow23Part00001Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0079
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 50
 (.branch 25
 (.branch 12
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(23, 2058094641664), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00001.record000_result⟩)
 (.branch 2
 (.leaf ⟨(23, 2058103029760), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00001.record001_result⟩)
 (.leaf ⟨(23, 2100910391552), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00001.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(23, 2118094225408), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00001.record003_result⟩)
 (.branch 5
 (.leaf ⟨(23, 2132606517504), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00001.record004_result⟩)
 (.leaf ⟨(23, 2132614905856), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00001.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(23, 2132854243584), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00001.record006_result⟩)
 (.branch 8
 (.leaf ⟨(23, 2133007040768), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00001.record007_result⟩)
 (.leaf ⟨(23, 2133011267584), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00001.record008_result⟩)))
 (.branch 10
 (.leaf ⟨(23, 2133122646272), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00001.record009_result⟩)
 (.branch 11
 (.leaf ⟨(23, 2133134936064), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00001.record010_result⟩)
 (.leaf ⟨(23, 2147697559552), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00001.record011_result⟩)))))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf ⟨(23, 2147895740416), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00001.record012_result⟩)
 (.branch 14
 (.leaf ⟨(23, 2150306480128), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00001.record013_result⟩)
 (.leaf ⟨(23, 2150314803200), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00001.record014_result⟩)))
 (.branch 16
 (.leaf ⟨(23, 2418750267648), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00001.record015_result⟩)
 (.branch 17
 (.leaf ⟨(23, 2427340202112), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00001.record016_result⟩)
 (.leaf ⟨(23, 2446399176704), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00001.record017_result⟩))))
 (.branch 21
 (.branch 19
 (.leaf ⟨(23, 2454984916992), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00001.record018_result⟩)
 (.branch 20
 (.leaf ⟨(23, 2455249158144), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00001.record019_result⟩)
 (.leaf ⟨(23, 2455257481216), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00001.record020_result⟩)))
 (.branch 23
 (.branch 22
 (.leaf ⟨(23, 2459277787136), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00001.record021_result⟩)
 (.leaf ⟨(23, 2521559040000), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00001.record022_result⟩))
 (.branch 24
 (.leaf ⟨(23, 2588126806016), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00001.record023_result⟩)
 (.leaf ⟨(23, 2686843944960), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00001.record024_result⟩))))))
 (.branch 37
 (.branch 31
 (.branch 28
 (.branch 26
 (.leaf ⟨(23, 2793211494656), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00001.record025_result⟩)
 (.branch 27
 (.leaf ⟨(23, 2796438950144), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00001.record026_result⟩)
 (.leaf ⟨(23, 2828651204864), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00001.record027_result⟩)))
 (.branch 29
 (.leaf ⟨(23, 2865561141248), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00001.record028_result⟩)
 (.branch 30
 (.leaf ⟨(23, 2874151043072), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00001.record029_result⟩)
 (.leaf ⟨(23, 2897368584448), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00001.record030_result⟩))))
 (.branch 34
 (.branch 32
 (.leaf ⟨(23, 2934146400256), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00001.record031_result⟩)
 (.branch 33
 (.leaf ⟨(23, 2942736302080), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00001.record032_result⟩)
 (.leaf ⟨(23, 2968439029760), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00001.record033_result⟩)))
 (.branch 35
 (.leaf ⟨(23, 2974948556800), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00001.record034_result⟩)
 (.branch 36
 (.leaf ⟨(23, 3034803343616), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00001.record035_result⟩)
 (.leaf ⟨(23, 3102382030848), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00001.record036_result⟩)))))
 (.branch 43
 (.branch 40
 (.branch 38
 (.leaf ⟨(23, 3118952628352), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00001.record037_result⟩)
 (.branch 39
 (.leaf ⟨(23, 3140430659584), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00001.record038_result⟩)
 (.leaf ⟨(23, 3140438982656), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00001.record039_result⟩)))
 (.branch 41
 (.leaf ⟨(23, 3149020561408), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00001.record040_result⟩)
 (.branch 42
 (.leaf ⟨(23, 3153313431552), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00001.record041_result⟩)
 (.leaf ⟨(23, 3157073657856), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00001.record042_result⟩))))
 (.branch 46
 (.branch 44
 (.leaf ⟨(23, 3157610463232), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00001.record043_result⟩)
 (.branch 45
 (.leaf ⟨(23, 3164726165504), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00001.record044_result⟩)
 (.leaf ⟨(23, 3166806540288), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00001.record045_result⟩)))
 (.branch 48
 (.branch 47
 (.leaf ⟨(23, 3200042205184), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00001.record046_result⟩)
 (.leaf ⟨(23, 3208743224064), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00001.record047_result⟩))
 (.branch 49
 (.leaf ⟨(23, 3208751677440), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00001.record048_result⟩)
 (.leaf ⟨(23, 3209015918592), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00001.record049_result⟩)))))))
 (.branch 75
 (.branch 62
 (.branch 56
 (.branch 53
 (.branch 51
 (.leaf ⟨(23, 3209024241664), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00001.record050_result⟩)
 (.branch 52
 (.leaf ⟨(23, 3217605820416), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00001.record051_result⟩)
 (.leaf ⟨(23, 3217737940992), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00001.record052_result⟩)))
 (.branch 54
 (.leaf ⟨(23, 3225658916864), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00001.record053_result⟩)
 (.branch 55
 (.leaf ⟨(23, 3225931481088), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00001.record054_result⟩)
 (.leaf ⟨(23, 3226195722240), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00001.record055_result⟩))))
 (.branch 59
 (.branch 57
 (.leaf ⟨(23, 3226459963392), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00001.record056_result⟩)
 (.branch 58
 (.leaf ⟨(23, 3232254459904), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00001.record057_result⟩)
 (.leaf ⟨(23, 3237067423744), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00001.record058_result⟩)))
 (.branch 60
 (.leaf ⟨(23, 3237075746816), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00001.record059_result⟩)
 (.branch 61
 (.leaf ⟨(23, 3238693765120), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00001.record060_result⟩)
 (.leaf ⟨(23, 3240955478784), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00001.record061_result⟩)))))
 (.branch 68
 (.branch 65
 (.branch 63
 (.leaf ⟨(23, 3240963932160), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00001.record062_result⟩)
 (.branch 64
 (.leaf ⟨(23, 3241228173312), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00001.record063_result⟩)
 (.leaf ⟨(23, 3241236496384), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00001.record064_result⟩)))
 (.branch 66
 (.leaf ⟨(23, 3243308548096), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00001.record065_result⟩)
 (.branch 67
 (.leaf ⟨(23, 3243316871168), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00001.record066_result⟩)
 (.leaf ⟨(23, 3249818075136), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00001.record067_result⟩))))
 (.branch 71
 (.branch 69
 (.leaf ⟨(23, 3249950195712), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00001.record068_result⟩)
 (.branch 70
 (.leaf ⟨(23, 3255654449408), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00001.record069_result⟩)
 (.leaf ⟨(23, 3338676502784), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00001.record070_result⟩)))
 (.branch 73
 (.branch 72
 (.leaf ⟨(23, 3423772639232), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00001.record071_result⟩)
 (.leaf ⟨(23, 3492490018816), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00001.record072_result⟩))
 (.branch 74
 (.leaf ⟨(23, 3524702273536), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00001.record073_result⟩)
 (.leaf ⟨(23, 3527447478272), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00001.record074_result⟩))))))
 (.branch 87
 (.branch 81
 (.branch 78
 (.branch 76
 (.leaf ⟨(23, 3647842877440), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00001.record075_result⟩)
 (.branch 77
 (.leaf ⟨(23, 3784067809536), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00001.record076_result⟩)
 (.leaf ⟨(23, 3786689019904), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00001.record077_result⟩)))
 (.branch 79
 (.leaf ⟨(23, 3853839794432), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00001.record078_result⟩)
 (.branch 80
 (.leaf ⟨(23, 3853839859712), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00001.record079_result⟩)
 (.leaf ⟨(23, 3853967753472), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00001.record080_result⟩))))
 (.branch 84
 (.branch 82
 (.leaf ⟨(23, 3853971915008), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00001.record081_result⟩)
 (.branch 83
 (.leaf ⟨(23, 3853971980288), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00001.record082_result⟩)
 (.leaf ⟨(23, 3854074646784), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00001.record083_result⟩)))
 (.branch 85
 (.leaf ⟨(23, 3861859274768), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00001.record084_result⟩)
 (.branch 86
 (.leaf ⟨(23, 3866953257216), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00001.record085_result⟩)
 (.leaf ⟨(23, 3921595138304), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00001.record086_result⟩)))))
 (.branch 93
 (.branch 90
 (.branch 88
 (.leaf ⟨(23, 3921599299840), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00001.record087_result⟩)
 (.branch 89
 (.leaf ⟨(23, 3921599365120), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00001.record088_result⟩)
 (.leaf ⟨(23, 3921602941184), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00001.record089_result⟩)))
 (.branch 91
 (.leaf ⟨(23, 3922655936512), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00001.record090_result⟩)
 (.branch 92
 (.leaf ⟨(23, 3926160052480), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00001.record091_result⟩)
 (.leaf ⟨(23, 3926283782160), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00001.record092_result⟩))))
 (.branch 96
 (.branch 94
 (.leaf ⟨(23, 3927357521921), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00001.record093_result⟩)
 (.branch 95
 (.leaf ⟨(23, 3927357587456), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00001.record094_result⟩)
 (.leaf ⟨(23, 3935679086592), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00001.record095_result⟩)))
 (.branch 98
 (.branch 97
 (.leaf ⟨(23, 3935947489280), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00001.record096_result⟩)
 (.leaf ⟨(23, 3939302903808), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00001.record097_result⟩))
 (.branch 99
 (.leaf ⟨(23, 4004664868864), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00001.record098_result⟩)
 (.leaf ⟨(23, 4068147789824), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00001.record099_result⟩))))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (5660 + i))) 0 100 :=
  interval_of_check _ 0 100 (by decide +kernel)

public theorem complete : Block 5660 5760 :=
  block_of_table results 5660 100 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0079
