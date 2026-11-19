module
prelude
import GraphInputsRow27Part00001Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0404
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 50
 (.branch 25
 (.branch 12
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(27, 1981468966912), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00001.record000_result⟩)
 (.branch 2
 (.leaf ⟨(27, 1981737369600), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00001.record001_result⟩)
 (.leaf ⟨(27, 1981861101824), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00001.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(27, 1981997449216), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00001.record003_result⟩)
 (.branch 5
 (.leaf ⟨(27, 1982005772288), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00001.record004_result⟩)
 (.leaf ⟨(27, 1986030239744), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00001.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(27, 2016290078720), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00001.record006_result⟩)
 (.branch 8
 (.leaf ⟨(27, 2016298401792), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00001.record007_result⟩)
 (.leaf ⟨(27, 2018787229952), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00001.record008_result⟩)))
 (.branch 10
 (.leaf ⟨(27, 2018787295232), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00001.record009_result⟩)
 (.branch 11
 (.leaf ⟨(27, 2019777741056), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00001.record010_result⟩)
 (.leaf ⟨(27, 2019777806336), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00001.record011_result⟩)))))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf ⟨(27, 2019781772544), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00001.record012_result⟩)
 (.branch 14
 (.leaf ⟨(27, 2019922280449), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00001.record013_result⟩)
 (.leaf ⟨(27, 2020314480896), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00001.record014_result⟩)))
 (.branch 16
 (.leaf ⟨(27, 2020318642177), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00001.record015_result⟩)
 (.branch 17
 (.leaf ⟨(27, 2020322869248), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00001.record016_result⟩)
 (.leaf ⟨(27, 2020459151360), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00001.record017_result⟩))))
 (.branch 21
 (.branch 19
 (.leaf ⟨(27, 2027388239880), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00001.record018_result⟩)
 (.branch 20
 (.leaf ⟨(27, 2032085860352), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00001.record019_result⟩)
 (.leaf ⟨(27, 2057293726720), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00001.record020_result⟩)))
 (.branch 23
 (.branch 22
 (.leaf ⟨(27, 2057301918724), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00001.record021_result⟩)
 (.leaf ⟨(27, 2057566159364), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00001.record022_result⟩))
 (.branch 24
 (.leaf ⟨(27, 2057566289921), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00001.record023_result⟩)
 (.leaf ⟨(27, 2057838789632), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00001.record024_result⟩))))))
 (.branch 37
 (.branch 31
 (.branch 28
 (.branch 26
 (.leaf ⟨(27, 2058107224064), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00001.record025_result⟩)
 (.branch 27
 (.leaf ⟨(27, 2126684160000), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00001.record026_result⟩)
 (.leaf ⟨(27, 2126692483072), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00001.record027_result⟩)))
 (.branch 29
 (.leaf ⟨(27, 2132594098184), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00001.record028_result⟩)
 (.branch 30
 (.leaf ⟨(27, 2150449037312), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00001.record029_result⟩)
 (.leaf ⟨(27, 2420325318656), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00001.record030_result⟩))))
 (.branch 34
 (.branch 32
 (.leaf ⟨(27, 2420424409088), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00001.record031_result⟩)
 (.branch 33
 (.leaf ⟨(27, 2446667644928), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00001.record032_result⟩)
 (.leaf ⟨(27, 2453040889856), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00001.record033_result⟩)))
 (.branch 35
 (.leaf ⟨(27, 2454716645376), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00001.record034_result⟩)
 (.branch 36
 (.leaf ⟨(27, 2454720611584), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00001.record035_result⟩)
 (.leaf ⟨(27, 2455257481217), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00001.record036_result⟩)))))
 (.branch 43
 (.branch 40
 (.branch 38
 (.leaf ⟨(27, 2459552465024), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00001.record037_result⟩)
 (.branch 39
 (.leaf ⟨(27, 2463438472448), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00001.record038_result⟩)
 (.leaf ⟨(27, 2469679596800), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00001.record039_result⟩)))
 (.branch 41
 (.leaf ⟨(27, 2469820170240), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00001.record040_result⟩)
 (.branch 42
 (.leaf ⟨(27, 2470018351104), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00001.record041_result⟩)
 (.leaf ⟨(27, 2470212305152), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00001.record042_result⟩))))
 (.branch 46
 (.branch 44
 (.leaf ⟨(27, 2470220693504), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00001.record043_result⟩)
 (.branch 45
 (.leaf ⟨(27, 2513971495168), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00001.record044_result⟩)
 (.leaf ⟨(27, 2579419414784), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00001.record045_result⟩)))
 (.branch 48
 (.branch 47
 (.leaf ⟨(27, 2584240734336), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00001.record046_result⟩)
 (.leaf ⟨(27, 2588131033088), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00001.record047_result⟩))
 (.branch 49
 (.leaf ⟨(27, 2588401483904), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00001.record048_result⟩)
 (.leaf ⟨(27, 2590277468160), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00001.record049_result⟩)))))))
 (.branch 75
 (.branch 62
 (.branch 56
 (.branch 53
 (.branch 51
 (.leaf ⟨(27, 2590481858688), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00001.record050_result⟩)
 (.branch 52
 (.leaf ⟨(27, 2601017966592), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00001.record051_result⟩)
 (.leaf ⟨(27, 2601410134144), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00001.record052_result⟩)))
 (.branch 54
 (.leaf ⟨(27, 2605302448384), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00001.record053_result⟩)
 (.branch 55
 (.leaf ⟨(27, 2605306675200), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00001.record054_result⟩)
 (.leaf ⟨(27, 2605310836736), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00001.record055_result⟩))))
 (.branch 59
 (.branch 57
 (.leaf ⟨(27, 2605570883712), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00001.record056_result⟩)
 (.branch 58
 (.leaf ⟨(27, 2605839319040), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00001.record057_result⟩)
 (.leaf ⟨(27, 2605843480576), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00001.record058_result⟩)))
 (.branch 60
 (.leaf ⟨(27, 2607250702592), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00001.record059_result⟩)
 (.branch 61
 (.leaf ⟨(27, 2607259090944), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00001.record060_result⟩)
 (.leaf ⟨(27, 2607382823168), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00001.record061_result⟩)))))
 (.branch 68
 (.branch 65
 (.branch 63
 (.leaf ⟨(27, 2607387049984), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00001.record062_result⟩)
 (.branch 64
 (.leaf ⟨(27, 2607391211520), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00001.record063_result⟩)
 (.leaf ⟨(27, 2607457271808), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00001.record064_result⟩)))
 (.branch 66
 (.leaf ⟨(27, 2607651258496), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00001.record065_result⟩)
 (.branch 67
 (.leaf ⟨(27, 2607851520128), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00001.record066_result⟩)
 (.leaf ⟨(27, 2675976470528), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00001.record067_result⟩))))
 (.branch 71
 (.branch 69
 (.leaf ⟨(27, 2686848172032), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00001.record068_result⟩)
 (.branch 70
 (.leaf ⟨(27, 2686914232320), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00001.record069_result⟩)
 (.leaf ⟨(27, 2687116542080), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00001.record070_result⟩)))
 (.branch 73
 (.branch 72
 (.leaf ⟨(27, 2687118622848), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00001.record071_result⟩)
 (.leaf ⟨(27, 2693557928064), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00001.record072_result⟩))
 (.branch 74
 (.leaf ⟨(27, 2981854446848), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00001.record073_result⟩)
 (.leaf ⟨(27, 2982395543552), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00001.record074_result⟩))))))
 (.branch 87
 (.branch 81
 (.branch 78
 (.branch 76
 (.leaf ⟨(27, 3119632121856), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00001.record075_result⟩)
 (.branch 77
 (.leaf ⟨(27, 3120094543872), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00001.record076_result⟩)
 (.leaf ⟨(27, 3120098705408), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00001.record077_result⟩)))
 (.branch 79
 (.leaf ⟨(27, 3131329052672), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00001.record078_result⟩)
 (.branch 80
 (.leaf ⟨(27, 3131849050240), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00001.record079_result⟩)
 (.leaf ⟨(27, 3135886163968), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00001.record080_result⟩))))
 (.branch 84
 (.branch 82
 (.leaf ⟨(27, 3140438982657), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00001.record081_result⟩)
 (.branch 83
 (.leaf ⟨(27, 3153330208768), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00001.record082_result⟩)
 (.leaf ⟨(27, 3153334370304), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00001.record083_result⟩)))
 (.branch 85
 (.leaf ⟨(27, 3157077950464), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00001.record084_result⟩)
 (.branch 86
 (.leaf ⟨(27, 3157337997440), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00001.record085_result⟩)
 (.leaf ⟨(27, 3162259898624), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00001.record086_result⟩)))))
 (.branch 93
 (.branch 90
 (.branch 88
 (.leaf ⟨(27, 3162325958912), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00001.record087_result⟩)
 (.branch 89
 (.leaf ⟨(27, 3165678772480), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00001.record088_result⟩)
 (.leaf ⟨(27, 3166810767360), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00001.record089_result⟩)))
 (.branch 91
 (.leaf ⟨(27, 3174392471552), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00001.record090_result⟩)
 (.branch 92
 (.leaf ⟨(27, 3191333781504), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00001.record091_result⟩)
 (.leaf ⟨(27, 3191337943040), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00001.record092_result⟩))))
 (.branch 96
 (.branch 94
 (.leaf ⟨(27, 3195611169024), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00001.record093_result⟩)
 (.branch 95
 (.leaf ⟨(27, 3199889213696), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00001.record094_result⟩)
 (.leaf ⟨(27, 3200310673408), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00001.record095_result⟩)))
 (.branch 98
 (.branch 97
 (.leaf ⟨(27, 3209024241665), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00001.record096_result⟩)
 (.leaf ⟨(27, 3213195493504), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00001.record097_result⟩))
 (.branch 99
 (.leaf ⟨(27, 3213195526144), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00001.record098_result⟩)
 (.leaf ⟨(27, 3225663209472), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00001.record099_result⟩))))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (17773 + i))) 0 100 :=
  interval_of_check _ 0 100 (by decide +kernel)

public theorem complete : Block 17773 17873 :=
  block_of_table results 17773 100 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0404
