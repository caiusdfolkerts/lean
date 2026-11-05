module
prelude
import GraphInputsRow26Part00004Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0320
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 47
 (.branch 23
 (.branch 11
 (.branch 5
 (.branch 2
 (.branch 1
 (.leaf ⟨(26, 2020322869248), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00004.record000_result⟩)
 (.leaf ⟨(26, 2020450828288), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00004.record001_result⟩))
 (.branch 3
 (.leaf ⟨(26, 2020459151360), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00004.record002_result⟩)
 (.branch 4
 (.leaf ⟨(26, 2027380113664), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00004.record003_result⟩)
 (.leaf ⟨(26, 2027388239880), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00004.record004_result⟩))))
 (.branch 8
 (.branch 6
 (.leaf ⟨(26, 2027514315008), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00004.record005_result⟩)
 (.branch 7
 (.leaf ⟨(26, 2027520360456), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00004.record006_result⟩)
 (.leaf ⟨(26, 2031796584456), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00004.record007_result⟩)))
 (.branch 9
 (.leaf ⟨(26, 2032085860352), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00004.record008_result⟩)
 (.branch 10
 (.leaf ⟨(26, 2035957334024), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00004.record009_result⟩)
 (.leaf ⟨(26, 2036091535368), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00004.record010_result⟩)))))
 (.branch 17
 (.branch 14
 (.branch 12
 (.leaf ⟨(26, 2036378730496), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00004.record011_result⟩)
 (.branch 13
 (.leaf ⟨(26, 2049517289473), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00004.record012_result⟩)
 (.leaf ⟨(26, 2057293661440), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00004.record013_result⟩)))
 (.branch 15
 (.leaf ⟨(26, 2057293726720), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00004.record014_result⟩)
 (.branch 16
 (.leaf ⟨(26, 2057301918724), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00004.record015_result⟩)
 (.leaf ⟨(26, 2057566159364), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00004.record016_result⟩))))
 (.branch 20
 (.branch 18
 (.leaf ⟨(26, 2057566289921), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00004.record017_result⟩)
 (.branch 19
 (.leaf ⟨(26, 2057566355456), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00004.record018_result⟩)
 (.leaf ⟨(26, 2057838789632), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00004.record019_result⟩)))
 (.branch 21
 (.leaf ⟨(26, 2058107224064), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00004.record020_result⟩)
 (.branch 22
 (.leaf ⟨(26, 2067567509760), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00004.record021_result⟩)
 (.leaf ⟨(26, 2109512679424), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00004.record022_result⟩))))))
 (.branch 35
 (.branch 29
 (.branch 26
 (.branch 24
 (.leaf ⟨(26, 2113805486208), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00004.record023_result⟩)
 (.branch 25
 (.leaf ⟨(26, 2118226313472), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00004.record024_result⟩)
 (.leaf ⟨(26, 2126147289344), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00004.record025_result⟩)))
 (.branch 27
 (.leaf ⟨(26, 2126684160000), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00004.record026_result⟩)
 (.branch 28
 (.leaf ⟨(26, 2126692483072), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00004.record027_result⟩)
 (.leaf ⟨(26, 2126816280576), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00004.record028_result⟩))))
 (.branch 32
 (.branch 30
 (.leaf ⟨(26, 2126956724224), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00004.record029_result⟩)
 (.branch 31
 (.leaf ⟨(26, 2130398248968), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00004.record030_result⟩)
 (.leaf ⟨(26, 2130860670984), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00004.record031_result⟩)))
 (.branch 33
 (.leaf ⟨(26, 2132589873408), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00004.record032_result⟩)
 (.branch 34
 (.leaf ⟨(26, 2132594098184), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00004.record033_result⟩)
 (.leaf ⟨(26, 2134670248192), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00004.record034_result⟩)))))
 (.branch 41
 (.branch 38
 (.branch 36
 (.leaf ⟨(26, 2147553083400), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00004.record035_result⟩)
 (.branch 37
 (.leaf ⟨(26, 2150314803201), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00004.record036_result⟩)
 (.leaf ⟨(26, 2150438568192), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00004.record037_result⟩)))
 (.branch 39
 (.leaf ⟨(26, 2150449037312), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00004.record038_result⟩)
 (.branch 40
 (.leaf ⟨(26, 2313253126400), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00004.record039_result⟩)
 (.leaf ⟨(26, 2315601936512), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00004.record040_result⟩))))
 (.branch 44
 (.branch 42
 (.leaf ⟨(26, 2316403015936), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00004.record041_result⟩)
 (.branch 43
 (.leaf ⟨(26, 2384992436480), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00004.record042_result⟩)
 (.leaf ⟨(26, 2415049933056), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00004.record043_result⟩)))
 (.branch 45
 (.leaf ⟨(26, 2420321091840), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00004.record044_result⟩)
 (.branch 46
 (.leaf ⟨(26, 2420325253376), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00004.record045_result⟩)
 (.leaf ⟨(26, 2420325318656), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00004.record046_result⟩)))))))
 (.branch 71
 (.branch 59
 (.branch 53
 (.branch 50
 (.branch 48
 (.leaf ⟨(26, 2420387152128), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00004.record047_result⟩)
 (.branch 49
 (.leaf ⟨(26, 2420391313664), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00004.record048_result⟩)
 (.leaf ⟨(26, 2420391378944), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00004.record049_result⟩)))
 (.branch 51
 (.leaf ⟨(26, 2420424409088), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00004.record050_result⟩)
 (.branch 52
 (.leaf ⟨(26, 2441846292736), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00004.record051_result⟩)
 (.leaf ⟨(26, 2443992727808), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00004.record052_result⟩))))
 (.branch 56
 (.branch 54
 (.leaf ⟨(26, 2444124848384), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00004.record053_result⟩)
 (.branch 55
 (.leaf ⟨(26, 2446667579648), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00004.record054_result⟩)
 (.leaf ⟨(26, 2446667644928), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00004.record055_result⟩)))
 (.branch 57
 (.leaf ⟨(26, 2453040889856), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00004.record056_result⟩)
 (.branch 58
 (.leaf ⟨(26, 2454716645376), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00004.record057_result⟩)
 (.leaf ⟨(26, 2454720611584), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00004.record058_result⟩)))))
 (.branch 65
 (.branch 62
 (.branch 60
 (.leaf ⟨(26, 2455257481217), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00004.record059_result⟩)
 (.branch 61
 (.leaf ⟨(26, 2459552465024), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00004.record060_result⟩)
 (.leaf ⟨(26, 2463438472448), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00004.record061_result⟩)))
 (.branch 63
 (.leaf ⟨(26, 2469679596800), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00004.record062_result⟩)
 (.branch 64
 (.leaf ⟨(26, 2469811781888), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00004.record063_result⟩)
 (.leaf ⟨(26, 2469820170240), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00004.record064_result⟩))))
 (.branch 68
 (.branch 66
 (.leaf ⟨(26, 2470018351104), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00004.record065_result⟩)
 (.branch 67
 (.leaf ⟨(26, 2470212305152), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00004.record066_result⟩)
 (.leaf ⟨(26, 2470220693504), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00004.record067_result⟩)))
 (.branch 69
 (.leaf ⟨(26, 2513971495168), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00004.record068_result⟩)
 (.branch 70
 (.leaf ⟨(26, 2522695663616), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00004.record069_result⟩)
 (.leaf ⟨(26, 2546183749888), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00004.record070_result⟩))))))
 (.branch 83
 (.branch 77
 (.branch 74
 (.branch 72
 (.leaf ⟨(26, 2548330184960), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00004.record071_result⟩)
 (.branch 73
 (.leaf ⟨(26, 2552490934528), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00004.record072_result⟩)
 (.leaf ⟨(26, 2579419414784), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00004.record073_result⟩)))
 (.branch 75
 (.leaf ⟨(26, 2581565849856), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00004.record074_result⟩)
 (.branch 76
 (.leaf ⟨(26, 2583838097664), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00004.record075_result⟩)
 (.leaf ⟨(26, 2584240734336), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00004.record076_result⟩))))
 (.branch 80
 (.branch 78
 (.leaf ⟨(26, 2588131033088), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00004.record077_result⟩)
 (.branch 79
 (.leaf ⟨(26, 2588401483904), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00004.record078_result⟩)
 (.leaf ⟨(26, 2590277468160), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00004.record079_result⟩)))
 (.branch 81
 (.leaf ⟨(26, 2590481858688), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00004.record080_result⟩)
 (.branch 82
 (.leaf ⟨(26, 2601017966592), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00004.record081_result⟩)
 (.leaf ⟨(26, 2601410134144), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00004.record082_result⟩)))))
 (.branch 89
 (.branch 86
 (.branch 84
 (.leaf ⟨(26, 2601546448896), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00004.record083_result⟩)
 (.branch 85
 (.leaf ⟨(26, 2605302448384), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00004.record084_result⟩)
 (.leaf ⟨(26, 2605306675200), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00004.record085_result⟩)))
 (.branch 87
 (.leaf ⟨(26, 2605310836736), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00004.record086_result⟩)
 (.branch 88
 (.leaf ⟨(26, 2605570883712), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00004.record087_result⟩)
 (.leaf ⟨(26, 2605839319040), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00004.record088_result⟩))))
 (.branch 92
 (.branch 90
 (.leaf ⟨(26, 2605843480576), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00004.record089_result⟩)
 (.branch 91
 (.leaf ⟨(26, 2607250702592), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00004.record090_result⟩)
 (.leaf ⟨(26, 2607259090944), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00004.record091_result⟩)))
 (.branch 93
 (.leaf ⟨(26, 2607382823168), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00004.record092_result⟩)
 (.branch 94
 (.leaf ⟨(26, 2607387049984), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00004.record093_result⟩)
 (.leaf ⟨(26, 2607391211520), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00004.record094_result⟩))))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (14206 + i))) 0 95 :=
  interval_of_check _ 0 95 (by decide +kernel)

public theorem complete : Block 14206 14301 :=
  block_of_table results 14206 95 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0320
