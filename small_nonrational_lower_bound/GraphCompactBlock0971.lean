module
prelude
import GraphInputsSix0Part00006Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0971
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 50
 (.branch 25
 (.branch 12
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(32, 2415049933056), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00006.record000_result⟩)
 (.branch 2
 (.leaf ⟨(32, 2418478752000), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00006.record001_result⟩)
 (.leaf ⟨(32, 2418680086656), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00006.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(32, 2420321091840), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00006.record003_result⟩)
 (.branch 5
 (.leaf ⟨(32, 2420325253376), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00006.record004_result⟩)
 (.leaf ⟨(32, 2420325318656), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00006.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(32, 2420387152128), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00006.record006_result⟩)
 (.branch 8
 (.leaf ⟨(32, 2420391313664), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00006.record007_result⟩)
 (.leaf ⟨(32, 2420391378944), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00006.record008_result⟩)))
 (.branch 10
 (.leaf ⟨(32, 2420424343808), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00006.record009_result⟩)
 (.branch 11
 (.leaf ⟨(32, 2420424409088), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00006.record010_result⟩)
 (.leaf ⟨(32, 2420625711104), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00006.record011_result⟩)))))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf ⟨(32, 2423641915648), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00006.record012_result⟩)
 (.branch 14
 (.leaf ⟨(32, 2441846292736), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00006.record013_result⟩)
 (.leaf ⟨(32, 2442248896768), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00006.record014_result⟩)))
 (.branch 16
 (.leaf ⟨(32, 2443992727808), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00006.record015_result⟩)
 (.branch 17
 (.leaf ⟨(32, 2444124848384), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00006.record016_result⟩)
 (.leaf ⟨(32, 2444131090688), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00006.record017_result⟩))))
 (.branch 21
 (.branch 19
 (.leaf ⟨(32, 2444395331840), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00006.record018_result⟩)
 (.branch 20
 (.leaf ⟨(32, 2446399176960), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00006.record019_result⟩)
 (.leaf ⟨(32, 2446667579648), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00006.record020_result⟩)))
 (.branch 23
 (.branch 22
 (.leaf ⟨(32, 2446667644928), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00006.record021_result⟩)
 (.leaf ⟨(32, 2450960449792), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00006.record022_result⟩))
 (.branch 24
 (.leaf ⟨(32, 2452838482176), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00006.record023_result⟩)
 (.leaf ⟨(32, 2453040824576), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00006.record024_result⟩))))))
 (.branch 37
 (.branch 31
 (.branch 28
 (.branch 26
 (.leaf ⟨(32, 2453040889856), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00006.record025_result⟩)
 (.branch 27
 (.leaf ⟨(32, 2454712418560), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00006.record026_result⟩)
 (.leaf ⟨(32, 2454716580096), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00006.record027_result⟩)))
 (.branch 29
 (.leaf ⟨(32, 2454716645376), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00006.record028_result⟩)
 (.branch 30
 (.leaf ⟨(32, 2454720611584), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00006.record029_result⟩)
 (.leaf ⟨(32, 2455116973312), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00006.record030_result⟩))))
 (.branch 34
 (.branch 32
 (.leaf ⟨(32, 2455119249408), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00006.record031_result⟩)
 (.branch 33
 (.leaf ⟨(32, 2455257481217), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00006.record032_result⟩)
 (.leaf ⟨(32, 2459550384256), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00006.record033_result⟩)))
 (.branch 35
 (.leaf ⟨(32, 2459552465024), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00006.record034_result⟩)
 (.branch 36
 (.leaf ⟨(32, 2463438472448), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00006.record035_result⟩)
 (.leaf ⟨(32, 2469679596800), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00006.record036_result⟩)))))
 (.branch 43
 (.branch 40
 (.branch 38
 (.leaf ⟨(32, 2469811781888), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00006.record037_result⟩)
 (.branch 39
 (.leaf ⟨(32, 2469820170240), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00006.record038_result⟩)
 (.leaf ⟨(32, 2470018351104), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00006.record039_result⟩)))
 (.branch 41
 (.leaf ⟨(32, 2470212305152), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00006.record040_result⟩)
 (.branch 42
 (.leaf ⟨(32, 2470220693504), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00006.record041_result⟩)
 (.leaf ⟨(32, 2492765094080), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00006.record042_result⟩))))
 (.branch 46
 (.branch 44
 (.leaf ⟨(32, 2511891120384), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00006.record043_result⟩)
 (.branch 45
 (.leaf ⟨(32, 2513971495168), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00006.record044_result⟩)
 (.leaf ⟨(32, 2521554845952), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00006.record045_result⟩)))
 (.branch 48
 (.branch 47
 (.leaf ⟨(32, 2522695663616), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00006.record046_result⟩)
 (.leaf ⟨(32, 2546183749888), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00006.record047_result⟩))
 (.branch 49
 (.leaf ⟨(32, 2548330184960), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00006.record048_result⟩)
 (.leaf ⟨(32, 2552490934528), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00006.record049_result⟩)))))))
 (.branch 75
 (.branch 62
 (.branch 56
 (.branch 53
 (.branch 51
 (.leaf ⟨(32, 2579419414784), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00006.record050_result⟩)
 (.branch 52
 (.leaf ⟨(32, 2581565849856), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00006.record051_result⟩)
 (.leaf ⟨(32, 2583838097664), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00006.record052_result⟩)))
 (.branch 54
 (.leaf ⟨(32, 2583838162944), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00006.record053_result⟩)
 (.branch 55
 (.leaf ⟨(32, 2584106532992), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00006.record054_result⟩)
 (.leaf ⟨(32, 2584240734336), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00006.record055_result⟩))))
 (.branch 59
 (.branch 57
 (.leaf ⟨(32, 2585858720000), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00006.record056_result⟩)
 (.branch 58
 (.leaf ⟨(32, 2588126806272), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00006.record057_result⟩)
 (.leaf ⟨(32, 2588130967808), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00006.record058_result⟩)))
 (.branch 60
 (.leaf ⟨(32, 2588131033088), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00006.record059_result⟩)
 (.branch 61
 (.leaf ⟨(32, 2588399403136), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00006.record060_result⟩)
 (.leaf ⟨(32, 2588401483904), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00006.record061_result⟩)))))
 (.branch 68
 (.branch 65
 (.branch 63
 (.leaf ⟨(32, 2590277402880), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00006.record062_result⟩)
 (.branch 64
 (.leaf ⟨(32, 2590277468160), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00006.record063_result⟩)
 (.leaf ⟨(32, 2590479777920), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00006.record064_result⟩)))
 (.branch 66
 (.leaf ⟨(32, 2590481858688), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00006.record065_result⟩)
 (.branch 67
 (.leaf ⟨(32, 2601009578240), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00006.record066_result⟩)
 (.leaf ⟨(32, 2601017966592), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00006.record067_result⟩))))
 (.branch 71
 (.branch 69
 (.leaf ⟨(32, 2601278013568), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00006.record068_result⟩)
 (.branch 70
 (.leaf ⟨(32, 2601410134144), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00006.record069_result⟩)
 (.leaf ⟨(32, 2601546448896), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00006.record070_result⟩)))
 (.branch 73
 (.branch 72
 (.leaf ⟨(32, 2605302448384), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00006.record071_result⟩)
 (.leaf ⟨(32, 2605306675200), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00006.record072_result⟩))
 (.branch 74
 (.leaf ⟨(32, 2605310836736), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00006.record073_result⟩)
 (.leaf ⟨(32, 2605570883712), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00006.record074_result⟩))))))
 (.branch 87
 (.branch 81
 (.branch 78
 (.branch 76
 (.leaf ⟨(32, 2605839319040), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00006.record075_result⟩)
 (.branch 77
 (.leaf ⟨(32, 2605843480576), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00006.record076_result⟩)
 (.leaf ⟨(32, 2607250702592), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00006.record077_result⟩)))
 (.branch 79
 (.leaf ⟨(32, 2607259090944), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00006.record078_result⟩)
 (.branch 80
 (.leaf ⟨(32, 2607382823168), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00006.record079_result⟩)
 (.leaf ⟨(32, 2607387049984), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00006.record080_result⟩))))
 (.branch 84
 (.branch 82
 (.leaf ⟨(32, 2607391211520), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00006.record081_result⟩)
 (.branch 83
 (.leaf ⟨(32, 2607457271808), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00006.record082_result⟩)
 (.leaf ⟨(32, 2607651258496), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00006.record083_result⟩)))
 (.branch 85
 (.leaf ⟨(32, 2607851520128), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00006.record084_result⟩)
 (.branch 86
 (.leaf ⟨(32, 2652555477248), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00006.record085_result⟩)
 (.leaf ⟨(32, 2652823912576), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00006.record086_result⟩)))))
 (.branch 93
 (.branch 90
 (.branch 88
 (.leaf ⟨(32, 2675976470528), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00006.record087_result⟩)
 (.branch 89
 (.leaf ⟨(32, 2682297303296), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00006.record088_result⟩)
 (.leaf ⟨(32, 2682363363584), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00006.record089_result⟩)))
 (.branch 91
 (.leaf ⟨(32, 2686715986176), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00006.record090_result⟩)
 (.branch 92
 (.leaf ⟨(32, 2686716051456), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00006.record091_result⟩)
 (.leaf ⟨(32, 2686843945216), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00006.record092_result⟩))))
 (.branch 96
 (.branch 94
 (.leaf ⟨(32, 2686848106752), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00006.record093_result⟩)
 (.branch 95
 (.leaf ⟨(32, 2686848172032), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00006.record094_result⟩)
 (.leaf ⟨(32, 2686914167040), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00006.record095_result⟩)))
 (.branch 98
 (.branch 97
 (.leaf ⟨(32, 2686914232320), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00006.record096_result⟩)
 (.leaf ⟨(32, 2687116542080), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00006.record097_result⟩))
 (.branch 99
 (.leaf ⟨(32, 2687118622848), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00006.record098_result⟩)
 (.leaf ⟨(32, 2693356658688), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00006.record099_result⟩))))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (27386 + i))) 0 100 :=
  interval_of_check _ 0 100 (by decide +kernel)

public theorem complete : Block 27386 27486 :=
  block_of_table results 27386 100 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0971
