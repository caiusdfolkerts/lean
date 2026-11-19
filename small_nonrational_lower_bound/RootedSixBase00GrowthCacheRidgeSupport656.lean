module
prelude
public meta import LowerSchemas.FiniteRootedSixBase
public import BundledChecks.RootedSixBase00GrowthCacheRidgeSupport656Batch000
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
cert_ridgeSupport_suffix_decode 656 048 15
cert_ridgeSupport_suffix_decode_2 656 047 15 10 10 048 048 0
cert_ridgeSupport_suffix_decode_2 656 046 15 42 32 048 047 10
cert_ridgeSupport_suffix_decode_2 656 045 15 74 32 048 046 42
cert_ridgeSupport_suffix_decode_2 656 044 15 106 32 048 045 74
cert_ridgeSupport_suffix_decode_2 656 043 15 138 32 048 044 106
cert_ridgeSupport_suffix_decode_2 656 042 15 170 32 048 043 138
cert_ridgeSupport_suffix_decode_2 656 041 15 202 32 048 042 170
cert_ridgeSupport_suffix_decode_2 656 040 15 234 32 048 041 202
cert_ridgeSupport_suffix_decode_2 656 039 15 266 32 048 040 234
cert_ridgeSupport_suffix_decode_2 656 038 15 298 32 048 039 266
cert_ridgeSupport_suffix_decode_2 656 037 15 330 32 048 038 298
cert_ridgeSupport_suffix_decode_2 656 036 15 362 32 048 037 330
cert_ridgeSupport_suffix_decode_2 656 035 15 394 32 048 036 362
cert_ridgeSupport_suffix_decode_2 656 034 15 426 32 048 035 394
cert_ridgeSupport_suffix_decode_2 656 033 15 458 32 048 034 426
cert_ridgeSupport_suffix_decode_2 656 032 15 490 32 048 033 458
cert_ridgeSupport_suffix_decode_2 656 031 15 522 32 048 032 490
cert_ridgeSupport_suffix_decode_2 656 030 15 554 32 048 031 522
cert_ridgeSupport_suffix_decode_2 656 029 15 586 32 048 030 554
cert_ridgeSupport_suffix_decode_2 656 028 15 618 32 048 029 586
cert_ridgeSupport_suffix_decode_2 656 027 15 650 32 048 028 618
cert_ridgeSupport_suffix_decode_2 656 026 15 682 32 048 027 650
cert_ridgeSupport_suffix_decode_2 656 025 15 714 32 048 026 682
cert_ridgeSupport_suffix_decode_2 656 024 15 746 32 048 025 714
cert_ridgeSupport_suffix_decode_2 656 023 15 778 32 048 024 746
cert_ridgeSupport_suffix_decode_2 656 022 15 810 32 048 023 778
cert_ridgeSupport_suffix_decode_2 656 021 15 842 32 048 022 810
cert_ridgeSupport_suffix_decode_2 656 020 15 874 32 048 021 842
cert_ridgeSupport_suffix_decode_2 656 019 15 906 32 048 020 874
cert_ridgeSupport_suffix_decode_2 656 018 15 938 32 048 019 906
cert_ridgeSupport_suffix_decode_2 656 017 15 970 32 048 018 938
cert_ridgeSupport_suffix_decode_2 656 016 15 1002 32 048 017 970
cert_ridgeSupport_suffix_decode_2 656 015 15 1034 32 048 016 1002
cert_ridgeSupport_suffix_decode_2 656 014 15 1066 32 048 015 1034
cert_ridgeSupport_suffix_decode_2 656 013 15 1098 32 048 014 1066
cert_ridgeSupport_suffix_decode_2 656 012 15 1130 32 048 013 1098
cert_ridgeSupport_suffix_decode_2 656 011 15 1162 32 048 012 1130
cert_ridgeSupport_suffix_decode_2 656 010 15 1194 32 048 011 1162
cert_ridgeSupport_suffix_decode_2 656 009 15 1226 32 048 010 1194
cert_ridgeSupport_suffix_decode_2 656 008 15 1258 32 048 009 1226
cert_ridgeSupport_suffix_decode_2 656 007 15 1290 32 048 008 1258
cert_ridgeSupport_suffix_decode_2 656 006 15 1322 32 048 007 1290
cert_ridgeSupport_suffix_decode_2 656 005 15 1354 32 048 006 1322
cert_ridgeSupport_suffix_decode_2 656 004 15 1386 32 048 005 1354
cert_ridgeSupport_suffix_decode_2 656 003 15 1418 32 048 004 1386
cert_ridgeSupport_suffix_decode_2 656 002 15 1450 32 048 003 1418
cert_ridgeSupport_suffix_decode_2 656 001 15 1482 32 048 002 1450
cert_ridgeSupport_suffix_decode_2 656 000 15 1514 32 048 001 1482
cert_ridgeSupport_eq_3 656
theorem ridgeTest_large_656 : ridgeTest 656 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport656_eq]
    simp only [ridgeSupport656_suffix_000, ridgeSupport656_suffix_001, ridgeSupport656_suffix_002, ridgeSupport656_suffix_003, ridgeSupport656_suffix_004, ridgeSupport656_suffix_005, ridgeSupport656_suffix_006, ridgeSupport656_suffix_007, ridgeSupport656_suffix_008, ridgeSupport656_suffix_009, ridgeSupport656_suffix_010, ridgeSupport656_suffix_011, ridgeSupport656_suffix_012, ridgeSupport656_suffix_013, ridgeSupport656_suffix_014, ridgeSupport656_suffix_015, ridgeSupport656_suffix_016, ridgeSupport656_suffix_017, ridgeSupport656_suffix_018, ridgeSupport656_suffix_019, ridgeSupport656_suffix_020, ridgeSupport656_suffix_021, ridgeSupport656_suffix_022, ridgeSupport656_suffix_023, ridgeSupport656_suffix_024, ridgeSupport656_suffix_025, ridgeSupport656_suffix_026, ridgeSupport656_suffix_027, ridgeSupport656_suffix_028, ridgeSupport656_suffix_029, ridgeSupport656_suffix_030, ridgeSupport656_suffix_031, ridgeSupport656_suffix_032, ridgeSupport656_suffix_033, ridgeSupport656_suffix_034, ridgeSupport656_suffix_035, ridgeSupport656_suffix_036, ridgeSupport656_suffix_037, ridgeSupport656_suffix_038, ridgeSupport656_suffix_039, ridgeSupport656_suffix_040, ridgeSupport656_suffix_041, ridgeSupport656_suffix_042, ridgeSupport656_suffix_043, ridgeSupport656_suffix_044, ridgeSupport656_suffix_045, ridgeSupport656_suffix_046, ridgeSupport656_suffix_047, ridgeSupport656_suffix_048, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport656_000_mask, ridgeSupport656_001_mask, ridgeSupport656_002_mask, ridgeSupport656_003_mask, ridgeSupport656_004_mask, ridgeSupport656_005_mask, ridgeSupport656_006_mask, ridgeSupport656_007_mask, ridgeSupport656_008_mask, ridgeSupport656_009_mask, ridgeSupport656_010_mask, ridgeSupport656_011_mask, ridgeSupport656_012_mask, ridgeSupport656_013_mask, ridgeSupport656_014_mask, ridgeSupport656_015_mask, ridgeSupport656_016_mask, ridgeSupport656_017_mask, ridgeSupport656_018_mask, ridgeSupport656_019_mask, ridgeSupport656_020_mask, ridgeSupport656_021_mask, ridgeSupport656_022_mask, ridgeSupport656_023_mask, ridgeSupport656_024_mask, ridgeSupport656_025_mask, ridgeSupport656_026_mask, ridgeSupport656_027_mask, ridgeSupport656_028_mask, ridgeSupport656_029_mask, ridgeSupport656_030_mask, ridgeSupport656_031_mask, ridgeSupport656_032_mask, ridgeSupport656_033_mask, ridgeSupport656_034_mask, ridgeSupport656_035_mask, ridgeSupport656_036_mask, ridgeSupport656_037_mask, ridgeSupport656_038_mask, ridgeSupport656_039_mask, ridgeSupport656_040_mask, ridgeSupport656_041_mask, ridgeSupport656_042_mask, ridgeSupport656_043_mask, ridgeSupport656_044_mask, ridgeSupport656_045_mask, ridgeSupport656_046_mask, ridgeSupport656_047_mask]
    decide +kernel
  · rw [ridgeSupport656_eq]
    simp only [ridgeSupport656_suffix_000, ridgeSupport656_suffix_001, ridgeSupport656_suffix_002, ridgeSupport656_suffix_003, ridgeSupport656_suffix_004, ridgeSupport656_suffix_005, ridgeSupport656_suffix_006, ridgeSupport656_suffix_007, ridgeSupport656_suffix_008, ridgeSupport656_suffix_009, ridgeSupport656_suffix_010, ridgeSupport656_suffix_011, ridgeSupport656_suffix_012, ridgeSupport656_suffix_013, ridgeSupport656_suffix_014, ridgeSupport656_suffix_015, ridgeSupport656_suffix_016, ridgeSupport656_suffix_017, ridgeSupport656_suffix_018, ridgeSupport656_suffix_019, ridgeSupport656_suffix_020, ridgeSupport656_suffix_021, ridgeSupport656_suffix_022, ridgeSupport656_suffix_023, ridgeSupport656_suffix_024, ridgeSupport656_suffix_025, ridgeSupport656_suffix_026, ridgeSupport656_suffix_027, ridgeSupport656_suffix_028, ridgeSupport656_suffix_029, ridgeSupport656_suffix_030, ridgeSupport656_suffix_031, ridgeSupport656_suffix_032, ridgeSupport656_suffix_033, ridgeSupport656_suffix_034, ridgeSupport656_suffix_035, ridgeSupport656_suffix_036, ridgeSupport656_suffix_037, ridgeSupport656_suffix_038, ridgeSupport656_suffix_039, ridgeSupport656_suffix_040, ridgeSupport656_suffix_041, ridgeSupport656_suffix_042, ridgeSupport656_suffix_043, ridgeSupport656_suffix_044, ridgeSupport656_suffix_045, ridgeSupport656_suffix_046, ridgeSupport656_suffix_047, ridgeSupport656_suffix_048, List.all_append, List.all_nil, ridgeSupport656_000_checked, ridgeSupport656_001_checked, ridgeSupport656_002_checked, ridgeSupport656_003_checked, ridgeSupport656_004_checked, ridgeSupport656_005_checked, ridgeSupport656_006_checked, ridgeSupport656_007_checked, ridgeSupport656_008_checked, ridgeSupport656_009_checked, ridgeSupport656_010_checked, ridgeSupport656_011_checked, ridgeSupport656_012_checked, ridgeSupport656_013_checked, ridgeSupport656_014_checked, ridgeSupport656_015_checked, ridgeSupport656_016_checked, ridgeSupport656_017_checked, ridgeSupport656_018_checked, ridgeSupport656_019_checked, ridgeSupport656_020_checked, ridgeSupport656_021_checked, ridgeSupport656_022_checked, ridgeSupport656_023_checked, ridgeSupport656_024_checked, ridgeSupport656_025_checked, ridgeSupport656_026_checked, ridgeSupport656_027_checked, ridgeSupport656_028_checked, ridgeSupport656_029_checked, ridgeSupport656_030_checked, ridgeSupport656_031_checked, ridgeSupport656_032_checked, ridgeSupport656_033_checked, ridgeSupport656_034_checked, ridgeSupport656_035_checked, ridgeSupport656_036_checked, ridgeSupport656_037_checked, ridgeSupport656_038_checked, ridgeSupport656_039_checked, ridgeSupport656_040_checked, ridgeSupport656_041_checked, ridgeSupport656_042_checked, ridgeSupport656_043_checked, ridgeSupport656_044_checked, ridgeSupport656_045_checked, ridgeSupport656_046_checked, ridgeSupport656_047_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase00
