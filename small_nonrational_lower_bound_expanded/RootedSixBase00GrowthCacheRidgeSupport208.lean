module
prelude
public meta import LowerSchemas.FiniteRootedSixBase.Part0
public import BundledChecks.RootedSixBase00GrowthCacheRidgeSupport208Batch000
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
cert_ridgeSupport_suffix_decode 208 048 15
cert_ridgeSupport_suffix_decode_2 208 047 15 10 10 048 048 0
cert_ridgeSupport_suffix_decode_2 208 046 15 42 32 048 047 10
cert_ridgeSupport_suffix_decode_2 208 045 15 74 32 048 046 42
cert_ridgeSupport_suffix_decode_2 208 044 15 106 32 048 045 74
cert_ridgeSupport_suffix_decode_2 208 043 15 138 32 048 044 106
cert_ridgeSupport_suffix_decode_2 208 042 15 170 32 048 043 138
cert_ridgeSupport_suffix_decode_2 208 041 15 202 32 048 042 170
cert_ridgeSupport_suffix_decode_2 208 040 15 234 32 048 041 202
cert_ridgeSupport_suffix_decode_2 208 039 15 266 32 048 040 234
cert_ridgeSupport_suffix_decode_2 208 038 15 298 32 048 039 266
cert_ridgeSupport_suffix_decode_2 208 037 15 330 32 048 038 298
cert_ridgeSupport_suffix_decode_2 208 036 15 362 32 048 037 330
cert_ridgeSupport_suffix_decode_2 208 035 15 394 32 048 036 362
cert_ridgeSupport_suffix_decode_2 208 034 15 426 32 048 035 394
cert_ridgeSupport_suffix_decode_2 208 033 15 458 32 048 034 426
cert_ridgeSupport_suffix_decode_2 208 032 15 490 32 048 033 458
cert_ridgeSupport_suffix_decode_2 208 031 15 522 32 048 032 490
cert_ridgeSupport_suffix_decode_2 208 030 15 554 32 048 031 522
cert_ridgeSupport_suffix_decode_2 208 029 15 586 32 048 030 554
cert_ridgeSupport_suffix_decode_2 208 028 15 618 32 048 029 586
cert_ridgeSupport_suffix_decode_2 208 027 15 650 32 048 028 618
cert_ridgeSupport_suffix_decode_2 208 026 15 682 32 048 027 650
cert_ridgeSupport_suffix_decode_2 208 025 15 714 32 048 026 682
cert_ridgeSupport_suffix_decode_2 208 024 15 746 32 048 025 714
cert_ridgeSupport_suffix_decode_2 208 023 15 778 32 048 024 746
cert_ridgeSupport_suffix_decode_2 208 022 15 810 32 048 023 778
cert_ridgeSupport_suffix_decode_2 208 021 15 842 32 048 022 810
cert_ridgeSupport_suffix_decode_2 208 020 15 874 32 048 021 842
cert_ridgeSupport_suffix_decode_2 208 019 15 906 32 048 020 874
cert_ridgeSupport_suffix_decode_2 208 018 15 938 32 048 019 906
cert_ridgeSupport_suffix_decode_2 208 017 15 970 32 048 018 938
cert_ridgeSupport_suffix_decode_2 208 016 15 1002 32 048 017 970
cert_ridgeSupport_suffix_decode_2 208 015 15 1034 32 048 016 1002
cert_ridgeSupport_suffix_decode_2 208 014 15 1066 32 048 015 1034
cert_ridgeSupport_suffix_decode_2 208 013 15 1098 32 048 014 1066
cert_ridgeSupport_suffix_decode_2 208 012 15 1130 32 048 013 1098
cert_ridgeSupport_suffix_decode_2 208 011 15 1162 32 048 012 1130
cert_ridgeSupport_suffix_decode_2 208 010 15 1194 32 048 011 1162
cert_ridgeSupport_suffix_decode_2 208 009 15 1226 32 048 010 1194
cert_ridgeSupport_suffix_decode_2 208 008 15 1258 32 048 009 1226
cert_ridgeSupport_suffix_decode_2 208 007 15 1290 32 048 008 1258
cert_ridgeSupport_suffix_decode_2 208 006 15 1322 32 048 007 1290
cert_ridgeSupport_suffix_decode_2 208 005 15 1354 32 048 006 1322
cert_ridgeSupport_suffix_decode_2 208 004 15 1386 32 048 005 1354
cert_ridgeSupport_suffix_decode_2 208 003 15 1418 32 048 004 1386
cert_ridgeSupport_suffix_decode_2 208 002 15 1450 32 048 003 1418
cert_ridgeSupport_suffix_decode_2 208 001 15 1482 32 048 002 1450
cert_ridgeSupport_suffix_decode_2 208 000 15 1514 32 048 001 1482
cert_ridgeSupport_eq_3 208
theorem ridgeTest_large_208 : ridgeTest 208 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport208_eq]
    simp only [ridgeSupport208_suffix_000, ridgeSupport208_suffix_001, ridgeSupport208_suffix_002, ridgeSupport208_suffix_003, ridgeSupport208_suffix_004, ridgeSupport208_suffix_005, ridgeSupport208_suffix_006, ridgeSupport208_suffix_007, ridgeSupport208_suffix_008, ridgeSupport208_suffix_009, ridgeSupport208_suffix_010, ridgeSupport208_suffix_011, ridgeSupport208_suffix_012, ridgeSupport208_suffix_013, ridgeSupport208_suffix_014, ridgeSupport208_suffix_015, ridgeSupport208_suffix_016, ridgeSupport208_suffix_017, ridgeSupport208_suffix_018, ridgeSupport208_suffix_019, ridgeSupport208_suffix_020, ridgeSupport208_suffix_021, ridgeSupport208_suffix_022, ridgeSupport208_suffix_023, ridgeSupport208_suffix_024, ridgeSupport208_suffix_025, ridgeSupport208_suffix_026, ridgeSupport208_suffix_027, ridgeSupport208_suffix_028, ridgeSupport208_suffix_029, ridgeSupport208_suffix_030, ridgeSupport208_suffix_031, ridgeSupport208_suffix_032, ridgeSupport208_suffix_033, ridgeSupport208_suffix_034, ridgeSupport208_suffix_035, ridgeSupport208_suffix_036, ridgeSupport208_suffix_037, ridgeSupport208_suffix_038, ridgeSupport208_suffix_039, ridgeSupport208_suffix_040, ridgeSupport208_suffix_041, ridgeSupport208_suffix_042, ridgeSupport208_suffix_043, ridgeSupport208_suffix_044, ridgeSupport208_suffix_045, ridgeSupport208_suffix_046, ridgeSupport208_suffix_047, ridgeSupport208_suffix_048, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport208_000_mask, ridgeSupport208_001_mask, ridgeSupport208_002_mask, ridgeSupport208_003_mask, ridgeSupport208_004_mask, ridgeSupport208_005_mask, ridgeSupport208_006_mask, ridgeSupport208_007_mask, ridgeSupport208_008_mask, ridgeSupport208_009_mask, ridgeSupport208_010_mask, ridgeSupport208_011_mask, ridgeSupport208_012_mask, ridgeSupport208_013_mask, ridgeSupport208_014_mask, ridgeSupport208_015_mask, ridgeSupport208_016_mask, ridgeSupport208_017_mask, ridgeSupport208_018_mask, ridgeSupport208_019_mask, ridgeSupport208_020_mask, ridgeSupport208_021_mask, ridgeSupport208_022_mask, ridgeSupport208_023_mask, ridgeSupport208_024_mask, ridgeSupport208_025_mask, ridgeSupport208_026_mask, ridgeSupport208_027_mask, ridgeSupport208_028_mask, ridgeSupport208_029_mask, ridgeSupport208_030_mask, ridgeSupport208_031_mask, ridgeSupport208_032_mask, ridgeSupport208_033_mask, ridgeSupport208_034_mask, ridgeSupport208_035_mask, ridgeSupport208_036_mask, ridgeSupport208_037_mask, ridgeSupport208_038_mask, ridgeSupport208_039_mask, ridgeSupport208_040_mask, ridgeSupport208_041_mask, ridgeSupport208_042_mask, ridgeSupport208_043_mask, ridgeSupport208_044_mask, ridgeSupport208_045_mask, ridgeSupport208_046_mask, ridgeSupport208_047_mask]
    decide +kernel
  · rw [ridgeSupport208_eq]
    simp only [ridgeSupport208_suffix_000, ridgeSupport208_suffix_001, ridgeSupport208_suffix_002, ridgeSupport208_suffix_003, ridgeSupport208_suffix_004, ridgeSupport208_suffix_005, ridgeSupport208_suffix_006, ridgeSupport208_suffix_007, ridgeSupport208_suffix_008, ridgeSupport208_suffix_009, ridgeSupport208_suffix_010, ridgeSupport208_suffix_011, ridgeSupport208_suffix_012, ridgeSupport208_suffix_013, ridgeSupport208_suffix_014, ridgeSupport208_suffix_015, ridgeSupport208_suffix_016, ridgeSupport208_suffix_017, ridgeSupport208_suffix_018, ridgeSupport208_suffix_019, ridgeSupport208_suffix_020, ridgeSupport208_suffix_021, ridgeSupport208_suffix_022, ridgeSupport208_suffix_023, ridgeSupport208_suffix_024, ridgeSupport208_suffix_025, ridgeSupport208_suffix_026, ridgeSupport208_suffix_027, ridgeSupport208_suffix_028, ridgeSupport208_suffix_029, ridgeSupport208_suffix_030, ridgeSupport208_suffix_031, ridgeSupport208_suffix_032, ridgeSupport208_suffix_033, ridgeSupport208_suffix_034, ridgeSupport208_suffix_035, ridgeSupport208_suffix_036, ridgeSupport208_suffix_037, ridgeSupport208_suffix_038, ridgeSupport208_suffix_039, ridgeSupport208_suffix_040, ridgeSupport208_suffix_041, ridgeSupport208_suffix_042, ridgeSupport208_suffix_043, ridgeSupport208_suffix_044, ridgeSupport208_suffix_045, ridgeSupport208_suffix_046, ridgeSupport208_suffix_047, ridgeSupport208_suffix_048, List.all_append, List.all_nil, ridgeSupport208_000_checked, ridgeSupport208_001_checked, ridgeSupport208_002_checked, ridgeSupport208_003_checked, ridgeSupport208_004_checked, ridgeSupport208_005_checked, ridgeSupport208_006_checked, ridgeSupport208_007_checked, ridgeSupport208_008_checked, ridgeSupport208_009_checked, ridgeSupport208_010_checked, ridgeSupport208_011_checked, ridgeSupport208_012_checked, ridgeSupport208_013_checked, ridgeSupport208_014_checked, ridgeSupport208_015_checked, ridgeSupport208_016_checked, ridgeSupport208_017_checked, ridgeSupport208_018_checked, ridgeSupport208_019_checked, ridgeSupport208_020_checked, ridgeSupport208_021_checked, ridgeSupport208_022_checked, ridgeSupport208_023_checked, ridgeSupport208_024_checked, ridgeSupport208_025_checked, ridgeSupport208_026_checked, ridgeSupport208_027_checked, ridgeSupport208_028_checked, ridgeSupport208_029_checked, ridgeSupport208_030_checked, ridgeSupport208_031_checked, ridgeSupport208_032_checked, ridgeSupport208_033_checked, ridgeSupport208_034_checked, ridgeSupport208_035_checked, ridgeSupport208_036_checked, ridgeSupport208_037_checked, ridgeSupport208_038_checked, ridgeSupport208_039_checked, ridgeSupport208_040_checked, ridgeSupport208_041_checked, ridgeSupport208_042_checked, ridgeSupport208_043_checked, ridgeSupport208_044_checked, ridgeSupport208_045_checked, ridgeSupport208_046_checked, ridgeSupport208_047_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase00
