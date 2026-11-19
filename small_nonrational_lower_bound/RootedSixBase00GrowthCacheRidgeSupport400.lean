module
prelude
public meta import LowerSchemas.FiniteRootedSixBase
public import BundledChecks.RootedSixBase00GrowthCacheRidgeSupport400Batch000
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
cert_ridgeSupport_suffix_decode 400 048 15
cert_ridgeSupport_suffix_decode_2 400 047 15 10 10 048 048 0
cert_ridgeSupport_suffix_decode_2 400 046 15 42 32 048 047 10
cert_ridgeSupport_suffix_decode_2 400 045 15 74 32 048 046 42
cert_ridgeSupport_suffix_decode_2 400 044 15 106 32 048 045 74
cert_ridgeSupport_suffix_decode_2 400 043 15 138 32 048 044 106
cert_ridgeSupport_suffix_decode_2 400 042 15 170 32 048 043 138
cert_ridgeSupport_suffix_decode_2 400 041 15 202 32 048 042 170
cert_ridgeSupport_suffix_decode_2 400 040 15 234 32 048 041 202
cert_ridgeSupport_suffix_decode_2 400 039 15 266 32 048 040 234
cert_ridgeSupport_suffix_decode_2 400 038 15 298 32 048 039 266
cert_ridgeSupport_suffix_decode_2 400 037 15 330 32 048 038 298
cert_ridgeSupport_suffix_decode_2 400 036 15 362 32 048 037 330
cert_ridgeSupport_suffix_decode_2 400 035 15 394 32 048 036 362
cert_ridgeSupport_suffix_decode_2 400 034 15 426 32 048 035 394
cert_ridgeSupport_suffix_decode_2 400 033 15 458 32 048 034 426
cert_ridgeSupport_suffix_decode_2 400 032 15 490 32 048 033 458
cert_ridgeSupport_suffix_decode_2 400 031 15 522 32 048 032 490
cert_ridgeSupport_suffix_decode_2 400 030 15 554 32 048 031 522
cert_ridgeSupport_suffix_decode_2 400 029 15 586 32 048 030 554
cert_ridgeSupport_suffix_decode_2 400 028 15 618 32 048 029 586
cert_ridgeSupport_suffix_decode_2 400 027 15 650 32 048 028 618
cert_ridgeSupport_suffix_decode_2 400 026 15 682 32 048 027 650
cert_ridgeSupport_suffix_decode_2 400 025 15 714 32 048 026 682
cert_ridgeSupport_suffix_decode_2 400 024 15 746 32 048 025 714
cert_ridgeSupport_suffix_decode_2 400 023 15 778 32 048 024 746
cert_ridgeSupport_suffix_decode_2 400 022 15 810 32 048 023 778
cert_ridgeSupport_suffix_decode_2 400 021 15 842 32 048 022 810
cert_ridgeSupport_suffix_decode_2 400 020 15 874 32 048 021 842
cert_ridgeSupport_suffix_decode_2 400 019 15 906 32 048 020 874
cert_ridgeSupport_suffix_decode_2 400 018 15 938 32 048 019 906
cert_ridgeSupport_suffix_decode_2 400 017 15 970 32 048 018 938
cert_ridgeSupport_suffix_decode_2 400 016 15 1002 32 048 017 970
cert_ridgeSupport_suffix_decode_2 400 015 15 1034 32 048 016 1002
cert_ridgeSupport_suffix_decode_2 400 014 15 1066 32 048 015 1034
cert_ridgeSupport_suffix_decode_2 400 013 15 1098 32 048 014 1066
cert_ridgeSupport_suffix_decode_2 400 012 15 1130 32 048 013 1098
cert_ridgeSupport_suffix_decode_2 400 011 15 1162 32 048 012 1130
cert_ridgeSupport_suffix_decode_2 400 010 15 1194 32 048 011 1162
cert_ridgeSupport_suffix_decode_2 400 009 15 1226 32 048 010 1194
cert_ridgeSupport_suffix_decode_2 400 008 15 1258 32 048 009 1226
cert_ridgeSupport_suffix_decode_2 400 007 15 1290 32 048 008 1258
cert_ridgeSupport_suffix_decode_2 400 006 15 1322 32 048 007 1290
cert_ridgeSupport_suffix_decode_2 400 005 15 1354 32 048 006 1322
cert_ridgeSupport_suffix_decode_2 400 004 15 1386 32 048 005 1354
cert_ridgeSupport_suffix_decode_2 400 003 15 1418 32 048 004 1386
cert_ridgeSupport_suffix_decode_2 400 002 15 1450 32 048 003 1418
cert_ridgeSupport_suffix_decode_2 400 001 15 1482 32 048 002 1450
cert_ridgeSupport_suffix_decode_2 400 000 15 1514 32 048 001 1482
cert_ridgeSupport_eq_3 400
theorem ridgeTest_large_400 : ridgeTest 400 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport400_eq]
    simp only [ridgeSupport400_suffix_000, ridgeSupport400_suffix_001, ridgeSupport400_suffix_002, ridgeSupport400_suffix_003, ridgeSupport400_suffix_004, ridgeSupport400_suffix_005, ridgeSupport400_suffix_006, ridgeSupport400_suffix_007, ridgeSupport400_suffix_008, ridgeSupport400_suffix_009, ridgeSupport400_suffix_010, ridgeSupport400_suffix_011, ridgeSupport400_suffix_012, ridgeSupport400_suffix_013, ridgeSupport400_suffix_014, ridgeSupport400_suffix_015, ridgeSupport400_suffix_016, ridgeSupport400_suffix_017, ridgeSupport400_suffix_018, ridgeSupport400_suffix_019, ridgeSupport400_suffix_020, ridgeSupport400_suffix_021, ridgeSupport400_suffix_022, ridgeSupport400_suffix_023, ridgeSupport400_suffix_024, ridgeSupport400_suffix_025, ridgeSupport400_suffix_026, ridgeSupport400_suffix_027, ridgeSupport400_suffix_028, ridgeSupport400_suffix_029, ridgeSupport400_suffix_030, ridgeSupport400_suffix_031, ridgeSupport400_suffix_032, ridgeSupport400_suffix_033, ridgeSupport400_suffix_034, ridgeSupport400_suffix_035, ridgeSupport400_suffix_036, ridgeSupport400_suffix_037, ridgeSupport400_suffix_038, ridgeSupport400_suffix_039, ridgeSupport400_suffix_040, ridgeSupport400_suffix_041, ridgeSupport400_suffix_042, ridgeSupport400_suffix_043, ridgeSupport400_suffix_044, ridgeSupport400_suffix_045, ridgeSupport400_suffix_046, ridgeSupport400_suffix_047, ridgeSupport400_suffix_048, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport400_000_mask, ridgeSupport400_001_mask, ridgeSupport400_002_mask, ridgeSupport400_003_mask, ridgeSupport400_004_mask, ridgeSupport400_005_mask, ridgeSupport400_006_mask, ridgeSupport400_007_mask, ridgeSupport400_008_mask, ridgeSupport400_009_mask, ridgeSupport400_010_mask, ridgeSupport400_011_mask, ridgeSupport400_012_mask, ridgeSupport400_013_mask, ridgeSupport400_014_mask, ridgeSupport400_015_mask, ridgeSupport400_016_mask, ridgeSupport400_017_mask, ridgeSupport400_018_mask, ridgeSupport400_019_mask, ridgeSupport400_020_mask, ridgeSupport400_021_mask, ridgeSupport400_022_mask, ridgeSupport400_023_mask, ridgeSupport400_024_mask, ridgeSupport400_025_mask, ridgeSupport400_026_mask, ridgeSupport400_027_mask, ridgeSupport400_028_mask, ridgeSupport400_029_mask, ridgeSupport400_030_mask, ridgeSupport400_031_mask, ridgeSupport400_032_mask, ridgeSupport400_033_mask, ridgeSupport400_034_mask, ridgeSupport400_035_mask, ridgeSupport400_036_mask, ridgeSupport400_037_mask, ridgeSupport400_038_mask, ridgeSupport400_039_mask, ridgeSupport400_040_mask, ridgeSupport400_041_mask, ridgeSupport400_042_mask, ridgeSupport400_043_mask, ridgeSupport400_044_mask, ridgeSupport400_045_mask, ridgeSupport400_046_mask, ridgeSupport400_047_mask]
    decide +kernel
  · rw [ridgeSupport400_eq]
    simp only [ridgeSupport400_suffix_000, ridgeSupport400_suffix_001, ridgeSupport400_suffix_002, ridgeSupport400_suffix_003, ridgeSupport400_suffix_004, ridgeSupport400_suffix_005, ridgeSupport400_suffix_006, ridgeSupport400_suffix_007, ridgeSupport400_suffix_008, ridgeSupport400_suffix_009, ridgeSupport400_suffix_010, ridgeSupport400_suffix_011, ridgeSupport400_suffix_012, ridgeSupport400_suffix_013, ridgeSupport400_suffix_014, ridgeSupport400_suffix_015, ridgeSupport400_suffix_016, ridgeSupport400_suffix_017, ridgeSupport400_suffix_018, ridgeSupport400_suffix_019, ridgeSupport400_suffix_020, ridgeSupport400_suffix_021, ridgeSupport400_suffix_022, ridgeSupport400_suffix_023, ridgeSupport400_suffix_024, ridgeSupport400_suffix_025, ridgeSupport400_suffix_026, ridgeSupport400_suffix_027, ridgeSupport400_suffix_028, ridgeSupport400_suffix_029, ridgeSupport400_suffix_030, ridgeSupport400_suffix_031, ridgeSupport400_suffix_032, ridgeSupport400_suffix_033, ridgeSupport400_suffix_034, ridgeSupport400_suffix_035, ridgeSupport400_suffix_036, ridgeSupport400_suffix_037, ridgeSupport400_suffix_038, ridgeSupport400_suffix_039, ridgeSupport400_suffix_040, ridgeSupport400_suffix_041, ridgeSupport400_suffix_042, ridgeSupport400_suffix_043, ridgeSupport400_suffix_044, ridgeSupport400_suffix_045, ridgeSupport400_suffix_046, ridgeSupport400_suffix_047, ridgeSupport400_suffix_048, List.all_append, List.all_nil, ridgeSupport400_000_checked, ridgeSupport400_001_checked, ridgeSupport400_002_checked, ridgeSupport400_003_checked, ridgeSupport400_004_checked, ridgeSupport400_005_checked, ridgeSupport400_006_checked, ridgeSupport400_007_checked, ridgeSupport400_008_checked, ridgeSupport400_009_checked, ridgeSupport400_010_checked, ridgeSupport400_011_checked, ridgeSupport400_012_checked, ridgeSupport400_013_checked, ridgeSupport400_014_checked, ridgeSupport400_015_checked, ridgeSupport400_016_checked, ridgeSupport400_017_checked, ridgeSupport400_018_checked, ridgeSupport400_019_checked, ridgeSupport400_020_checked, ridgeSupport400_021_checked, ridgeSupport400_022_checked, ridgeSupport400_023_checked, ridgeSupport400_024_checked, ridgeSupport400_025_checked, ridgeSupport400_026_checked, ridgeSupport400_027_checked, ridgeSupport400_028_checked, ridgeSupport400_029_checked, ridgeSupport400_030_checked, ridgeSupport400_031_checked, ridgeSupport400_032_checked, ridgeSupport400_033_checked, ridgeSupport400_034_checked, ridgeSupport400_035_checked, ridgeSupport400_036_checked, ridgeSupport400_037_checked, ridgeSupport400_038_checked, ridgeSupport400_039_checked, ridgeSupport400_040_checked, ridgeSupport400_041_checked, ridgeSupport400_042_checked, ridgeSupport400_043_checked, ridgeSupport400_044_checked, ridgeSupport400_045_checked, ridgeSupport400_046_checked, ridgeSupport400_047_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase00
