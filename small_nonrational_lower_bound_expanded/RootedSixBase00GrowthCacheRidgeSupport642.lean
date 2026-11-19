module
prelude
public meta import LowerSchemas.FiniteRootedSixBase.Part0
public import BundledChecks.RootedSixBase00GrowthCacheRidgeSupport642Batch000
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
cert_ridgeSupport_suffix_decode 642 048 15
cert_ridgeSupport_suffix_decode_2 642 047 15 10 10 048 048 0
cert_ridgeSupport_suffix_decode_2 642 046 15 42 32 048 047 10
cert_ridgeSupport_suffix_decode_2 642 045 15 74 32 048 046 42
cert_ridgeSupport_suffix_decode_2 642 044 15 106 32 048 045 74
cert_ridgeSupport_suffix_decode_2 642 043 15 138 32 048 044 106
cert_ridgeSupport_suffix_decode_2 642 042 15 170 32 048 043 138
cert_ridgeSupport_suffix_decode_2 642 041 15 202 32 048 042 170
cert_ridgeSupport_suffix_decode_2 642 040 15 234 32 048 041 202
cert_ridgeSupport_suffix_decode_2 642 039 15 266 32 048 040 234
cert_ridgeSupport_suffix_decode_2 642 038 15 298 32 048 039 266
cert_ridgeSupport_suffix_decode_2 642 037 15 330 32 048 038 298
cert_ridgeSupport_suffix_decode_2 642 036 15 362 32 048 037 330
cert_ridgeSupport_suffix_decode_2 642 035 15 394 32 048 036 362
cert_ridgeSupport_suffix_decode_2 642 034 15 426 32 048 035 394
cert_ridgeSupport_suffix_decode_2 642 033 15 458 32 048 034 426
cert_ridgeSupport_suffix_decode_2 642 032 15 490 32 048 033 458
cert_ridgeSupport_suffix_decode_2 642 031 15 522 32 048 032 490
cert_ridgeSupport_suffix_decode_2 642 030 15 554 32 048 031 522
cert_ridgeSupport_suffix_decode_2 642 029 15 586 32 048 030 554
cert_ridgeSupport_suffix_decode_2 642 028 15 618 32 048 029 586
cert_ridgeSupport_suffix_decode_2 642 027 15 650 32 048 028 618
cert_ridgeSupport_suffix_decode_2 642 026 15 682 32 048 027 650
cert_ridgeSupport_suffix_decode_2 642 025 15 714 32 048 026 682
cert_ridgeSupport_suffix_decode_2 642 024 15 746 32 048 025 714
cert_ridgeSupport_suffix_decode_2 642 023 15 778 32 048 024 746
cert_ridgeSupport_suffix_decode_2 642 022 15 810 32 048 023 778
cert_ridgeSupport_suffix_decode_2 642 021 15 842 32 048 022 810
cert_ridgeSupport_suffix_decode_2 642 020 15 874 32 048 021 842
cert_ridgeSupport_suffix_decode_2 642 019 15 906 32 048 020 874
cert_ridgeSupport_suffix_decode_2 642 018 15 938 32 048 019 906
cert_ridgeSupport_suffix_decode_2 642 017 15 970 32 048 018 938
cert_ridgeSupport_suffix_decode_2 642 016 15 1002 32 048 017 970
cert_ridgeSupport_suffix_decode_2 642 015 15 1034 32 048 016 1002
cert_ridgeSupport_suffix_decode_2 642 014 15 1066 32 048 015 1034
cert_ridgeSupport_suffix_decode_2 642 013 15 1098 32 048 014 1066
cert_ridgeSupport_suffix_decode_2 642 012 15 1130 32 048 013 1098
cert_ridgeSupport_suffix_decode_2 642 011 15 1162 32 048 012 1130
cert_ridgeSupport_suffix_decode_2 642 010 15 1194 32 048 011 1162
cert_ridgeSupport_suffix_decode_2 642 009 15 1226 32 048 010 1194
cert_ridgeSupport_suffix_decode_2 642 008 15 1258 32 048 009 1226
cert_ridgeSupport_suffix_decode_2 642 007 15 1290 32 048 008 1258
cert_ridgeSupport_suffix_decode_2 642 006 15 1322 32 048 007 1290
cert_ridgeSupport_suffix_decode_2 642 005 15 1354 32 048 006 1322
cert_ridgeSupport_suffix_decode_2 642 004 15 1386 32 048 005 1354
cert_ridgeSupport_suffix_decode_2 642 003 15 1418 32 048 004 1386
cert_ridgeSupport_suffix_decode_2 642 002 15 1450 32 048 003 1418
cert_ridgeSupport_suffix_decode_2 642 001 15 1482 32 048 002 1450
cert_ridgeSupport_suffix_decode_2 642 000 15 1514 32 048 001 1482
cert_ridgeSupport_eq_3 642
theorem ridgeTest_large_642 : ridgeTest 642 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport642_eq]
    simp only [ridgeSupport642_suffix_000, ridgeSupport642_suffix_001, ridgeSupport642_suffix_002, ridgeSupport642_suffix_003, ridgeSupport642_suffix_004, ridgeSupport642_suffix_005, ridgeSupport642_suffix_006, ridgeSupport642_suffix_007, ridgeSupport642_suffix_008, ridgeSupport642_suffix_009, ridgeSupport642_suffix_010, ridgeSupport642_suffix_011, ridgeSupport642_suffix_012, ridgeSupport642_suffix_013, ridgeSupport642_suffix_014, ridgeSupport642_suffix_015, ridgeSupport642_suffix_016, ridgeSupport642_suffix_017, ridgeSupport642_suffix_018, ridgeSupport642_suffix_019, ridgeSupport642_suffix_020, ridgeSupport642_suffix_021, ridgeSupport642_suffix_022, ridgeSupport642_suffix_023, ridgeSupport642_suffix_024, ridgeSupport642_suffix_025, ridgeSupport642_suffix_026, ridgeSupport642_suffix_027, ridgeSupport642_suffix_028, ridgeSupport642_suffix_029, ridgeSupport642_suffix_030, ridgeSupport642_suffix_031, ridgeSupport642_suffix_032, ridgeSupport642_suffix_033, ridgeSupport642_suffix_034, ridgeSupport642_suffix_035, ridgeSupport642_suffix_036, ridgeSupport642_suffix_037, ridgeSupport642_suffix_038, ridgeSupport642_suffix_039, ridgeSupport642_suffix_040, ridgeSupport642_suffix_041, ridgeSupport642_suffix_042, ridgeSupport642_suffix_043, ridgeSupport642_suffix_044, ridgeSupport642_suffix_045, ridgeSupport642_suffix_046, ridgeSupport642_suffix_047, ridgeSupport642_suffix_048, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport642_000_mask, ridgeSupport642_001_mask, ridgeSupport642_002_mask, ridgeSupport642_003_mask, ridgeSupport642_004_mask, ridgeSupport642_005_mask, ridgeSupport642_006_mask, ridgeSupport642_007_mask, ridgeSupport642_008_mask, ridgeSupport642_009_mask, ridgeSupport642_010_mask, ridgeSupport642_011_mask, ridgeSupport642_012_mask, ridgeSupport642_013_mask, ridgeSupport642_014_mask, ridgeSupport642_015_mask, ridgeSupport642_016_mask, ridgeSupport642_017_mask, ridgeSupport642_018_mask, ridgeSupport642_019_mask, ridgeSupport642_020_mask, ridgeSupport642_021_mask, ridgeSupport642_022_mask, ridgeSupport642_023_mask, ridgeSupport642_024_mask, ridgeSupport642_025_mask, ridgeSupport642_026_mask, ridgeSupport642_027_mask, ridgeSupport642_028_mask, ridgeSupport642_029_mask, ridgeSupport642_030_mask, ridgeSupport642_031_mask, ridgeSupport642_032_mask, ridgeSupport642_033_mask, ridgeSupport642_034_mask, ridgeSupport642_035_mask, ridgeSupport642_036_mask, ridgeSupport642_037_mask, ridgeSupport642_038_mask, ridgeSupport642_039_mask, ridgeSupport642_040_mask, ridgeSupport642_041_mask, ridgeSupport642_042_mask, ridgeSupport642_043_mask, ridgeSupport642_044_mask, ridgeSupport642_045_mask, ridgeSupport642_046_mask, ridgeSupport642_047_mask]
    decide +kernel
  · rw [ridgeSupport642_eq]
    simp only [ridgeSupport642_suffix_000, ridgeSupport642_suffix_001, ridgeSupport642_suffix_002, ridgeSupport642_suffix_003, ridgeSupport642_suffix_004, ridgeSupport642_suffix_005, ridgeSupport642_suffix_006, ridgeSupport642_suffix_007, ridgeSupport642_suffix_008, ridgeSupport642_suffix_009, ridgeSupport642_suffix_010, ridgeSupport642_suffix_011, ridgeSupport642_suffix_012, ridgeSupport642_suffix_013, ridgeSupport642_suffix_014, ridgeSupport642_suffix_015, ridgeSupport642_suffix_016, ridgeSupport642_suffix_017, ridgeSupport642_suffix_018, ridgeSupport642_suffix_019, ridgeSupport642_suffix_020, ridgeSupport642_suffix_021, ridgeSupport642_suffix_022, ridgeSupport642_suffix_023, ridgeSupport642_suffix_024, ridgeSupport642_suffix_025, ridgeSupport642_suffix_026, ridgeSupport642_suffix_027, ridgeSupport642_suffix_028, ridgeSupport642_suffix_029, ridgeSupport642_suffix_030, ridgeSupport642_suffix_031, ridgeSupport642_suffix_032, ridgeSupport642_suffix_033, ridgeSupport642_suffix_034, ridgeSupport642_suffix_035, ridgeSupport642_suffix_036, ridgeSupport642_suffix_037, ridgeSupport642_suffix_038, ridgeSupport642_suffix_039, ridgeSupport642_suffix_040, ridgeSupport642_suffix_041, ridgeSupport642_suffix_042, ridgeSupport642_suffix_043, ridgeSupport642_suffix_044, ridgeSupport642_suffix_045, ridgeSupport642_suffix_046, ridgeSupport642_suffix_047, ridgeSupport642_suffix_048, List.all_append, List.all_nil, ridgeSupport642_000_checked, ridgeSupport642_001_checked, ridgeSupport642_002_checked, ridgeSupport642_003_checked, ridgeSupport642_004_checked, ridgeSupport642_005_checked, ridgeSupport642_006_checked, ridgeSupport642_007_checked, ridgeSupport642_008_checked, ridgeSupport642_009_checked, ridgeSupport642_010_checked, ridgeSupport642_011_checked, ridgeSupport642_012_checked, ridgeSupport642_013_checked, ridgeSupport642_014_checked, ridgeSupport642_015_checked, ridgeSupport642_016_checked, ridgeSupport642_017_checked, ridgeSupport642_018_checked, ridgeSupport642_019_checked, ridgeSupport642_020_checked, ridgeSupport642_021_checked, ridgeSupport642_022_checked, ridgeSupport642_023_checked, ridgeSupport642_024_checked, ridgeSupport642_025_checked, ridgeSupport642_026_checked, ridgeSupport642_027_checked, ridgeSupport642_028_checked, ridgeSupport642_029_checked, ridgeSupport642_030_checked, ridgeSupport642_031_checked, ridgeSupport642_032_checked, ridgeSupport642_033_checked, ridgeSupport642_034_checked, ridgeSupport642_035_checked, ridgeSupport642_036_checked, ridgeSupport642_037_checked, ridgeSupport642_038_checked, ridgeSupport642_039_checked, ridgeSupport642_040_checked, ridgeSupport642_041_checked, ridgeSupport642_042_checked, ridgeSupport642_043_checked, ridgeSupport642_044_checked, ridgeSupport642_045_checked, ridgeSupport642_046_checked, ridgeSupport642_047_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase00
