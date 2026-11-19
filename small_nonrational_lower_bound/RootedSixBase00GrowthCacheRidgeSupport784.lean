module
prelude
public meta import LowerSchemas.FiniteRootedSixBase
public import BundledChecks.RootedSixBase00GrowthCacheRidgeSupport784Batch000
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
cert_ridgeSupport_suffix_decode 784 048 15
cert_ridgeSupport_suffix_decode_2 784 047 15 10 10 048 048 0
cert_ridgeSupport_suffix_decode_2 784 046 15 42 32 048 047 10
cert_ridgeSupport_suffix_decode_2 784 045 15 74 32 048 046 42
cert_ridgeSupport_suffix_decode_2 784 044 15 106 32 048 045 74
cert_ridgeSupport_suffix_decode_2 784 043 15 138 32 048 044 106
cert_ridgeSupport_suffix_decode_2 784 042 15 170 32 048 043 138
cert_ridgeSupport_suffix_decode_2 784 041 15 202 32 048 042 170
cert_ridgeSupport_suffix_decode_2 784 040 15 234 32 048 041 202
cert_ridgeSupport_suffix_decode_2 784 039 15 266 32 048 040 234
cert_ridgeSupport_suffix_decode_2 784 038 15 298 32 048 039 266
cert_ridgeSupport_suffix_decode_2 784 037 15 330 32 048 038 298
cert_ridgeSupport_suffix_decode_2 784 036 15 362 32 048 037 330
cert_ridgeSupport_suffix_decode_2 784 035 15 394 32 048 036 362
cert_ridgeSupport_suffix_decode_2 784 034 15 426 32 048 035 394
cert_ridgeSupport_suffix_decode_2 784 033 15 458 32 048 034 426
cert_ridgeSupport_suffix_decode_2 784 032 15 490 32 048 033 458
cert_ridgeSupport_suffix_decode_2 784 031 15 522 32 048 032 490
cert_ridgeSupport_suffix_decode_2 784 030 15 554 32 048 031 522
cert_ridgeSupport_suffix_decode_2 784 029 15 586 32 048 030 554
cert_ridgeSupport_suffix_decode_2 784 028 15 618 32 048 029 586
cert_ridgeSupport_suffix_decode_2 784 027 15 650 32 048 028 618
cert_ridgeSupport_suffix_decode_2 784 026 15 682 32 048 027 650
cert_ridgeSupport_suffix_decode_2 784 025 15 714 32 048 026 682
cert_ridgeSupport_suffix_decode_2 784 024 15 746 32 048 025 714
cert_ridgeSupport_suffix_decode_2 784 023 15 778 32 048 024 746
cert_ridgeSupport_suffix_decode_2 784 022 15 810 32 048 023 778
cert_ridgeSupport_suffix_decode_2 784 021 15 842 32 048 022 810
cert_ridgeSupport_suffix_decode_2 784 020 15 874 32 048 021 842
cert_ridgeSupport_suffix_decode_2 784 019 15 906 32 048 020 874
cert_ridgeSupport_suffix_decode_2 784 018 15 938 32 048 019 906
cert_ridgeSupport_suffix_decode_2 784 017 15 970 32 048 018 938
cert_ridgeSupport_suffix_decode_2 784 016 15 1002 32 048 017 970
cert_ridgeSupport_suffix_decode_2 784 015 15 1034 32 048 016 1002
cert_ridgeSupport_suffix_decode_2 784 014 15 1066 32 048 015 1034
cert_ridgeSupport_suffix_decode_2 784 013 15 1098 32 048 014 1066
cert_ridgeSupport_suffix_decode_2 784 012 15 1130 32 048 013 1098
cert_ridgeSupport_suffix_decode_2 784 011 15 1162 32 048 012 1130
cert_ridgeSupport_suffix_decode_2 784 010 15 1194 32 048 011 1162
cert_ridgeSupport_suffix_decode_2 784 009 15 1226 32 048 010 1194
cert_ridgeSupport_suffix_decode_2 784 008 15 1258 32 048 009 1226
cert_ridgeSupport_suffix_decode_2 784 007 15 1290 32 048 008 1258
cert_ridgeSupport_suffix_decode_2 784 006 15 1322 32 048 007 1290
cert_ridgeSupport_suffix_decode_2 784 005 15 1354 32 048 006 1322
cert_ridgeSupport_suffix_decode_2 784 004 15 1386 32 048 005 1354
cert_ridgeSupport_suffix_decode_2 784 003 15 1418 32 048 004 1386
cert_ridgeSupport_suffix_decode_2 784 002 15 1450 32 048 003 1418
cert_ridgeSupport_suffix_decode_2 784 001 15 1482 32 048 002 1450
cert_ridgeSupport_suffix_decode_2 784 000 15 1514 32 048 001 1482
cert_ridgeSupport_eq_3 784
theorem ridgeTest_large_784 : ridgeTest 784 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport784_eq]
    simp only [ridgeSupport784_suffix_000, ridgeSupport784_suffix_001, ridgeSupport784_suffix_002, ridgeSupport784_suffix_003, ridgeSupport784_suffix_004, ridgeSupport784_suffix_005, ridgeSupport784_suffix_006, ridgeSupport784_suffix_007, ridgeSupport784_suffix_008, ridgeSupport784_suffix_009, ridgeSupport784_suffix_010, ridgeSupport784_suffix_011, ridgeSupport784_suffix_012, ridgeSupport784_suffix_013, ridgeSupport784_suffix_014, ridgeSupport784_suffix_015, ridgeSupport784_suffix_016, ridgeSupport784_suffix_017, ridgeSupport784_suffix_018, ridgeSupport784_suffix_019, ridgeSupport784_suffix_020, ridgeSupport784_suffix_021, ridgeSupport784_suffix_022, ridgeSupport784_suffix_023, ridgeSupport784_suffix_024, ridgeSupport784_suffix_025, ridgeSupport784_suffix_026, ridgeSupport784_suffix_027, ridgeSupport784_suffix_028, ridgeSupport784_suffix_029, ridgeSupport784_suffix_030, ridgeSupport784_suffix_031, ridgeSupport784_suffix_032, ridgeSupport784_suffix_033, ridgeSupport784_suffix_034, ridgeSupport784_suffix_035, ridgeSupport784_suffix_036, ridgeSupport784_suffix_037, ridgeSupport784_suffix_038, ridgeSupport784_suffix_039, ridgeSupport784_suffix_040, ridgeSupport784_suffix_041, ridgeSupport784_suffix_042, ridgeSupport784_suffix_043, ridgeSupport784_suffix_044, ridgeSupport784_suffix_045, ridgeSupport784_suffix_046, ridgeSupport784_suffix_047, ridgeSupport784_suffix_048, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport784_000_mask, ridgeSupport784_001_mask, ridgeSupport784_002_mask, ridgeSupport784_003_mask, ridgeSupport784_004_mask, ridgeSupport784_005_mask, ridgeSupport784_006_mask, ridgeSupport784_007_mask, ridgeSupport784_008_mask, ridgeSupport784_009_mask, ridgeSupport784_010_mask, ridgeSupport784_011_mask, ridgeSupport784_012_mask, ridgeSupport784_013_mask, ridgeSupport784_014_mask, ridgeSupport784_015_mask, ridgeSupport784_016_mask, ridgeSupport784_017_mask, ridgeSupport784_018_mask, ridgeSupport784_019_mask, ridgeSupport784_020_mask, ridgeSupport784_021_mask, ridgeSupport784_022_mask, ridgeSupport784_023_mask, ridgeSupport784_024_mask, ridgeSupport784_025_mask, ridgeSupport784_026_mask, ridgeSupport784_027_mask, ridgeSupport784_028_mask, ridgeSupport784_029_mask, ridgeSupport784_030_mask, ridgeSupport784_031_mask, ridgeSupport784_032_mask, ridgeSupport784_033_mask, ridgeSupport784_034_mask, ridgeSupport784_035_mask, ridgeSupport784_036_mask, ridgeSupport784_037_mask, ridgeSupport784_038_mask, ridgeSupport784_039_mask, ridgeSupport784_040_mask, ridgeSupport784_041_mask, ridgeSupport784_042_mask, ridgeSupport784_043_mask, ridgeSupport784_044_mask, ridgeSupport784_045_mask, ridgeSupport784_046_mask, ridgeSupport784_047_mask]
    decide +kernel
  · rw [ridgeSupport784_eq]
    simp only [ridgeSupport784_suffix_000, ridgeSupport784_suffix_001, ridgeSupport784_suffix_002, ridgeSupport784_suffix_003, ridgeSupport784_suffix_004, ridgeSupport784_suffix_005, ridgeSupport784_suffix_006, ridgeSupport784_suffix_007, ridgeSupport784_suffix_008, ridgeSupport784_suffix_009, ridgeSupport784_suffix_010, ridgeSupport784_suffix_011, ridgeSupport784_suffix_012, ridgeSupport784_suffix_013, ridgeSupport784_suffix_014, ridgeSupport784_suffix_015, ridgeSupport784_suffix_016, ridgeSupport784_suffix_017, ridgeSupport784_suffix_018, ridgeSupport784_suffix_019, ridgeSupport784_suffix_020, ridgeSupport784_suffix_021, ridgeSupport784_suffix_022, ridgeSupport784_suffix_023, ridgeSupport784_suffix_024, ridgeSupport784_suffix_025, ridgeSupport784_suffix_026, ridgeSupport784_suffix_027, ridgeSupport784_suffix_028, ridgeSupport784_suffix_029, ridgeSupport784_suffix_030, ridgeSupport784_suffix_031, ridgeSupport784_suffix_032, ridgeSupport784_suffix_033, ridgeSupport784_suffix_034, ridgeSupport784_suffix_035, ridgeSupport784_suffix_036, ridgeSupport784_suffix_037, ridgeSupport784_suffix_038, ridgeSupport784_suffix_039, ridgeSupport784_suffix_040, ridgeSupport784_suffix_041, ridgeSupport784_suffix_042, ridgeSupport784_suffix_043, ridgeSupport784_suffix_044, ridgeSupport784_suffix_045, ridgeSupport784_suffix_046, ridgeSupport784_suffix_047, ridgeSupport784_suffix_048, List.all_append, List.all_nil, ridgeSupport784_000_checked, ridgeSupport784_001_checked, ridgeSupport784_002_checked, ridgeSupport784_003_checked, ridgeSupport784_004_checked, ridgeSupport784_005_checked, ridgeSupport784_006_checked, ridgeSupport784_007_checked, ridgeSupport784_008_checked, ridgeSupport784_009_checked, ridgeSupport784_010_checked, ridgeSupport784_011_checked, ridgeSupport784_012_checked, ridgeSupport784_013_checked, ridgeSupport784_014_checked, ridgeSupport784_015_checked, ridgeSupport784_016_checked, ridgeSupport784_017_checked, ridgeSupport784_018_checked, ridgeSupport784_019_checked, ridgeSupport784_020_checked, ridgeSupport784_021_checked, ridgeSupport784_022_checked, ridgeSupport784_023_checked, ridgeSupport784_024_checked, ridgeSupport784_025_checked, ridgeSupport784_026_checked, ridgeSupport784_027_checked, ridgeSupport784_028_checked, ridgeSupport784_029_checked, ridgeSupport784_030_checked, ridgeSupport784_031_checked, ridgeSupport784_032_checked, ridgeSupport784_033_checked, ridgeSupport784_034_checked, ridgeSupport784_035_checked, ridgeSupport784_036_checked, ridgeSupport784_037_checked, ridgeSupport784_038_checked, ridgeSupport784_039_checked, ridgeSupport784_040_checked, ridgeSupport784_041_checked, ridgeSupport784_042_checked, ridgeSupport784_043_checked, ridgeSupport784_044_checked, ridgeSupport784_045_checked, ridgeSupport784_046_checked, ridgeSupport784_047_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase00
