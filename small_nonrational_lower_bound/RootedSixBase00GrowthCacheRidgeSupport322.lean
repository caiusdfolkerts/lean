module
prelude
public meta import LowerSchemas.FiniteRootedSixBase
public import BundledChecks.RootedSixBase00GrowthCacheRidgeSupport322Batch000
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
cert_ridgeSupport_suffix_decode 322 048 15
cert_ridgeSupport_suffix_decode_2 322 047 15 10 10 048 048 0
cert_ridgeSupport_suffix_decode_2 322 046 15 42 32 048 047 10
cert_ridgeSupport_suffix_decode_2 322 045 15 74 32 048 046 42
cert_ridgeSupport_suffix_decode_2 322 044 15 106 32 048 045 74
cert_ridgeSupport_suffix_decode_2 322 043 15 138 32 048 044 106
cert_ridgeSupport_suffix_decode_2 322 042 15 170 32 048 043 138
cert_ridgeSupport_suffix_decode_2 322 041 15 202 32 048 042 170
cert_ridgeSupport_suffix_decode_2 322 040 15 234 32 048 041 202
cert_ridgeSupport_suffix_decode_2 322 039 15 266 32 048 040 234
cert_ridgeSupport_suffix_decode_2 322 038 15 298 32 048 039 266
cert_ridgeSupport_suffix_decode_2 322 037 15 330 32 048 038 298
cert_ridgeSupport_suffix_decode_2 322 036 15 362 32 048 037 330
cert_ridgeSupport_suffix_decode_2 322 035 15 394 32 048 036 362
cert_ridgeSupport_suffix_decode_2 322 034 15 426 32 048 035 394
cert_ridgeSupport_suffix_decode_2 322 033 15 458 32 048 034 426
cert_ridgeSupport_suffix_decode_2 322 032 15 490 32 048 033 458
cert_ridgeSupport_suffix_decode_2 322 031 15 522 32 048 032 490
cert_ridgeSupport_suffix_decode_2 322 030 15 554 32 048 031 522
cert_ridgeSupport_suffix_decode_2 322 029 15 586 32 048 030 554
cert_ridgeSupport_suffix_decode_2 322 028 15 618 32 048 029 586
cert_ridgeSupport_suffix_decode_2 322 027 15 650 32 048 028 618
cert_ridgeSupport_suffix_decode_2 322 026 15 682 32 048 027 650
cert_ridgeSupport_suffix_decode_2 322 025 15 714 32 048 026 682
cert_ridgeSupport_suffix_decode_2 322 024 15 746 32 048 025 714
cert_ridgeSupport_suffix_decode_2 322 023 15 778 32 048 024 746
cert_ridgeSupport_suffix_decode_2 322 022 15 810 32 048 023 778
cert_ridgeSupport_suffix_decode_2 322 021 15 842 32 048 022 810
cert_ridgeSupport_suffix_decode_2 322 020 15 874 32 048 021 842
cert_ridgeSupport_suffix_decode_2 322 019 15 906 32 048 020 874
cert_ridgeSupport_suffix_decode_2 322 018 15 938 32 048 019 906
cert_ridgeSupport_suffix_decode_2 322 017 15 970 32 048 018 938
cert_ridgeSupport_suffix_decode_2 322 016 15 1002 32 048 017 970
cert_ridgeSupport_suffix_decode_2 322 015 15 1034 32 048 016 1002
cert_ridgeSupport_suffix_decode_2 322 014 15 1066 32 048 015 1034
cert_ridgeSupport_suffix_decode_2 322 013 15 1098 32 048 014 1066
cert_ridgeSupport_suffix_decode_2 322 012 15 1130 32 048 013 1098
cert_ridgeSupport_suffix_decode_2 322 011 15 1162 32 048 012 1130
cert_ridgeSupport_suffix_decode_2 322 010 15 1194 32 048 011 1162
cert_ridgeSupport_suffix_decode_2 322 009 15 1226 32 048 010 1194
cert_ridgeSupport_suffix_decode_2 322 008 15 1258 32 048 009 1226
cert_ridgeSupport_suffix_decode_2 322 007 15 1290 32 048 008 1258
cert_ridgeSupport_suffix_decode_2 322 006 15 1322 32 048 007 1290
cert_ridgeSupport_suffix_decode_2 322 005 15 1354 32 048 006 1322
cert_ridgeSupport_suffix_decode_2 322 004 15 1386 32 048 005 1354
cert_ridgeSupport_suffix_decode_2 322 003 15 1418 32 048 004 1386
cert_ridgeSupport_suffix_decode_2 322 002 15 1450 32 048 003 1418
cert_ridgeSupport_suffix_decode_2 322 001 15 1482 32 048 002 1450
cert_ridgeSupport_suffix_decode_2 322 000 15 1514 32 048 001 1482
cert_ridgeSupport_eq_3 322
theorem ridgeTest_large_322 : ridgeTest 322 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport322_eq]
    simp only [ridgeSupport322_suffix_000, ridgeSupport322_suffix_001, ridgeSupport322_suffix_002, ridgeSupport322_suffix_003, ridgeSupport322_suffix_004, ridgeSupport322_suffix_005, ridgeSupport322_suffix_006, ridgeSupport322_suffix_007, ridgeSupport322_suffix_008, ridgeSupport322_suffix_009, ridgeSupport322_suffix_010, ridgeSupport322_suffix_011, ridgeSupport322_suffix_012, ridgeSupport322_suffix_013, ridgeSupport322_suffix_014, ridgeSupport322_suffix_015, ridgeSupport322_suffix_016, ridgeSupport322_suffix_017, ridgeSupport322_suffix_018, ridgeSupport322_suffix_019, ridgeSupport322_suffix_020, ridgeSupport322_suffix_021, ridgeSupport322_suffix_022, ridgeSupport322_suffix_023, ridgeSupport322_suffix_024, ridgeSupport322_suffix_025, ridgeSupport322_suffix_026, ridgeSupport322_suffix_027, ridgeSupport322_suffix_028, ridgeSupport322_suffix_029, ridgeSupport322_suffix_030, ridgeSupport322_suffix_031, ridgeSupport322_suffix_032, ridgeSupport322_suffix_033, ridgeSupport322_suffix_034, ridgeSupport322_suffix_035, ridgeSupport322_suffix_036, ridgeSupport322_suffix_037, ridgeSupport322_suffix_038, ridgeSupport322_suffix_039, ridgeSupport322_suffix_040, ridgeSupport322_suffix_041, ridgeSupport322_suffix_042, ridgeSupport322_suffix_043, ridgeSupport322_suffix_044, ridgeSupport322_suffix_045, ridgeSupport322_suffix_046, ridgeSupport322_suffix_047, ridgeSupport322_suffix_048, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport322_000_mask, ridgeSupport322_001_mask, ridgeSupport322_002_mask, ridgeSupport322_003_mask, ridgeSupport322_004_mask, ridgeSupport322_005_mask, ridgeSupport322_006_mask, ridgeSupport322_007_mask, ridgeSupport322_008_mask, ridgeSupport322_009_mask, ridgeSupport322_010_mask, ridgeSupport322_011_mask, ridgeSupport322_012_mask, ridgeSupport322_013_mask, ridgeSupport322_014_mask, ridgeSupport322_015_mask, ridgeSupport322_016_mask, ridgeSupport322_017_mask, ridgeSupport322_018_mask, ridgeSupport322_019_mask, ridgeSupport322_020_mask, ridgeSupport322_021_mask, ridgeSupport322_022_mask, ridgeSupport322_023_mask, ridgeSupport322_024_mask, ridgeSupport322_025_mask, ridgeSupport322_026_mask, ridgeSupport322_027_mask, ridgeSupport322_028_mask, ridgeSupport322_029_mask, ridgeSupport322_030_mask, ridgeSupport322_031_mask, ridgeSupport322_032_mask, ridgeSupport322_033_mask, ridgeSupport322_034_mask, ridgeSupport322_035_mask, ridgeSupport322_036_mask, ridgeSupport322_037_mask, ridgeSupport322_038_mask, ridgeSupport322_039_mask, ridgeSupport322_040_mask, ridgeSupport322_041_mask, ridgeSupport322_042_mask, ridgeSupport322_043_mask, ridgeSupport322_044_mask, ridgeSupport322_045_mask, ridgeSupport322_046_mask, ridgeSupport322_047_mask]
    decide +kernel
  · rw [ridgeSupport322_eq]
    simp only [ridgeSupport322_suffix_000, ridgeSupport322_suffix_001, ridgeSupport322_suffix_002, ridgeSupport322_suffix_003, ridgeSupport322_suffix_004, ridgeSupport322_suffix_005, ridgeSupport322_suffix_006, ridgeSupport322_suffix_007, ridgeSupport322_suffix_008, ridgeSupport322_suffix_009, ridgeSupport322_suffix_010, ridgeSupport322_suffix_011, ridgeSupport322_suffix_012, ridgeSupport322_suffix_013, ridgeSupport322_suffix_014, ridgeSupport322_suffix_015, ridgeSupport322_suffix_016, ridgeSupport322_suffix_017, ridgeSupport322_suffix_018, ridgeSupport322_suffix_019, ridgeSupport322_suffix_020, ridgeSupport322_suffix_021, ridgeSupport322_suffix_022, ridgeSupport322_suffix_023, ridgeSupport322_suffix_024, ridgeSupport322_suffix_025, ridgeSupport322_suffix_026, ridgeSupport322_suffix_027, ridgeSupport322_suffix_028, ridgeSupport322_suffix_029, ridgeSupport322_suffix_030, ridgeSupport322_suffix_031, ridgeSupport322_suffix_032, ridgeSupport322_suffix_033, ridgeSupport322_suffix_034, ridgeSupport322_suffix_035, ridgeSupport322_suffix_036, ridgeSupport322_suffix_037, ridgeSupport322_suffix_038, ridgeSupport322_suffix_039, ridgeSupport322_suffix_040, ridgeSupport322_suffix_041, ridgeSupport322_suffix_042, ridgeSupport322_suffix_043, ridgeSupport322_suffix_044, ridgeSupport322_suffix_045, ridgeSupport322_suffix_046, ridgeSupport322_suffix_047, ridgeSupport322_suffix_048, List.all_append, List.all_nil, ridgeSupport322_000_checked, ridgeSupport322_001_checked, ridgeSupport322_002_checked, ridgeSupport322_003_checked, ridgeSupport322_004_checked, ridgeSupport322_005_checked, ridgeSupport322_006_checked, ridgeSupport322_007_checked, ridgeSupport322_008_checked, ridgeSupport322_009_checked, ridgeSupport322_010_checked, ridgeSupport322_011_checked, ridgeSupport322_012_checked, ridgeSupport322_013_checked, ridgeSupport322_014_checked, ridgeSupport322_015_checked, ridgeSupport322_016_checked, ridgeSupport322_017_checked, ridgeSupport322_018_checked, ridgeSupport322_019_checked, ridgeSupport322_020_checked, ridgeSupport322_021_checked, ridgeSupport322_022_checked, ridgeSupport322_023_checked, ridgeSupport322_024_checked, ridgeSupport322_025_checked, ridgeSupport322_026_checked, ridgeSupport322_027_checked, ridgeSupport322_028_checked, ridgeSupport322_029_checked, ridgeSupport322_030_checked, ridgeSupport322_031_checked, ridgeSupport322_032_checked, ridgeSupport322_033_checked, ridgeSupport322_034_checked, ridgeSupport322_035_checked, ridgeSupport322_036_checked, ridgeSupport322_037_checked, ridgeSupport322_038_checked, ridgeSupport322_039_checked, ridgeSupport322_040_checked, ridgeSupport322_041_checked, ridgeSupport322_042_checked, ridgeSupport322_043_checked, ridgeSupport322_044_checked, ridgeSupport322_045_checked, ridgeSupport322_046_checked, ridgeSupport322_047_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase00
