module
prelude
public meta import LowerSchemas.FiniteRootedSixBase
public import BundledChecks.RootedSixBase00GrowthCacheRidgeSupport194Batch000
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
cert_ridgeSupport_suffix_decode 194 048 15
cert_ridgeSupport_suffix_decode_2 194 047 15 10 10 048 048 0
cert_ridgeSupport_suffix_decode_2 194 046 15 42 32 048 047 10
cert_ridgeSupport_suffix_decode_2 194 045 15 74 32 048 046 42
cert_ridgeSupport_suffix_decode_2 194 044 15 106 32 048 045 74
cert_ridgeSupport_suffix_decode_2 194 043 15 138 32 048 044 106
cert_ridgeSupport_suffix_decode_2 194 042 15 170 32 048 043 138
cert_ridgeSupport_suffix_decode_2 194 041 15 202 32 048 042 170
cert_ridgeSupport_suffix_decode_2 194 040 15 234 32 048 041 202
cert_ridgeSupport_suffix_decode_2 194 039 15 266 32 048 040 234
cert_ridgeSupport_suffix_decode_2 194 038 15 298 32 048 039 266
cert_ridgeSupport_suffix_decode_2 194 037 15 330 32 048 038 298
cert_ridgeSupport_suffix_decode_2 194 036 15 362 32 048 037 330
cert_ridgeSupport_suffix_decode_2 194 035 15 394 32 048 036 362
cert_ridgeSupport_suffix_decode_2 194 034 15 426 32 048 035 394
cert_ridgeSupport_suffix_decode_2 194 033 15 458 32 048 034 426
cert_ridgeSupport_suffix_decode_2 194 032 15 490 32 048 033 458
cert_ridgeSupport_suffix_decode_2 194 031 15 522 32 048 032 490
cert_ridgeSupport_suffix_decode_2 194 030 15 554 32 048 031 522
cert_ridgeSupport_suffix_decode_2 194 029 15 586 32 048 030 554
cert_ridgeSupport_suffix_decode_2 194 028 15 618 32 048 029 586
cert_ridgeSupport_suffix_decode_2 194 027 15 650 32 048 028 618
cert_ridgeSupport_suffix_decode_2 194 026 15 682 32 048 027 650
cert_ridgeSupport_suffix_decode_2 194 025 15 714 32 048 026 682
cert_ridgeSupport_suffix_decode_2 194 024 15 746 32 048 025 714
cert_ridgeSupport_suffix_decode_2 194 023 15 778 32 048 024 746
cert_ridgeSupport_suffix_decode_2 194 022 15 810 32 048 023 778
cert_ridgeSupport_suffix_decode_2 194 021 15 842 32 048 022 810
cert_ridgeSupport_suffix_decode_2 194 020 15 874 32 048 021 842
cert_ridgeSupport_suffix_decode_2 194 019 15 906 32 048 020 874
cert_ridgeSupport_suffix_decode_2 194 018 15 938 32 048 019 906
cert_ridgeSupport_suffix_decode_2 194 017 15 970 32 048 018 938
cert_ridgeSupport_suffix_decode_2 194 016 15 1002 32 048 017 970
cert_ridgeSupport_suffix_decode_2 194 015 15 1034 32 048 016 1002
cert_ridgeSupport_suffix_decode_2 194 014 15 1066 32 048 015 1034
cert_ridgeSupport_suffix_decode_2 194 013 15 1098 32 048 014 1066
cert_ridgeSupport_suffix_decode_2 194 012 15 1130 32 048 013 1098
cert_ridgeSupport_suffix_decode_2 194 011 15 1162 32 048 012 1130
cert_ridgeSupport_suffix_decode_2 194 010 15 1194 32 048 011 1162
cert_ridgeSupport_suffix_decode_2 194 009 15 1226 32 048 010 1194
cert_ridgeSupport_suffix_decode_2 194 008 15 1258 32 048 009 1226
cert_ridgeSupport_suffix_decode_2 194 007 15 1290 32 048 008 1258
cert_ridgeSupport_suffix_decode_2 194 006 15 1322 32 048 007 1290
cert_ridgeSupport_suffix_decode_2 194 005 15 1354 32 048 006 1322
cert_ridgeSupport_suffix_decode_2 194 004 15 1386 32 048 005 1354
cert_ridgeSupport_suffix_decode_2 194 003 15 1418 32 048 004 1386
cert_ridgeSupport_suffix_decode_2 194 002 15 1450 32 048 003 1418
cert_ridgeSupport_suffix_decode_2 194 001 15 1482 32 048 002 1450
cert_ridgeSupport_suffix_decode_2 194 000 15 1514 32 048 001 1482
cert_ridgeSupport_eq_3 194
theorem ridgeTest_large_194 : ridgeTest 194 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport194_eq]
    simp only [ridgeSupport194_suffix_000, ridgeSupport194_suffix_001, ridgeSupport194_suffix_002, ridgeSupport194_suffix_003, ridgeSupport194_suffix_004, ridgeSupport194_suffix_005, ridgeSupport194_suffix_006, ridgeSupport194_suffix_007, ridgeSupport194_suffix_008, ridgeSupport194_suffix_009, ridgeSupport194_suffix_010, ridgeSupport194_suffix_011, ridgeSupport194_suffix_012, ridgeSupport194_suffix_013, ridgeSupport194_suffix_014, ridgeSupport194_suffix_015, ridgeSupport194_suffix_016, ridgeSupport194_suffix_017, ridgeSupport194_suffix_018, ridgeSupport194_suffix_019, ridgeSupport194_suffix_020, ridgeSupport194_suffix_021, ridgeSupport194_suffix_022, ridgeSupport194_suffix_023, ridgeSupport194_suffix_024, ridgeSupport194_suffix_025, ridgeSupport194_suffix_026, ridgeSupport194_suffix_027, ridgeSupport194_suffix_028, ridgeSupport194_suffix_029, ridgeSupport194_suffix_030, ridgeSupport194_suffix_031, ridgeSupport194_suffix_032, ridgeSupport194_suffix_033, ridgeSupport194_suffix_034, ridgeSupport194_suffix_035, ridgeSupport194_suffix_036, ridgeSupport194_suffix_037, ridgeSupport194_suffix_038, ridgeSupport194_suffix_039, ridgeSupport194_suffix_040, ridgeSupport194_suffix_041, ridgeSupport194_suffix_042, ridgeSupport194_suffix_043, ridgeSupport194_suffix_044, ridgeSupport194_suffix_045, ridgeSupport194_suffix_046, ridgeSupport194_suffix_047, ridgeSupport194_suffix_048, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport194_000_mask, ridgeSupport194_001_mask, ridgeSupport194_002_mask, ridgeSupport194_003_mask, ridgeSupport194_004_mask, ridgeSupport194_005_mask, ridgeSupport194_006_mask, ridgeSupport194_007_mask, ridgeSupport194_008_mask, ridgeSupport194_009_mask, ridgeSupport194_010_mask, ridgeSupport194_011_mask, ridgeSupport194_012_mask, ridgeSupport194_013_mask, ridgeSupport194_014_mask, ridgeSupport194_015_mask, ridgeSupport194_016_mask, ridgeSupport194_017_mask, ridgeSupport194_018_mask, ridgeSupport194_019_mask, ridgeSupport194_020_mask, ridgeSupport194_021_mask, ridgeSupport194_022_mask, ridgeSupport194_023_mask, ridgeSupport194_024_mask, ridgeSupport194_025_mask, ridgeSupport194_026_mask, ridgeSupport194_027_mask, ridgeSupport194_028_mask, ridgeSupport194_029_mask, ridgeSupport194_030_mask, ridgeSupport194_031_mask, ridgeSupport194_032_mask, ridgeSupport194_033_mask, ridgeSupport194_034_mask, ridgeSupport194_035_mask, ridgeSupport194_036_mask, ridgeSupport194_037_mask, ridgeSupport194_038_mask, ridgeSupport194_039_mask, ridgeSupport194_040_mask, ridgeSupport194_041_mask, ridgeSupport194_042_mask, ridgeSupport194_043_mask, ridgeSupport194_044_mask, ridgeSupport194_045_mask, ridgeSupport194_046_mask, ridgeSupport194_047_mask]
    decide +kernel
  · rw [ridgeSupport194_eq]
    simp only [ridgeSupport194_suffix_000, ridgeSupport194_suffix_001, ridgeSupport194_suffix_002, ridgeSupport194_suffix_003, ridgeSupport194_suffix_004, ridgeSupport194_suffix_005, ridgeSupport194_suffix_006, ridgeSupport194_suffix_007, ridgeSupport194_suffix_008, ridgeSupport194_suffix_009, ridgeSupport194_suffix_010, ridgeSupport194_suffix_011, ridgeSupport194_suffix_012, ridgeSupport194_suffix_013, ridgeSupport194_suffix_014, ridgeSupport194_suffix_015, ridgeSupport194_suffix_016, ridgeSupport194_suffix_017, ridgeSupport194_suffix_018, ridgeSupport194_suffix_019, ridgeSupport194_suffix_020, ridgeSupport194_suffix_021, ridgeSupport194_suffix_022, ridgeSupport194_suffix_023, ridgeSupport194_suffix_024, ridgeSupport194_suffix_025, ridgeSupport194_suffix_026, ridgeSupport194_suffix_027, ridgeSupport194_suffix_028, ridgeSupport194_suffix_029, ridgeSupport194_suffix_030, ridgeSupport194_suffix_031, ridgeSupport194_suffix_032, ridgeSupport194_suffix_033, ridgeSupport194_suffix_034, ridgeSupport194_suffix_035, ridgeSupport194_suffix_036, ridgeSupport194_suffix_037, ridgeSupport194_suffix_038, ridgeSupport194_suffix_039, ridgeSupport194_suffix_040, ridgeSupport194_suffix_041, ridgeSupport194_suffix_042, ridgeSupport194_suffix_043, ridgeSupport194_suffix_044, ridgeSupport194_suffix_045, ridgeSupport194_suffix_046, ridgeSupport194_suffix_047, ridgeSupport194_suffix_048, List.all_append, List.all_nil, ridgeSupport194_000_checked, ridgeSupport194_001_checked, ridgeSupport194_002_checked, ridgeSupport194_003_checked, ridgeSupport194_004_checked, ridgeSupport194_005_checked, ridgeSupport194_006_checked, ridgeSupport194_007_checked, ridgeSupport194_008_checked, ridgeSupport194_009_checked, ridgeSupport194_010_checked, ridgeSupport194_011_checked, ridgeSupport194_012_checked, ridgeSupport194_013_checked, ridgeSupport194_014_checked, ridgeSupport194_015_checked, ridgeSupport194_016_checked, ridgeSupport194_017_checked, ridgeSupport194_018_checked, ridgeSupport194_019_checked, ridgeSupport194_020_checked, ridgeSupport194_021_checked, ridgeSupport194_022_checked, ridgeSupport194_023_checked, ridgeSupport194_024_checked, ridgeSupport194_025_checked, ridgeSupport194_026_checked, ridgeSupport194_027_checked, ridgeSupport194_028_checked, ridgeSupport194_029_checked, ridgeSupport194_030_checked, ridgeSupport194_031_checked, ridgeSupport194_032_checked, ridgeSupport194_033_checked, ridgeSupport194_034_checked, ridgeSupport194_035_checked, ridgeSupport194_036_checked, ridgeSupport194_037_checked, ridgeSupport194_038_checked, ridgeSupport194_039_checked, ridgeSupport194_040_checked, ridgeSupport194_041_checked, ridgeSupport194_042_checked, ridgeSupport194_043_checked, ridgeSupport194_044_checked, ridgeSupport194_045_checked, ridgeSupport194_046_checked, ridgeSupport194_047_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase00
