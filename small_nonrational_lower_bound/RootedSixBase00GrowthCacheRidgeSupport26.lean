module
prelude
public meta import LowerSchemas.FiniteRootedSixBase
public import BundledChecks.RootedSixBase00GrowthCacheRidgeSupport26Batch000
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
cert_ridgeSupport_suffix_decode 26 043 15
cert_ridgeSupport_suffix_decode_2 26 042 15 5 5 043 043 0
cert_ridgeSupport_suffix_decode_2 26 041 15 37 32 043 042 5
cert_ridgeSupport_suffix_decode_2 26 040 15 69 32 043 041 37
cert_ridgeSupport_suffix_decode_2 26 039 15 101 32 043 040 69
cert_ridgeSupport_suffix_decode_2 26 038 15 133 32 043 039 101
cert_ridgeSupport_suffix_decode_2 26 037 15 165 32 043 038 133
cert_ridgeSupport_suffix_decode_2 26 036 15 197 32 043 037 165
cert_ridgeSupport_suffix_decode_2 26 035 15 229 32 043 036 197
cert_ridgeSupport_suffix_decode_2 26 034 15 261 32 043 035 229
cert_ridgeSupport_suffix_decode_2 26 033 15 293 32 043 034 261
cert_ridgeSupport_suffix_decode_2 26 032 15 325 32 043 033 293
cert_ridgeSupport_suffix_decode_2 26 031 15 357 32 043 032 325
cert_ridgeSupport_suffix_decode_2 26 030 15 389 32 043 031 357
cert_ridgeSupport_suffix_decode_2 26 029 15 421 32 043 030 389
cert_ridgeSupport_suffix_decode_2 26 028 15 453 32 043 029 421
cert_ridgeSupport_suffix_decode_2 26 027 15 485 32 043 028 453
cert_ridgeSupport_suffix_decode_2 26 026 15 517 32 043 027 485
cert_ridgeSupport_suffix_decode_2 26 025 15 549 32 043 026 517
cert_ridgeSupport_suffix_decode_2 26 024 15 581 32 043 025 549
cert_ridgeSupport_suffix_decode_2 26 023 15 613 32 043 024 581
cert_ridgeSupport_suffix_decode_2 26 022 15 645 32 043 023 613
cert_ridgeSupport_suffix_decode_2 26 021 15 677 32 043 022 645
cert_ridgeSupport_suffix_decode_2 26 020 15 709 32 043 021 677
cert_ridgeSupport_suffix_decode_2 26 019 15 741 32 043 020 709
cert_ridgeSupport_suffix_decode_2 26 018 15 773 32 043 019 741
cert_ridgeSupport_suffix_decode_2 26 017 15 805 32 043 018 773
cert_ridgeSupport_suffix_decode_2 26 016 15 837 32 043 017 805
cert_ridgeSupport_suffix_decode_2 26 015 15 869 32 043 016 837
cert_ridgeSupport_suffix_decode_2 26 014 15 901 32 043 015 869
cert_ridgeSupport_suffix_decode_2 26 013 15 933 32 043 014 901
cert_ridgeSupport_suffix_decode_2 26 012 15 965 32 043 013 933
cert_ridgeSupport_suffix_decode_2 26 011 15 997 32 043 012 965
cert_ridgeSupport_suffix_decode_2 26 010 15 1029 32 043 011 997
cert_ridgeSupport_suffix_decode_2 26 009 15 1061 32 043 010 1029
cert_ridgeSupport_suffix_decode_2 26 008 15 1093 32 043 009 1061
cert_ridgeSupport_suffix_decode_2 26 007 15 1125 32 043 008 1093
cert_ridgeSupport_suffix_decode_2 26 006 15 1157 32 043 007 1125
cert_ridgeSupport_suffix_decode_2 26 005 15 1189 32 043 006 1157
cert_ridgeSupport_suffix_decode_2 26 004 15 1221 32 043 005 1189
cert_ridgeSupport_suffix_decode_2 26 003 15 1253 32 043 004 1221
cert_ridgeSupport_suffix_decode_2 26 002 15 1285 32 043 003 1253
cert_ridgeSupport_suffix_decode_2 26 001 15 1317 32 043 002 1285
cert_ridgeSupport_suffix_decode_2 26 000 15 1349 32 043 001 1317
cert_ridgeSupport_eq_3 26
theorem ridgeTest_large_26 : ridgeTest 26 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport26_eq]
    simp only [ridgeSupport26_suffix_000, ridgeSupport26_suffix_001, ridgeSupport26_suffix_002, ridgeSupport26_suffix_003, ridgeSupport26_suffix_004, ridgeSupport26_suffix_005, ridgeSupport26_suffix_006, ridgeSupport26_suffix_007, ridgeSupport26_suffix_008, ridgeSupport26_suffix_009, ridgeSupport26_suffix_010, ridgeSupport26_suffix_011, ridgeSupport26_suffix_012, ridgeSupport26_suffix_013, ridgeSupport26_suffix_014, ridgeSupport26_suffix_015, ridgeSupport26_suffix_016, ridgeSupport26_suffix_017, ridgeSupport26_suffix_018, ridgeSupport26_suffix_019, ridgeSupport26_suffix_020, ridgeSupport26_suffix_021, ridgeSupport26_suffix_022, ridgeSupport26_suffix_023, ridgeSupport26_suffix_024, ridgeSupport26_suffix_025, ridgeSupport26_suffix_026, ridgeSupport26_suffix_027, ridgeSupport26_suffix_028, ridgeSupport26_suffix_029, ridgeSupport26_suffix_030, ridgeSupport26_suffix_031, ridgeSupport26_suffix_032, ridgeSupport26_suffix_033, ridgeSupport26_suffix_034, ridgeSupport26_suffix_035, ridgeSupport26_suffix_036, ridgeSupport26_suffix_037, ridgeSupport26_suffix_038, ridgeSupport26_suffix_039, ridgeSupport26_suffix_040, ridgeSupport26_suffix_041, ridgeSupport26_suffix_042, ridgeSupport26_suffix_043, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport26_000_mask, ridgeSupport26_001_mask, ridgeSupport26_002_mask, ridgeSupport26_003_mask, ridgeSupport26_004_mask, ridgeSupport26_005_mask, ridgeSupport26_006_mask, ridgeSupport26_007_mask, ridgeSupport26_008_mask, ridgeSupport26_009_mask, ridgeSupport26_010_mask, ridgeSupport26_011_mask, ridgeSupport26_012_mask, ridgeSupport26_013_mask, ridgeSupport26_014_mask, ridgeSupport26_015_mask, ridgeSupport26_016_mask, ridgeSupport26_017_mask, ridgeSupport26_018_mask, ridgeSupport26_019_mask, ridgeSupport26_020_mask, ridgeSupport26_021_mask, ridgeSupport26_022_mask, ridgeSupport26_023_mask, ridgeSupport26_024_mask, ridgeSupport26_025_mask, ridgeSupport26_026_mask, ridgeSupport26_027_mask, ridgeSupport26_028_mask, ridgeSupport26_029_mask, ridgeSupport26_030_mask, ridgeSupport26_031_mask, ridgeSupport26_032_mask, ridgeSupport26_033_mask, ridgeSupport26_034_mask, ridgeSupport26_035_mask, ridgeSupport26_036_mask, ridgeSupport26_037_mask, ridgeSupport26_038_mask, ridgeSupport26_039_mask, ridgeSupport26_040_mask, ridgeSupport26_041_mask, ridgeSupport26_042_mask]
    decide +kernel
  · rw [ridgeSupport26_eq]
    simp only [ridgeSupport26_suffix_000, ridgeSupport26_suffix_001, ridgeSupport26_suffix_002, ridgeSupport26_suffix_003, ridgeSupport26_suffix_004, ridgeSupport26_suffix_005, ridgeSupport26_suffix_006, ridgeSupport26_suffix_007, ridgeSupport26_suffix_008, ridgeSupport26_suffix_009, ridgeSupport26_suffix_010, ridgeSupport26_suffix_011, ridgeSupport26_suffix_012, ridgeSupport26_suffix_013, ridgeSupport26_suffix_014, ridgeSupport26_suffix_015, ridgeSupport26_suffix_016, ridgeSupport26_suffix_017, ridgeSupport26_suffix_018, ridgeSupport26_suffix_019, ridgeSupport26_suffix_020, ridgeSupport26_suffix_021, ridgeSupport26_suffix_022, ridgeSupport26_suffix_023, ridgeSupport26_suffix_024, ridgeSupport26_suffix_025, ridgeSupport26_suffix_026, ridgeSupport26_suffix_027, ridgeSupport26_suffix_028, ridgeSupport26_suffix_029, ridgeSupport26_suffix_030, ridgeSupport26_suffix_031, ridgeSupport26_suffix_032, ridgeSupport26_suffix_033, ridgeSupport26_suffix_034, ridgeSupport26_suffix_035, ridgeSupport26_suffix_036, ridgeSupport26_suffix_037, ridgeSupport26_suffix_038, ridgeSupport26_suffix_039, ridgeSupport26_suffix_040, ridgeSupport26_suffix_041, ridgeSupport26_suffix_042, ridgeSupport26_suffix_043, List.all_append, List.all_nil, ridgeSupport26_000_checked, ridgeSupport26_001_checked, ridgeSupport26_002_checked, ridgeSupport26_003_checked, ridgeSupport26_004_checked, ridgeSupport26_005_checked, ridgeSupport26_006_checked, ridgeSupport26_007_checked, ridgeSupport26_008_checked, ridgeSupport26_009_checked, ridgeSupport26_010_checked, ridgeSupport26_011_checked, ridgeSupport26_012_checked, ridgeSupport26_013_checked, ridgeSupport26_014_checked, ridgeSupport26_015_checked, ridgeSupport26_016_checked, ridgeSupport26_017_checked, ridgeSupport26_018_checked, ridgeSupport26_019_checked, ridgeSupport26_020_checked, ridgeSupport26_021_checked, ridgeSupport26_022_checked, ridgeSupport26_023_checked, ridgeSupport26_024_checked, ridgeSupport26_025_checked, ridgeSupport26_026_checked, ridgeSupport26_027_checked, ridgeSupport26_028_checked, ridgeSupport26_029_checked, ridgeSupport26_030_checked, ridgeSupport26_031_checked, ridgeSupport26_032_checked, ridgeSupport26_033_checked, ridgeSupport26_034_checked, ridgeSupport26_035_checked, ridgeSupport26_036_checked, ridgeSupport26_037_checked, ridgeSupport26_038_checked, ridgeSupport26_039_checked, ridgeSupport26_040_checked, ridgeSupport26_041_checked, ridgeSupport26_042_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase00
