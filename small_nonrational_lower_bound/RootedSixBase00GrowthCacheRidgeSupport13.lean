module
prelude
public meta import LowerSchemas.FiniteRootedSixBase
public import BundledChecks.RootedSixBase00GrowthCacheRidgeSupport13Batch000
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
cert_ridgeSupport_suffix_decode 13 043 15
cert_ridgeSupport_suffix_decode_2 13 042 15 5 5 043 043 0
cert_ridgeSupport_suffix_decode_2 13 041 15 37 32 043 042 5
cert_ridgeSupport_suffix_decode_2 13 040 15 69 32 043 041 37
cert_ridgeSupport_suffix_decode_2 13 039 15 101 32 043 040 69
cert_ridgeSupport_suffix_decode_2 13 038 15 133 32 043 039 101
cert_ridgeSupport_suffix_decode_2 13 037 15 165 32 043 038 133
cert_ridgeSupport_suffix_decode_2 13 036 15 197 32 043 037 165
cert_ridgeSupport_suffix_decode_2 13 035 15 229 32 043 036 197
cert_ridgeSupport_suffix_decode_2 13 034 15 261 32 043 035 229
cert_ridgeSupport_suffix_decode_2 13 033 15 293 32 043 034 261
cert_ridgeSupport_suffix_decode_2 13 032 15 325 32 043 033 293
cert_ridgeSupport_suffix_decode_2 13 031 15 357 32 043 032 325
cert_ridgeSupport_suffix_decode_2 13 030 15 389 32 043 031 357
cert_ridgeSupport_suffix_decode_2 13 029 15 421 32 043 030 389
cert_ridgeSupport_suffix_decode_2 13 028 15 453 32 043 029 421
cert_ridgeSupport_suffix_decode_2 13 027 15 485 32 043 028 453
cert_ridgeSupport_suffix_decode_2 13 026 15 517 32 043 027 485
cert_ridgeSupport_suffix_decode_2 13 025 15 549 32 043 026 517
cert_ridgeSupport_suffix_decode_2 13 024 15 581 32 043 025 549
cert_ridgeSupport_suffix_decode_2 13 023 15 613 32 043 024 581
cert_ridgeSupport_suffix_decode_2 13 022 15 645 32 043 023 613
cert_ridgeSupport_suffix_decode_2 13 021 15 677 32 043 022 645
cert_ridgeSupport_suffix_decode_2 13 020 15 709 32 043 021 677
cert_ridgeSupport_suffix_decode_2 13 019 15 741 32 043 020 709
cert_ridgeSupport_suffix_decode_2 13 018 15 773 32 043 019 741
cert_ridgeSupport_suffix_decode_2 13 017 15 805 32 043 018 773
cert_ridgeSupport_suffix_decode_2 13 016 15 837 32 043 017 805
cert_ridgeSupport_suffix_decode_2 13 015 15 869 32 043 016 837
cert_ridgeSupport_suffix_decode_2 13 014 15 901 32 043 015 869
cert_ridgeSupport_suffix_decode_2 13 013 15 933 32 043 014 901
cert_ridgeSupport_suffix_decode_2 13 012 15 965 32 043 013 933
cert_ridgeSupport_suffix_decode_2 13 011 15 997 32 043 012 965
cert_ridgeSupport_suffix_decode_2 13 010 15 1029 32 043 011 997
cert_ridgeSupport_suffix_decode_2 13 009 15 1061 32 043 010 1029
cert_ridgeSupport_suffix_decode_2 13 008 15 1093 32 043 009 1061
cert_ridgeSupport_suffix_decode_2 13 007 15 1125 32 043 008 1093
cert_ridgeSupport_suffix_decode_2 13 006 15 1157 32 043 007 1125
cert_ridgeSupport_suffix_decode_2 13 005 15 1189 32 043 006 1157
cert_ridgeSupport_suffix_decode_2 13 004 15 1221 32 043 005 1189
cert_ridgeSupport_suffix_decode_2 13 003 15 1253 32 043 004 1221
cert_ridgeSupport_suffix_decode_2 13 002 15 1285 32 043 003 1253
cert_ridgeSupport_suffix_decode_2 13 001 15 1317 32 043 002 1285
cert_ridgeSupport_suffix_decode_2 13 000 15 1349 32 043 001 1317
cert_ridgeSupport_eq_3 13
theorem ridgeTest_large_13 : ridgeTest 13 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport13_eq]
    simp only [ridgeSupport13_suffix_000, ridgeSupport13_suffix_001, ridgeSupport13_suffix_002, ridgeSupport13_suffix_003, ridgeSupport13_suffix_004, ridgeSupport13_suffix_005, ridgeSupport13_suffix_006, ridgeSupport13_suffix_007, ridgeSupport13_suffix_008, ridgeSupport13_suffix_009, ridgeSupport13_suffix_010, ridgeSupport13_suffix_011, ridgeSupport13_suffix_012, ridgeSupport13_suffix_013, ridgeSupport13_suffix_014, ridgeSupport13_suffix_015, ridgeSupport13_suffix_016, ridgeSupport13_suffix_017, ridgeSupport13_suffix_018, ridgeSupport13_suffix_019, ridgeSupport13_suffix_020, ridgeSupport13_suffix_021, ridgeSupport13_suffix_022, ridgeSupport13_suffix_023, ridgeSupport13_suffix_024, ridgeSupport13_suffix_025, ridgeSupport13_suffix_026, ridgeSupport13_suffix_027, ridgeSupport13_suffix_028, ridgeSupport13_suffix_029, ridgeSupport13_suffix_030, ridgeSupport13_suffix_031, ridgeSupport13_suffix_032, ridgeSupport13_suffix_033, ridgeSupport13_suffix_034, ridgeSupport13_suffix_035, ridgeSupport13_suffix_036, ridgeSupport13_suffix_037, ridgeSupport13_suffix_038, ridgeSupport13_suffix_039, ridgeSupport13_suffix_040, ridgeSupport13_suffix_041, ridgeSupport13_suffix_042, ridgeSupport13_suffix_043, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport13_000_mask, ridgeSupport13_001_mask, ridgeSupport13_002_mask, ridgeSupport13_003_mask, ridgeSupport13_004_mask, ridgeSupport13_005_mask, ridgeSupport13_006_mask, ridgeSupport13_007_mask, ridgeSupport13_008_mask, ridgeSupport13_009_mask, ridgeSupport13_010_mask, ridgeSupport13_011_mask, ridgeSupport13_012_mask, ridgeSupport13_013_mask, ridgeSupport13_014_mask, ridgeSupport13_015_mask, ridgeSupport13_016_mask, ridgeSupport13_017_mask, ridgeSupport13_018_mask, ridgeSupport13_019_mask, ridgeSupport13_020_mask, ridgeSupport13_021_mask, ridgeSupport13_022_mask, ridgeSupport13_023_mask, ridgeSupport13_024_mask, ridgeSupport13_025_mask, ridgeSupport13_026_mask, ridgeSupport13_027_mask, ridgeSupport13_028_mask, ridgeSupport13_029_mask, ridgeSupport13_030_mask, ridgeSupport13_031_mask, ridgeSupport13_032_mask, ridgeSupport13_033_mask, ridgeSupport13_034_mask, ridgeSupport13_035_mask, ridgeSupport13_036_mask, ridgeSupport13_037_mask, ridgeSupport13_038_mask, ridgeSupport13_039_mask, ridgeSupport13_040_mask, ridgeSupport13_041_mask, ridgeSupport13_042_mask]
    decide +kernel
  · rw [ridgeSupport13_eq]
    simp only [ridgeSupport13_suffix_000, ridgeSupport13_suffix_001, ridgeSupport13_suffix_002, ridgeSupport13_suffix_003, ridgeSupport13_suffix_004, ridgeSupport13_suffix_005, ridgeSupport13_suffix_006, ridgeSupport13_suffix_007, ridgeSupport13_suffix_008, ridgeSupport13_suffix_009, ridgeSupport13_suffix_010, ridgeSupport13_suffix_011, ridgeSupport13_suffix_012, ridgeSupport13_suffix_013, ridgeSupport13_suffix_014, ridgeSupport13_suffix_015, ridgeSupport13_suffix_016, ridgeSupport13_suffix_017, ridgeSupport13_suffix_018, ridgeSupport13_suffix_019, ridgeSupport13_suffix_020, ridgeSupport13_suffix_021, ridgeSupport13_suffix_022, ridgeSupport13_suffix_023, ridgeSupport13_suffix_024, ridgeSupport13_suffix_025, ridgeSupport13_suffix_026, ridgeSupport13_suffix_027, ridgeSupport13_suffix_028, ridgeSupport13_suffix_029, ridgeSupport13_suffix_030, ridgeSupport13_suffix_031, ridgeSupport13_suffix_032, ridgeSupport13_suffix_033, ridgeSupport13_suffix_034, ridgeSupport13_suffix_035, ridgeSupport13_suffix_036, ridgeSupport13_suffix_037, ridgeSupport13_suffix_038, ridgeSupport13_suffix_039, ridgeSupport13_suffix_040, ridgeSupport13_suffix_041, ridgeSupport13_suffix_042, ridgeSupport13_suffix_043, List.all_append, List.all_nil, ridgeSupport13_000_checked, ridgeSupport13_001_checked, ridgeSupport13_002_checked, ridgeSupport13_003_checked, ridgeSupport13_004_checked, ridgeSupport13_005_checked, ridgeSupport13_006_checked, ridgeSupport13_007_checked, ridgeSupport13_008_checked, ridgeSupport13_009_checked, ridgeSupport13_010_checked, ridgeSupport13_011_checked, ridgeSupport13_012_checked, ridgeSupport13_013_checked, ridgeSupport13_014_checked, ridgeSupport13_015_checked, ridgeSupport13_016_checked, ridgeSupport13_017_checked, ridgeSupport13_018_checked, ridgeSupport13_019_checked, ridgeSupport13_020_checked, ridgeSupport13_021_checked, ridgeSupport13_022_checked, ridgeSupport13_023_checked, ridgeSupport13_024_checked, ridgeSupport13_025_checked, ridgeSupport13_026_checked, ridgeSupport13_027_checked, ridgeSupport13_028_checked, ridgeSupport13_029_checked, ridgeSupport13_030_checked, ridgeSupport13_031_checked, ridgeSupport13_032_checked, ridgeSupport13_033_checked, ridgeSupport13_034_checked, ridgeSupport13_035_checked, ridgeSupport13_036_checked, ridgeSupport13_037_checked, ridgeSupport13_038_checked, ridgeSupport13_039_checked, ridgeSupport13_040_checked, ridgeSupport13_041_checked, ridgeSupport13_042_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase00
