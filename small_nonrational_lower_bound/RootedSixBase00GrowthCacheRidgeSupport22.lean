module
prelude
public meta import LowerSchemas.FiniteRootedSixBase
public import BundledChecks.RootedSixBase00GrowthCacheRidgeSupport22Batch000
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
cert_ridgeSupport_suffix_decode 22 043 15
cert_ridgeSupport_suffix_decode_2 22 042 15 5 5 043 043 0
cert_ridgeSupport_suffix_decode_2 22 041 15 37 32 043 042 5
cert_ridgeSupport_suffix_decode_2 22 040 15 69 32 043 041 37
cert_ridgeSupport_suffix_decode_2 22 039 15 101 32 043 040 69
cert_ridgeSupport_suffix_decode_2 22 038 15 133 32 043 039 101
cert_ridgeSupport_suffix_decode_2 22 037 15 165 32 043 038 133
cert_ridgeSupport_suffix_decode_2 22 036 15 197 32 043 037 165
cert_ridgeSupport_suffix_decode_2 22 035 15 229 32 043 036 197
cert_ridgeSupport_suffix_decode_2 22 034 15 261 32 043 035 229
cert_ridgeSupport_suffix_decode_2 22 033 15 293 32 043 034 261
cert_ridgeSupport_suffix_decode_2 22 032 15 325 32 043 033 293
cert_ridgeSupport_suffix_decode_2 22 031 15 357 32 043 032 325
cert_ridgeSupport_suffix_decode_2 22 030 15 389 32 043 031 357
cert_ridgeSupport_suffix_decode_2 22 029 15 421 32 043 030 389
cert_ridgeSupport_suffix_decode_2 22 028 15 453 32 043 029 421
cert_ridgeSupport_suffix_decode_2 22 027 15 485 32 043 028 453
cert_ridgeSupport_suffix_decode_2 22 026 15 517 32 043 027 485
cert_ridgeSupport_suffix_decode_2 22 025 15 549 32 043 026 517
cert_ridgeSupport_suffix_decode_2 22 024 15 581 32 043 025 549
cert_ridgeSupport_suffix_decode_2 22 023 15 613 32 043 024 581
cert_ridgeSupport_suffix_decode_2 22 022 15 645 32 043 023 613
cert_ridgeSupport_suffix_decode_2 22 021 15 677 32 043 022 645
cert_ridgeSupport_suffix_decode_2 22 020 15 709 32 043 021 677
cert_ridgeSupport_suffix_decode_2 22 019 15 741 32 043 020 709
cert_ridgeSupport_suffix_decode_2 22 018 15 773 32 043 019 741
cert_ridgeSupport_suffix_decode_2 22 017 15 805 32 043 018 773
cert_ridgeSupport_suffix_decode_2 22 016 15 837 32 043 017 805
cert_ridgeSupport_suffix_decode_2 22 015 15 869 32 043 016 837
cert_ridgeSupport_suffix_decode_2 22 014 15 901 32 043 015 869
cert_ridgeSupport_suffix_decode_2 22 013 15 933 32 043 014 901
cert_ridgeSupport_suffix_decode_2 22 012 15 965 32 043 013 933
cert_ridgeSupport_suffix_decode_2 22 011 15 997 32 043 012 965
cert_ridgeSupport_suffix_decode_2 22 010 15 1029 32 043 011 997
cert_ridgeSupport_suffix_decode_2 22 009 15 1061 32 043 010 1029
cert_ridgeSupport_suffix_decode_2 22 008 15 1093 32 043 009 1061
cert_ridgeSupport_suffix_decode_2 22 007 15 1125 32 043 008 1093
cert_ridgeSupport_suffix_decode_2 22 006 15 1157 32 043 007 1125
cert_ridgeSupport_suffix_decode_2 22 005 15 1189 32 043 006 1157
cert_ridgeSupport_suffix_decode_2 22 004 15 1221 32 043 005 1189
cert_ridgeSupport_suffix_decode_2 22 003 15 1253 32 043 004 1221
cert_ridgeSupport_suffix_decode_2 22 002 15 1285 32 043 003 1253
cert_ridgeSupport_suffix_decode_2 22 001 15 1317 32 043 002 1285
cert_ridgeSupport_suffix_decode_2 22 000 15 1349 32 043 001 1317
cert_ridgeSupport_eq_3 22
theorem ridgeTest_large_22 : ridgeTest 22 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport22_eq]
    simp only [ridgeSupport22_suffix_000, ridgeSupport22_suffix_001, ridgeSupport22_suffix_002, ridgeSupport22_suffix_003, ridgeSupport22_suffix_004, ridgeSupport22_suffix_005, ridgeSupport22_suffix_006, ridgeSupport22_suffix_007, ridgeSupport22_suffix_008, ridgeSupport22_suffix_009, ridgeSupport22_suffix_010, ridgeSupport22_suffix_011, ridgeSupport22_suffix_012, ridgeSupport22_suffix_013, ridgeSupport22_suffix_014, ridgeSupport22_suffix_015, ridgeSupport22_suffix_016, ridgeSupport22_suffix_017, ridgeSupport22_suffix_018, ridgeSupport22_suffix_019, ridgeSupport22_suffix_020, ridgeSupport22_suffix_021, ridgeSupport22_suffix_022, ridgeSupport22_suffix_023, ridgeSupport22_suffix_024, ridgeSupport22_suffix_025, ridgeSupport22_suffix_026, ridgeSupport22_suffix_027, ridgeSupport22_suffix_028, ridgeSupport22_suffix_029, ridgeSupport22_suffix_030, ridgeSupport22_suffix_031, ridgeSupport22_suffix_032, ridgeSupport22_suffix_033, ridgeSupport22_suffix_034, ridgeSupport22_suffix_035, ridgeSupport22_suffix_036, ridgeSupport22_suffix_037, ridgeSupport22_suffix_038, ridgeSupport22_suffix_039, ridgeSupport22_suffix_040, ridgeSupport22_suffix_041, ridgeSupport22_suffix_042, ridgeSupport22_suffix_043, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport22_000_mask, ridgeSupport22_001_mask, ridgeSupport22_002_mask, ridgeSupport22_003_mask, ridgeSupport22_004_mask, ridgeSupport22_005_mask, ridgeSupport22_006_mask, ridgeSupport22_007_mask, ridgeSupport22_008_mask, ridgeSupport22_009_mask, ridgeSupport22_010_mask, ridgeSupport22_011_mask, ridgeSupport22_012_mask, ridgeSupport22_013_mask, ridgeSupport22_014_mask, ridgeSupport22_015_mask, ridgeSupport22_016_mask, ridgeSupport22_017_mask, ridgeSupport22_018_mask, ridgeSupport22_019_mask, ridgeSupport22_020_mask, ridgeSupport22_021_mask, ridgeSupport22_022_mask, ridgeSupport22_023_mask, ridgeSupport22_024_mask, ridgeSupport22_025_mask, ridgeSupport22_026_mask, ridgeSupport22_027_mask, ridgeSupport22_028_mask, ridgeSupport22_029_mask, ridgeSupport22_030_mask, ridgeSupport22_031_mask, ridgeSupport22_032_mask, ridgeSupport22_033_mask, ridgeSupport22_034_mask, ridgeSupport22_035_mask, ridgeSupport22_036_mask, ridgeSupport22_037_mask, ridgeSupport22_038_mask, ridgeSupport22_039_mask, ridgeSupport22_040_mask, ridgeSupport22_041_mask, ridgeSupport22_042_mask]
    decide +kernel
  · rw [ridgeSupport22_eq]
    simp only [ridgeSupport22_suffix_000, ridgeSupport22_suffix_001, ridgeSupport22_suffix_002, ridgeSupport22_suffix_003, ridgeSupport22_suffix_004, ridgeSupport22_suffix_005, ridgeSupport22_suffix_006, ridgeSupport22_suffix_007, ridgeSupport22_suffix_008, ridgeSupport22_suffix_009, ridgeSupport22_suffix_010, ridgeSupport22_suffix_011, ridgeSupport22_suffix_012, ridgeSupport22_suffix_013, ridgeSupport22_suffix_014, ridgeSupport22_suffix_015, ridgeSupport22_suffix_016, ridgeSupport22_suffix_017, ridgeSupport22_suffix_018, ridgeSupport22_suffix_019, ridgeSupport22_suffix_020, ridgeSupport22_suffix_021, ridgeSupport22_suffix_022, ridgeSupport22_suffix_023, ridgeSupport22_suffix_024, ridgeSupport22_suffix_025, ridgeSupport22_suffix_026, ridgeSupport22_suffix_027, ridgeSupport22_suffix_028, ridgeSupport22_suffix_029, ridgeSupport22_suffix_030, ridgeSupport22_suffix_031, ridgeSupport22_suffix_032, ridgeSupport22_suffix_033, ridgeSupport22_suffix_034, ridgeSupport22_suffix_035, ridgeSupport22_suffix_036, ridgeSupport22_suffix_037, ridgeSupport22_suffix_038, ridgeSupport22_suffix_039, ridgeSupport22_suffix_040, ridgeSupport22_suffix_041, ridgeSupport22_suffix_042, ridgeSupport22_suffix_043, List.all_append, List.all_nil, ridgeSupport22_000_checked, ridgeSupport22_001_checked, ridgeSupport22_002_checked, ridgeSupport22_003_checked, ridgeSupport22_004_checked, ridgeSupport22_005_checked, ridgeSupport22_006_checked, ridgeSupport22_007_checked, ridgeSupport22_008_checked, ridgeSupport22_009_checked, ridgeSupport22_010_checked, ridgeSupport22_011_checked, ridgeSupport22_012_checked, ridgeSupport22_013_checked, ridgeSupport22_014_checked, ridgeSupport22_015_checked, ridgeSupport22_016_checked, ridgeSupport22_017_checked, ridgeSupport22_018_checked, ridgeSupport22_019_checked, ridgeSupport22_020_checked, ridgeSupport22_021_checked, ridgeSupport22_022_checked, ridgeSupport22_023_checked, ridgeSupport22_024_checked, ridgeSupport22_025_checked, ridgeSupport22_026_checked, ridgeSupport22_027_checked, ridgeSupport22_028_checked, ridgeSupport22_029_checked, ridgeSupport22_030_checked, ridgeSupport22_031_checked, ridgeSupport22_032_checked, ridgeSupport22_033_checked, ridgeSupport22_034_checked, ridgeSupport22_035_checked, ridgeSupport22_036_checked, ridgeSupport22_037_checked, ridgeSupport22_038_checked, ridgeSupport22_039_checked, ridgeSupport22_040_checked, ridgeSupport22_041_checked, ridgeSupport22_042_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase00
