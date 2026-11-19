module
prelude
public meta import LowerSchemas.FiniteRootedSixBase.Part0
public import BundledChecks.RootedSixBase00GrowthCacheRidgeSupport7Batch000
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
cert_ridgeSupport_suffix_decode 7 043 15
cert_ridgeSupport_suffix_decode_2 7 042 15 5 5 043 043 0
cert_ridgeSupport_suffix_decode_2 7 041 15 37 32 043 042 5
cert_ridgeSupport_suffix_decode_2 7 040 15 69 32 043 041 37
cert_ridgeSupport_suffix_decode_2 7 039 15 101 32 043 040 69
cert_ridgeSupport_suffix_decode_2 7 038 15 133 32 043 039 101
cert_ridgeSupport_suffix_decode_2 7 037 15 165 32 043 038 133
cert_ridgeSupport_suffix_decode_2 7 036 15 197 32 043 037 165
cert_ridgeSupport_suffix_decode_2 7 035 15 229 32 043 036 197
cert_ridgeSupport_suffix_decode_2 7 034 15 261 32 043 035 229
cert_ridgeSupport_suffix_decode_2 7 033 15 293 32 043 034 261
cert_ridgeSupport_suffix_decode_2 7 032 15 325 32 043 033 293
cert_ridgeSupport_suffix_decode_2 7 031 15 357 32 043 032 325
cert_ridgeSupport_suffix_decode_2 7 030 15 389 32 043 031 357
cert_ridgeSupport_suffix_decode_2 7 029 15 421 32 043 030 389
cert_ridgeSupport_suffix_decode_2 7 028 15 453 32 043 029 421
cert_ridgeSupport_suffix_decode_2 7 027 15 485 32 043 028 453
cert_ridgeSupport_suffix_decode_2 7 026 15 517 32 043 027 485
cert_ridgeSupport_suffix_decode_2 7 025 15 549 32 043 026 517
cert_ridgeSupport_suffix_decode_2 7 024 15 581 32 043 025 549
cert_ridgeSupport_suffix_decode_2 7 023 15 613 32 043 024 581
cert_ridgeSupport_suffix_decode_2 7 022 15 645 32 043 023 613
cert_ridgeSupport_suffix_decode_2 7 021 15 677 32 043 022 645
cert_ridgeSupport_suffix_decode_2 7 020 15 709 32 043 021 677
cert_ridgeSupport_suffix_decode_2 7 019 15 741 32 043 020 709
cert_ridgeSupport_suffix_decode_2 7 018 15 773 32 043 019 741
cert_ridgeSupport_suffix_decode_2 7 017 15 805 32 043 018 773
cert_ridgeSupport_suffix_decode_2 7 016 15 837 32 043 017 805
cert_ridgeSupport_suffix_decode_2 7 015 15 869 32 043 016 837
cert_ridgeSupport_suffix_decode_2 7 014 15 901 32 043 015 869
cert_ridgeSupport_suffix_decode_2 7 013 15 933 32 043 014 901
cert_ridgeSupport_suffix_decode_2 7 012 15 965 32 043 013 933
cert_ridgeSupport_suffix_decode_2 7 011 15 997 32 043 012 965
cert_ridgeSupport_suffix_decode_2 7 010 15 1029 32 043 011 997
cert_ridgeSupport_suffix_decode_2 7 009 15 1061 32 043 010 1029
cert_ridgeSupport_suffix_decode_2 7 008 15 1093 32 043 009 1061
cert_ridgeSupport_suffix_decode_2 7 007 15 1125 32 043 008 1093
cert_ridgeSupport_suffix_decode_2 7 006 15 1157 32 043 007 1125
cert_ridgeSupport_suffix_decode_2 7 005 15 1189 32 043 006 1157
cert_ridgeSupport_suffix_decode_2 7 004 15 1221 32 043 005 1189
cert_ridgeSupport_suffix_decode_2 7 003 15 1253 32 043 004 1221
cert_ridgeSupport_suffix_decode_2 7 002 15 1285 32 043 003 1253
cert_ridgeSupport_suffix_decode_2 7 001 15 1317 32 043 002 1285
cert_ridgeSupport_suffix_decode_2 7 000 15 1349 32 043 001 1317
cert_ridgeSupport_eq_3 7
theorem ridgeTest_large_7 : ridgeTest 7 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport7_eq]
    simp only [ridgeSupport7_suffix_000, ridgeSupport7_suffix_001, ridgeSupport7_suffix_002, ridgeSupport7_suffix_003, ridgeSupport7_suffix_004, ridgeSupport7_suffix_005, ridgeSupport7_suffix_006, ridgeSupport7_suffix_007, ridgeSupport7_suffix_008, ridgeSupport7_suffix_009, ridgeSupport7_suffix_010, ridgeSupport7_suffix_011, ridgeSupport7_suffix_012, ridgeSupport7_suffix_013, ridgeSupport7_suffix_014, ridgeSupport7_suffix_015, ridgeSupport7_suffix_016, ridgeSupport7_suffix_017, ridgeSupport7_suffix_018, ridgeSupport7_suffix_019, ridgeSupport7_suffix_020, ridgeSupport7_suffix_021, ridgeSupport7_suffix_022, ridgeSupport7_suffix_023, ridgeSupport7_suffix_024, ridgeSupport7_suffix_025, ridgeSupport7_suffix_026, ridgeSupport7_suffix_027, ridgeSupport7_suffix_028, ridgeSupport7_suffix_029, ridgeSupport7_suffix_030, ridgeSupport7_suffix_031, ridgeSupport7_suffix_032, ridgeSupport7_suffix_033, ridgeSupport7_suffix_034, ridgeSupport7_suffix_035, ridgeSupport7_suffix_036, ridgeSupport7_suffix_037, ridgeSupport7_suffix_038, ridgeSupport7_suffix_039, ridgeSupport7_suffix_040, ridgeSupport7_suffix_041, ridgeSupport7_suffix_042, ridgeSupport7_suffix_043, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport7_000_mask, ridgeSupport7_001_mask, ridgeSupport7_002_mask, ridgeSupport7_003_mask, ridgeSupport7_004_mask, ridgeSupport7_005_mask, ridgeSupport7_006_mask, ridgeSupport7_007_mask, ridgeSupport7_008_mask, ridgeSupport7_009_mask, ridgeSupport7_010_mask, ridgeSupport7_011_mask, ridgeSupport7_012_mask, ridgeSupport7_013_mask, ridgeSupport7_014_mask, ridgeSupport7_015_mask, ridgeSupport7_016_mask, ridgeSupport7_017_mask, ridgeSupport7_018_mask, ridgeSupport7_019_mask, ridgeSupport7_020_mask, ridgeSupport7_021_mask, ridgeSupport7_022_mask, ridgeSupport7_023_mask, ridgeSupport7_024_mask, ridgeSupport7_025_mask, ridgeSupport7_026_mask, ridgeSupport7_027_mask, ridgeSupport7_028_mask, ridgeSupport7_029_mask, ridgeSupport7_030_mask, ridgeSupport7_031_mask, ridgeSupport7_032_mask, ridgeSupport7_033_mask, ridgeSupport7_034_mask, ridgeSupport7_035_mask, ridgeSupport7_036_mask, ridgeSupport7_037_mask, ridgeSupport7_038_mask, ridgeSupport7_039_mask, ridgeSupport7_040_mask, ridgeSupport7_041_mask, ridgeSupport7_042_mask]
    decide +kernel
  · rw [ridgeSupport7_eq]
    simp only [ridgeSupport7_suffix_000, ridgeSupport7_suffix_001, ridgeSupport7_suffix_002, ridgeSupport7_suffix_003, ridgeSupport7_suffix_004, ridgeSupport7_suffix_005, ridgeSupport7_suffix_006, ridgeSupport7_suffix_007, ridgeSupport7_suffix_008, ridgeSupport7_suffix_009, ridgeSupport7_suffix_010, ridgeSupport7_suffix_011, ridgeSupport7_suffix_012, ridgeSupport7_suffix_013, ridgeSupport7_suffix_014, ridgeSupport7_suffix_015, ridgeSupport7_suffix_016, ridgeSupport7_suffix_017, ridgeSupport7_suffix_018, ridgeSupport7_suffix_019, ridgeSupport7_suffix_020, ridgeSupport7_suffix_021, ridgeSupport7_suffix_022, ridgeSupport7_suffix_023, ridgeSupport7_suffix_024, ridgeSupport7_suffix_025, ridgeSupport7_suffix_026, ridgeSupport7_suffix_027, ridgeSupport7_suffix_028, ridgeSupport7_suffix_029, ridgeSupport7_suffix_030, ridgeSupport7_suffix_031, ridgeSupport7_suffix_032, ridgeSupport7_suffix_033, ridgeSupport7_suffix_034, ridgeSupport7_suffix_035, ridgeSupport7_suffix_036, ridgeSupport7_suffix_037, ridgeSupport7_suffix_038, ridgeSupport7_suffix_039, ridgeSupport7_suffix_040, ridgeSupport7_suffix_041, ridgeSupport7_suffix_042, ridgeSupport7_suffix_043, List.all_append, List.all_nil, ridgeSupport7_000_checked, ridgeSupport7_001_checked, ridgeSupport7_002_checked, ridgeSupport7_003_checked, ridgeSupport7_004_checked, ridgeSupport7_005_checked, ridgeSupport7_006_checked, ridgeSupport7_007_checked, ridgeSupport7_008_checked, ridgeSupport7_009_checked, ridgeSupport7_010_checked, ridgeSupport7_011_checked, ridgeSupport7_012_checked, ridgeSupport7_013_checked, ridgeSupport7_014_checked, ridgeSupport7_015_checked, ridgeSupport7_016_checked, ridgeSupport7_017_checked, ridgeSupport7_018_checked, ridgeSupport7_019_checked, ridgeSupport7_020_checked, ridgeSupport7_021_checked, ridgeSupport7_022_checked, ridgeSupport7_023_checked, ridgeSupport7_024_checked, ridgeSupport7_025_checked, ridgeSupport7_026_checked, ridgeSupport7_027_checked, ridgeSupport7_028_checked, ridgeSupport7_029_checked, ridgeSupport7_030_checked, ridgeSupport7_031_checked, ridgeSupport7_032_checked, ridgeSupport7_033_checked, ridgeSupport7_034_checked, ridgeSupport7_035_checked, ridgeSupport7_036_checked, ridgeSupport7_037_checked, ridgeSupport7_038_checked, ridgeSupport7_039_checked, ridgeSupport7_040_checked, ridgeSupport7_041_checked, ridgeSupport7_042_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase00
