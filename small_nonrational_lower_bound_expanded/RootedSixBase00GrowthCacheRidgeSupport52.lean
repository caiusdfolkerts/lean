module
prelude
public meta import LowerSchemas.FiniteRootedSixBase.Part0
public import BundledChecks.RootedSixBase00GrowthCacheRidgeSupport52Batch000
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
cert_ridgeSupport_suffix_decode 52 043 15
cert_ridgeSupport_suffix_decode_2 52 042 15 5 5 043 043 0
cert_ridgeSupport_suffix_decode_2 52 041 15 37 32 043 042 5
cert_ridgeSupport_suffix_decode_2 52 040 15 69 32 043 041 37
cert_ridgeSupport_suffix_decode_2 52 039 15 101 32 043 040 69
cert_ridgeSupport_suffix_decode_2 52 038 15 133 32 043 039 101
cert_ridgeSupport_suffix_decode_2 52 037 15 165 32 043 038 133
cert_ridgeSupport_suffix_decode_2 52 036 15 197 32 043 037 165
cert_ridgeSupport_suffix_decode_2 52 035 15 229 32 043 036 197
cert_ridgeSupport_suffix_decode_2 52 034 15 261 32 043 035 229
cert_ridgeSupport_suffix_decode_2 52 033 15 293 32 043 034 261
cert_ridgeSupport_suffix_decode_2 52 032 15 325 32 043 033 293
cert_ridgeSupport_suffix_decode_2 52 031 15 357 32 043 032 325
cert_ridgeSupport_suffix_decode_2 52 030 15 389 32 043 031 357
cert_ridgeSupport_suffix_decode_2 52 029 15 421 32 043 030 389
cert_ridgeSupport_suffix_decode_2 52 028 15 453 32 043 029 421
cert_ridgeSupport_suffix_decode_2 52 027 15 485 32 043 028 453
cert_ridgeSupport_suffix_decode_2 52 026 15 517 32 043 027 485
cert_ridgeSupport_suffix_decode_2 52 025 15 549 32 043 026 517
cert_ridgeSupport_suffix_decode_2 52 024 15 581 32 043 025 549
cert_ridgeSupport_suffix_decode_2 52 023 15 613 32 043 024 581
cert_ridgeSupport_suffix_decode_2 52 022 15 645 32 043 023 613
cert_ridgeSupport_suffix_decode_2 52 021 15 677 32 043 022 645
cert_ridgeSupport_suffix_decode_2 52 020 15 709 32 043 021 677
cert_ridgeSupport_suffix_decode_2 52 019 15 741 32 043 020 709
cert_ridgeSupport_suffix_decode_2 52 018 15 773 32 043 019 741
cert_ridgeSupport_suffix_decode_2 52 017 15 805 32 043 018 773
cert_ridgeSupport_suffix_decode_2 52 016 15 837 32 043 017 805
cert_ridgeSupport_suffix_decode_2 52 015 15 869 32 043 016 837
cert_ridgeSupport_suffix_decode_2 52 014 15 901 32 043 015 869
cert_ridgeSupport_suffix_decode_2 52 013 15 933 32 043 014 901
cert_ridgeSupport_suffix_decode_2 52 012 15 965 32 043 013 933
cert_ridgeSupport_suffix_decode_2 52 011 15 997 32 043 012 965
cert_ridgeSupport_suffix_decode_2 52 010 15 1029 32 043 011 997
cert_ridgeSupport_suffix_decode_2 52 009 15 1061 32 043 010 1029
cert_ridgeSupport_suffix_decode_2 52 008 15 1093 32 043 009 1061
cert_ridgeSupport_suffix_decode_2 52 007 15 1125 32 043 008 1093
cert_ridgeSupport_suffix_decode_2 52 006 15 1157 32 043 007 1125
cert_ridgeSupport_suffix_decode_2 52 005 15 1189 32 043 006 1157
cert_ridgeSupport_suffix_decode_2 52 004 15 1221 32 043 005 1189
cert_ridgeSupport_suffix_decode_2 52 003 15 1253 32 043 004 1221
cert_ridgeSupport_suffix_decode_2 52 002 15 1285 32 043 003 1253
cert_ridgeSupport_suffix_decode_2 52 001 15 1317 32 043 002 1285
cert_ridgeSupport_suffix_decode_2 52 000 15 1349 32 043 001 1317
cert_ridgeSupport_eq_3 52
theorem ridgeTest_large_52 : ridgeTest 52 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport52_eq]
    simp only [ridgeSupport52_suffix_000, ridgeSupport52_suffix_001, ridgeSupport52_suffix_002, ridgeSupport52_suffix_003, ridgeSupport52_suffix_004, ridgeSupport52_suffix_005, ridgeSupport52_suffix_006, ridgeSupport52_suffix_007, ridgeSupport52_suffix_008, ridgeSupport52_suffix_009, ridgeSupport52_suffix_010, ridgeSupport52_suffix_011, ridgeSupport52_suffix_012, ridgeSupport52_suffix_013, ridgeSupport52_suffix_014, ridgeSupport52_suffix_015, ridgeSupport52_suffix_016, ridgeSupport52_suffix_017, ridgeSupport52_suffix_018, ridgeSupport52_suffix_019, ridgeSupport52_suffix_020, ridgeSupport52_suffix_021, ridgeSupport52_suffix_022, ridgeSupport52_suffix_023, ridgeSupport52_suffix_024, ridgeSupport52_suffix_025, ridgeSupport52_suffix_026, ridgeSupport52_suffix_027, ridgeSupport52_suffix_028, ridgeSupport52_suffix_029, ridgeSupport52_suffix_030, ridgeSupport52_suffix_031, ridgeSupport52_suffix_032, ridgeSupport52_suffix_033, ridgeSupport52_suffix_034, ridgeSupport52_suffix_035, ridgeSupport52_suffix_036, ridgeSupport52_suffix_037, ridgeSupport52_suffix_038, ridgeSupport52_suffix_039, ridgeSupport52_suffix_040, ridgeSupport52_suffix_041, ridgeSupport52_suffix_042, ridgeSupport52_suffix_043, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport52_000_mask, ridgeSupport52_001_mask, ridgeSupport52_002_mask, ridgeSupport52_003_mask, ridgeSupport52_004_mask, ridgeSupport52_005_mask, ridgeSupport52_006_mask, ridgeSupport52_007_mask, ridgeSupport52_008_mask, ridgeSupport52_009_mask, ridgeSupport52_010_mask, ridgeSupport52_011_mask, ridgeSupport52_012_mask, ridgeSupport52_013_mask, ridgeSupport52_014_mask, ridgeSupport52_015_mask, ridgeSupport52_016_mask, ridgeSupport52_017_mask, ridgeSupport52_018_mask, ridgeSupport52_019_mask, ridgeSupport52_020_mask, ridgeSupport52_021_mask, ridgeSupport52_022_mask, ridgeSupport52_023_mask, ridgeSupport52_024_mask, ridgeSupport52_025_mask, ridgeSupport52_026_mask, ridgeSupport52_027_mask, ridgeSupport52_028_mask, ridgeSupport52_029_mask, ridgeSupport52_030_mask, ridgeSupport52_031_mask, ridgeSupport52_032_mask, ridgeSupport52_033_mask, ridgeSupport52_034_mask, ridgeSupport52_035_mask, ridgeSupport52_036_mask, ridgeSupport52_037_mask, ridgeSupport52_038_mask, ridgeSupport52_039_mask, ridgeSupport52_040_mask, ridgeSupport52_041_mask, ridgeSupport52_042_mask]
    decide +kernel
  · rw [ridgeSupport52_eq]
    simp only [ridgeSupport52_suffix_000, ridgeSupport52_suffix_001, ridgeSupport52_suffix_002, ridgeSupport52_suffix_003, ridgeSupport52_suffix_004, ridgeSupport52_suffix_005, ridgeSupport52_suffix_006, ridgeSupport52_suffix_007, ridgeSupport52_suffix_008, ridgeSupport52_suffix_009, ridgeSupport52_suffix_010, ridgeSupport52_suffix_011, ridgeSupport52_suffix_012, ridgeSupport52_suffix_013, ridgeSupport52_suffix_014, ridgeSupport52_suffix_015, ridgeSupport52_suffix_016, ridgeSupport52_suffix_017, ridgeSupport52_suffix_018, ridgeSupport52_suffix_019, ridgeSupport52_suffix_020, ridgeSupport52_suffix_021, ridgeSupport52_suffix_022, ridgeSupport52_suffix_023, ridgeSupport52_suffix_024, ridgeSupport52_suffix_025, ridgeSupport52_suffix_026, ridgeSupport52_suffix_027, ridgeSupport52_suffix_028, ridgeSupport52_suffix_029, ridgeSupport52_suffix_030, ridgeSupport52_suffix_031, ridgeSupport52_suffix_032, ridgeSupport52_suffix_033, ridgeSupport52_suffix_034, ridgeSupport52_suffix_035, ridgeSupport52_suffix_036, ridgeSupport52_suffix_037, ridgeSupport52_suffix_038, ridgeSupport52_suffix_039, ridgeSupport52_suffix_040, ridgeSupport52_suffix_041, ridgeSupport52_suffix_042, ridgeSupport52_suffix_043, List.all_append, List.all_nil, ridgeSupport52_000_checked, ridgeSupport52_001_checked, ridgeSupport52_002_checked, ridgeSupport52_003_checked, ridgeSupport52_004_checked, ridgeSupport52_005_checked, ridgeSupport52_006_checked, ridgeSupport52_007_checked, ridgeSupport52_008_checked, ridgeSupport52_009_checked, ridgeSupport52_010_checked, ridgeSupport52_011_checked, ridgeSupport52_012_checked, ridgeSupport52_013_checked, ridgeSupport52_014_checked, ridgeSupport52_015_checked, ridgeSupport52_016_checked, ridgeSupport52_017_checked, ridgeSupport52_018_checked, ridgeSupport52_019_checked, ridgeSupport52_020_checked, ridgeSupport52_021_checked, ridgeSupport52_022_checked, ridgeSupport52_023_checked, ridgeSupport52_024_checked, ridgeSupport52_025_checked, ridgeSupport52_026_checked, ridgeSupport52_027_checked, ridgeSupport52_028_checked, ridgeSupport52_029_checked, ridgeSupport52_030_checked, ridgeSupport52_031_checked, ridgeSupport52_032_checked, ridgeSupport52_033_checked, ridgeSupport52_034_checked, ridgeSupport52_035_checked, ridgeSupport52_036_checked, ridgeSupport52_037_checked, ridgeSupport52_038_checked, ridgeSupport52_039_checked, ridgeSupport52_040_checked, ridgeSupport52_041_checked, ridgeSupport52_042_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase00
