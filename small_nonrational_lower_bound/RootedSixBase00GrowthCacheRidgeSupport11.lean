module
prelude
public meta import LowerSchemas.FiniteRootedSixBase
public import BundledChecks.RootedSixBase00GrowthCacheRidgeSupport11Batch000
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
cert_ridgeSupport_suffix_decode 11 043 15
cert_ridgeSupport_suffix_decode_2 11 042 15 5 5 043 043 0
cert_ridgeSupport_suffix_decode_2 11 041 15 37 32 043 042 5
cert_ridgeSupport_suffix_decode_2 11 040 15 69 32 043 041 37
cert_ridgeSupport_suffix_decode_2 11 039 15 101 32 043 040 69
cert_ridgeSupport_suffix_decode_2 11 038 15 133 32 043 039 101
cert_ridgeSupport_suffix_decode_2 11 037 15 165 32 043 038 133
cert_ridgeSupport_suffix_decode_2 11 036 15 197 32 043 037 165
cert_ridgeSupport_suffix_decode_2 11 035 15 229 32 043 036 197
cert_ridgeSupport_suffix_decode_2 11 034 15 261 32 043 035 229
cert_ridgeSupport_suffix_decode_2 11 033 15 293 32 043 034 261
cert_ridgeSupport_suffix_decode_2 11 032 15 325 32 043 033 293
cert_ridgeSupport_suffix_decode_2 11 031 15 357 32 043 032 325
cert_ridgeSupport_suffix_decode_2 11 030 15 389 32 043 031 357
cert_ridgeSupport_suffix_decode_2 11 029 15 421 32 043 030 389
cert_ridgeSupport_suffix_decode_2 11 028 15 453 32 043 029 421
cert_ridgeSupport_suffix_decode_2 11 027 15 485 32 043 028 453
cert_ridgeSupport_suffix_decode_2 11 026 15 517 32 043 027 485
cert_ridgeSupport_suffix_decode_2 11 025 15 549 32 043 026 517
cert_ridgeSupport_suffix_decode_2 11 024 15 581 32 043 025 549
cert_ridgeSupport_suffix_decode_2 11 023 15 613 32 043 024 581
cert_ridgeSupport_suffix_decode_2 11 022 15 645 32 043 023 613
cert_ridgeSupport_suffix_decode_2 11 021 15 677 32 043 022 645
cert_ridgeSupport_suffix_decode_2 11 020 15 709 32 043 021 677
cert_ridgeSupport_suffix_decode_2 11 019 15 741 32 043 020 709
cert_ridgeSupport_suffix_decode_2 11 018 15 773 32 043 019 741
cert_ridgeSupport_suffix_decode_2 11 017 15 805 32 043 018 773
cert_ridgeSupport_suffix_decode_2 11 016 15 837 32 043 017 805
cert_ridgeSupport_suffix_decode_2 11 015 15 869 32 043 016 837
cert_ridgeSupport_suffix_decode_2 11 014 15 901 32 043 015 869
cert_ridgeSupport_suffix_decode_2 11 013 15 933 32 043 014 901
cert_ridgeSupport_suffix_decode_2 11 012 15 965 32 043 013 933
cert_ridgeSupport_suffix_decode_2 11 011 15 997 32 043 012 965
cert_ridgeSupport_suffix_decode_2 11 010 15 1029 32 043 011 997
cert_ridgeSupport_suffix_decode_2 11 009 15 1061 32 043 010 1029
cert_ridgeSupport_suffix_decode_2 11 008 15 1093 32 043 009 1061
cert_ridgeSupport_suffix_decode_2 11 007 15 1125 32 043 008 1093
cert_ridgeSupport_suffix_decode_2 11 006 15 1157 32 043 007 1125
cert_ridgeSupport_suffix_decode_2 11 005 15 1189 32 043 006 1157
cert_ridgeSupport_suffix_decode_2 11 004 15 1221 32 043 005 1189
cert_ridgeSupport_suffix_decode_2 11 003 15 1253 32 043 004 1221
cert_ridgeSupport_suffix_decode_2 11 002 15 1285 32 043 003 1253
cert_ridgeSupport_suffix_decode_2 11 001 15 1317 32 043 002 1285
cert_ridgeSupport_suffix_decode_2 11 000 15 1349 32 043 001 1317
cert_ridgeSupport_eq_3 11
theorem ridgeTest_large_11 : ridgeTest 11 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport11_eq]
    simp only [ridgeSupport11_suffix_000, ridgeSupport11_suffix_001, ridgeSupport11_suffix_002, ridgeSupport11_suffix_003, ridgeSupport11_suffix_004, ridgeSupport11_suffix_005, ridgeSupport11_suffix_006, ridgeSupport11_suffix_007, ridgeSupport11_suffix_008, ridgeSupport11_suffix_009, ridgeSupport11_suffix_010, ridgeSupport11_suffix_011, ridgeSupport11_suffix_012, ridgeSupport11_suffix_013, ridgeSupport11_suffix_014, ridgeSupport11_suffix_015, ridgeSupport11_suffix_016, ridgeSupport11_suffix_017, ridgeSupport11_suffix_018, ridgeSupport11_suffix_019, ridgeSupport11_suffix_020, ridgeSupport11_suffix_021, ridgeSupport11_suffix_022, ridgeSupport11_suffix_023, ridgeSupport11_suffix_024, ridgeSupport11_suffix_025, ridgeSupport11_suffix_026, ridgeSupport11_suffix_027, ridgeSupport11_suffix_028, ridgeSupport11_suffix_029, ridgeSupport11_suffix_030, ridgeSupport11_suffix_031, ridgeSupport11_suffix_032, ridgeSupport11_suffix_033, ridgeSupport11_suffix_034, ridgeSupport11_suffix_035, ridgeSupport11_suffix_036, ridgeSupport11_suffix_037, ridgeSupport11_suffix_038, ridgeSupport11_suffix_039, ridgeSupport11_suffix_040, ridgeSupport11_suffix_041, ridgeSupport11_suffix_042, ridgeSupport11_suffix_043, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport11_000_mask, ridgeSupport11_001_mask, ridgeSupport11_002_mask, ridgeSupport11_003_mask, ridgeSupport11_004_mask, ridgeSupport11_005_mask, ridgeSupport11_006_mask, ridgeSupport11_007_mask, ridgeSupport11_008_mask, ridgeSupport11_009_mask, ridgeSupport11_010_mask, ridgeSupport11_011_mask, ridgeSupport11_012_mask, ridgeSupport11_013_mask, ridgeSupport11_014_mask, ridgeSupport11_015_mask, ridgeSupport11_016_mask, ridgeSupport11_017_mask, ridgeSupport11_018_mask, ridgeSupport11_019_mask, ridgeSupport11_020_mask, ridgeSupport11_021_mask, ridgeSupport11_022_mask, ridgeSupport11_023_mask, ridgeSupport11_024_mask, ridgeSupport11_025_mask, ridgeSupport11_026_mask, ridgeSupport11_027_mask, ridgeSupport11_028_mask, ridgeSupport11_029_mask, ridgeSupport11_030_mask, ridgeSupport11_031_mask, ridgeSupport11_032_mask, ridgeSupport11_033_mask, ridgeSupport11_034_mask, ridgeSupport11_035_mask, ridgeSupport11_036_mask, ridgeSupport11_037_mask, ridgeSupport11_038_mask, ridgeSupport11_039_mask, ridgeSupport11_040_mask, ridgeSupport11_041_mask, ridgeSupport11_042_mask]
    decide +kernel
  · rw [ridgeSupport11_eq]
    simp only [ridgeSupport11_suffix_000, ridgeSupport11_suffix_001, ridgeSupport11_suffix_002, ridgeSupport11_suffix_003, ridgeSupport11_suffix_004, ridgeSupport11_suffix_005, ridgeSupport11_suffix_006, ridgeSupport11_suffix_007, ridgeSupport11_suffix_008, ridgeSupport11_suffix_009, ridgeSupport11_suffix_010, ridgeSupport11_suffix_011, ridgeSupport11_suffix_012, ridgeSupport11_suffix_013, ridgeSupport11_suffix_014, ridgeSupport11_suffix_015, ridgeSupport11_suffix_016, ridgeSupport11_suffix_017, ridgeSupport11_suffix_018, ridgeSupport11_suffix_019, ridgeSupport11_suffix_020, ridgeSupport11_suffix_021, ridgeSupport11_suffix_022, ridgeSupport11_suffix_023, ridgeSupport11_suffix_024, ridgeSupport11_suffix_025, ridgeSupport11_suffix_026, ridgeSupport11_suffix_027, ridgeSupport11_suffix_028, ridgeSupport11_suffix_029, ridgeSupport11_suffix_030, ridgeSupport11_suffix_031, ridgeSupport11_suffix_032, ridgeSupport11_suffix_033, ridgeSupport11_suffix_034, ridgeSupport11_suffix_035, ridgeSupport11_suffix_036, ridgeSupport11_suffix_037, ridgeSupport11_suffix_038, ridgeSupport11_suffix_039, ridgeSupport11_suffix_040, ridgeSupport11_suffix_041, ridgeSupport11_suffix_042, ridgeSupport11_suffix_043, List.all_append, List.all_nil, ridgeSupport11_000_checked, ridgeSupport11_001_checked, ridgeSupport11_002_checked, ridgeSupport11_003_checked, ridgeSupport11_004_checked, ridgeSupport11_005_checked, ridgeSupport11_006_checked, ridgeSupport11_007_checked, ridgeSupport11_008_checked, ridgeSupport11_009_checked, ridgeSupport11_010_checked, ridgeSupport11_011_checked, ridgeSupport11_012_checked, ridgeSupport11_013_checked, ridgeSupport11_014_checked, ridgeSupport11_015_checked, ridgeSupport11_016_checked, ridgeSupport11_017_checked, ridgeSupport11_018_checked, ridgeSupport11_019_checked, ridgeSupport11_020_checked, ridgeSupport11_021_checked, ridgeSupport11_022_checked, ridgeSupport11_023_checked, ridgeSupport11_024_checked, ridgeSupport11_025_checked, ridgeSupport11_026_checked, ridgeSupport11_027_checked, ridgeSupport11_028_checked, ridgeSupport11_029_checked, ridgeSupport11_030_checked, ridgeSupport11_031_checked, ridgeSupport11_032_checked, ridgeSupport11_033_checked, ridgeSupport11_034_checked, ridgeSupport11_035_checked, ridgeSupport11_036_checked, ridgeSupport11_037_checked, ridgeSupport11_038_checked, ridgeSupport11_039_checked, ridgeSupport11_040_checked, ridgeSupport11_041_checked, ridgeSupport11_042_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase00
