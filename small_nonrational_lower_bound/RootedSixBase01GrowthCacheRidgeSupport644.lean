module
prelude
public meta import LowerSchemas.FiniteRootedSixBase
public import BundledChecks.RootedSixBase01GrowthCacheRidgeSupport644Batch000
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
cert_ridgeSupport_suffix_decode 644 043 14
cert_ridgeSupport_suffix_decode_2 644 042 14 5 5 043 043 0
cert_ridgeSupport_suffix_decode_2 644 041 14 37 32 043 042 5
cert_ridgeSupport_suffix_decode_2 644 040 14 69 32 043 041 37
cert_ridgeSupport_suffix_decode_2 644 039 14 101 32 043 040 69
cert_ridgeSupport_suffix_decode_2 644 038 14 133 32 043 039 101
cert_ridgeSupport_suffix_decode_2 644 037 14 165 32 043 038 133
cert_ridgeSupport_suffix_decode_2 644 036 14 197 32 043 037 165
cert_ridgeSupport_suffix_decode_2 644 035 14 229 32 043 036 197
cert_ridgeSupport_suffix_decode_2 644 034 14 261 32 043 035 229
cert_ridgeSupport_suffix_decode_2 644 033 14 293 32 043 034 261
cert_ridgeSupport_suffix_decode_2 644 032 14 325 32 043 033 293
cert_ridgeSupport_suffix_decode_2 644 031 14 357 32 043 032 325
cert_ridgeSupport_suffix_decode_2 644 030 14 389 32 043 031 357
cert_ridgeSupport_suffix_decode_2 644 029 14 421 32 043 030 389
cert_ridgeSupport_suffix_decode_2 644 028 14 453 32 043 029 421
cert_ridgeSupport_suffix_decode_2 644 027 14 485 32 043 028 453
cert_ridgeSupport_suffix_decode_2 644 026 14 517 32 043 027 485
cert_ridgeSupport_suffix_decode_2 644 025 14 549 32 043 026 517
cert_ridgeSupport_suffix_decode_2 644 024 14 581 32 043 025 549
cert_ridgeSupport_suffix_decode_2 644 023 14 613 32 043 024 581
cert_ridgeSupport_suffix_decode_2 644 022 14 645 32 043 023 613
cert_ridgeSupport_suffix_decode_2 644 021 14 677 32 043 022 645
cert_ridgeSupport_suffix_decode_2 644 020 14 709 32 043 021 677
cert_ridgeSupport_suffix_decode_2 644 019 14 741 32 043 020 709
cert_ridgeSupport_suffix_decode_2 644 018 14 773 32 043 019 741
cert_ridgeSupport_suffix_decode_2 644 017 14 805 32 043 018 773
cert_ridgeSupport_suffix_decode_2 644 016 14 837 32 043 017 805
cert_ridgeSupport_suffix_decode_2 644 015 14 869 32 043 016 837
cert_ridgeSupport_suffix_decode_2 644 014 14 901 32 043 015 869
cert_ridgeSupport_suffix_decode_2 644 013 14 933 32 043 014 901
cert_ridgeSupport_suffix_decode_2 644 012 14 965 32 043 013 933
cert_ridgeSupport_suffix_decode_2 644 011 14 997 32 043 012 965
cert_ridgeSupport_suffix_decode_2 644 010 14 1029 32 043 011 997
cert_ridgeSupport_suffix_decode_2 644 009 14 1061 32 043 010 1029
cert_ridgeSupport_suffix_decode_2 644 008 14 1093 32 043 009 1061
cert_ridgeSupport_suffix_decode_2 644 007 14 1125 32 043 008 1093
cert_ridgeSupport_suffix_decode_2 644 006 14 1157 32 043 007 1125
cert_ridgeSupport_suffix_decode_2 644 005 14 1189 32 043 006 1157
cert_ridgeSupport_suffix_decode_2 644 004 14 1221 32 043 005 1189
cert_ridgeSupport_suffix_decode_2 644 003 14 1253 32 043 004 1221
cert_ridgeSupport_suffix_decode_2 644 002 14 1285 32 043 003 1253
cert_ridgeSupport_suffix_decode_2 644 001 14 1317 32 043 002 1285
cert_ridgeSupport_suffix_decode_2 644 000 14 1349 32 043 001 1317
cert_ridgeSupport_eq_3 644
theorem ridgeTest_large_644 : ridgeTest 644 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport644_eq]
    simp only [ridgeSupport644_suffix_000, ridgeSupport644_suffix_001, ridgeSupport644_suffix_002, ridgeSupport644_suffix_003, ridgeSupport644_suffix_004, ridgeSupport644_suffix_005, ridgeSupport644_suffix_006, ridgeSupport644_suffix_007, ridgeSupport644_suffix_008, ridgeSupport644_suffix_009, ridgeSupport644_suffix_010, ridgeSupport644_suffix_011, ridgeSupport644_suffix_012, ridgeSupport644_suffix_013, ridgeSupport644_suffix_014, ridgeSupport644_suffix_015, ridgeSupport644_suffix_016, ridgeSupport644_suffix_017, ridgeSupport644_suffix_018, ridgeSupport644_suffix_019, ridgeSupport644_suffix_020, ridgeSupport644_suffix_021, ridgeSupport644_suffix_022, ridgeSupport644_suffix_023, ridgeSupport644_suffix_024, ridgeSupport644_suffix_025, ridgeSupport644_suffix_026, ridgeSupport644_suffix_027, ridgeSupport644_suffix_028, ridgeSupport644_suffix_029, ridgeSupport644_suffix_030, ridgeSupport644_suffix_031, ridgeSupport644_suffix_032, ridgeSupport644_suffix_033, ridgeSupport644_suffix_034, ridgeSupport644_suffix_035, ridgeSupport644_suffix_036, ridgeSupport644_suffix_037, ridgeSupport644_suffix_038, ridgeSupport644_suffix_039, ridgeSupport644_suffix_040, ridgeSupport644_suffix_041, ridgeSupport644_suffix_042, ridgeSupport644_suffix_043, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport644_000_mask, ridgeSupport644_001_mask, ridgeSupport644_002_mask, ridgeSupport644_003_mask, ridgeSupport644_004_mask, ridgeSupport644_005_mask, ridgeSupport644_006_mask, ridgeSupport644_007_mask, ridgeSupport644_008_mask, ridgeSupport644_009_mask, ridgeSupport644_010_mask, ridgeSupport644_011_mask, ridgeSupport644_012_mask, ridgeSupport644_013_mask, ridgeSupport644_014_mask, ridgeSupport644_015_mask, ridgeSupport644_016_mask, ridgeSupport644_017_mask, ridgeSupport644_018_mask, ridgeSupport644_019_mask, ridgeSupport644_020_mask, ridgeSupport644_021_mask, ridgeSupport644_022_mask, ridgeSupport644_023_mask, ridgeSupport644_024_mask, ridgeSupport644_025_mask, ridgeSupport644_026_mask, ridgeSupport644_027_mask, ridgeSupport644_028_mask, ridgeSupport644_029_mask, ridgeSupport644_030_mask, ridgeSupport644_031_mask, ridgeSupport644_032_mask, ridgeSupport644_033_mask, ridgeSupport644_034_mask, ridgeSupport644_035_mask, ridgeSupport644_036_mask, ridgeSupport644_037_mask, ridgeSupport644_038_mask, ridgeSupport644_039_mask, ridgeSupport644_040_mask, ridgeSupport644_041_mask, ridgeSupport644_042_mask]
    decide +kernel
  · rw [ridgeSupport644_eq]
    simp only [ridgeSupport644_suffix_000, ridgeSupport644_suffix_001, ridgeSupport644_suffix_002, ridgeSupport644_suffix_003, ridgeSupport644_suffix_004, ridgeSupport644_suffix_005, ridgeSupport644_suffix_006, ridgeSupport644_suffix_007, ridgeSupport644_suffix_008, ridgeSupport644_suffix_009, ridgeSupport644_suffix_010, ridgeSupport644_suffix_011, ridgeSupport644_suffix_012, ridgeSupport644_suffix_013, ridgeSupport644_suffix_014, ridgeSupport644_suffix_015, ridgeSupport644_suffix_016, ridgeSupport644_suffix_017, ridgeSupport644_suffix_018, ridgeSupport644_suffix_019, ridgeSupport644_suffix_020, ridgeSupport644_suffix_021, ridgeSupport644_suffix_022, ridgeSupport644_suffix_023, ridgeSupport644_suffix_024, ridgeSupport644_suffix_025, ridgeSupport644_suffix_026, ridgeSupport644_suffix_027, ridgeSupport644_suffix_028, ridgeSupport644_suffix_029, ridgeSupport644_suffix_030, ridgeSupport644_suffix_031, ridgeSupport644_suffix_032, ridgeSupport644_suffix_033, ridgeSupport644_suffix_034, ridgeSupport644_suffix_035, ridgeSupport644_suffix_036, ridgeSupport644_suffix_037, ridgeSupport644_suffix_038, ridgeSupport644_suffix_039, ridgeSupport644_suffix_040, ridgeSupport644_suffix_041, ridgeSupport644_suffix_042, ridgeSupport644_suffix_043, List.all_append, List.all_nil, ridgeSupport644_000_checked, ridgeSupport644_001_checked, ridgeSupport644_002_checked, ridgeSupport644_003_checked, ridgeSupport644_004_checked, ridgeSupport644_005_checked, ridgeSupport644_006_checked, ridgeSupport644_007_checked, ridgeSupport644_008_checked, ridgeSupport644_009_checked, ridgeSupport644_010_checked, ridgeSupport644_011_checked, ridgeSupport644_012_checked, ridgeSupport644_013_checked, ridgeSupport644_014_checked, ridgeSupport644_015_checked, ridgeSupport644_016_checked, ridgeSupport644_017_checked, ridgeSupport644_018_checked, ridgeSupport644_019_checked, ridgeSupport644_020_checked, ridgeSupport644_021_checked, ridgeSupport644_022_checked, ridgeSupport644_023_checked, ridgeSupport644_024_checked, ridgeSupport644_025_checked, ridgeSupport644_026_checked, ridgeSupport644_027_checked, ridgeSupport644_028_checked, ridgeSupport644_029_checked, ridgeSupport644_030_checked, ridgeSupport644_031_checked, ridgeSupport644_032_checked, ridgeSupport644_033_checked, ridgeSupport644_034_checked, ridgeSupport644_035_checked, ridgeSupport644_036_checked, ridgeSupport644_037_checked, ridgeSupport644_038_checked, ridgeSupport644_039_checked, ridgeSupport644_040_checked, ridgeSupport644_041_checked, ridgeSupport644_042_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase01
