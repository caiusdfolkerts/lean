module
prelude
public meta import LowerSchemas.FiniteRootedSixBase.Part0
public import BundledChecks.RootedSixBase01GrowthCacheRidgeSupport772Batch000
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
cert_ridgeSupport_suffix_decode 772 043 14
cert_ridgeSupport_suffix_decode_2 772 042 14 5 5 043 043 0
cert_ridgeSupport_suffix_decode_2 772 041 14 37 32 043 042 5
cert_ridgeSupport_suffix_decode_2 772 040 14 69 32 043 041 37
cert_ridgeSupport_suffix_decode_2 772 039 14 101 32 043 040 69
cert_ridgeSupport_suffix_decode_2 772 038 14 133 32 043 039 101
cert_ridgeSupport_suffix_decode_2 772 037 14 165 32 043 038 133
cert_ridgeSupport_suffix_decode_2 772 036 14 197 32 043 037 165
cert_ridgeSupport_suffix_decode_2 772 035 14 229 32 043 036 197
cert_ridgeSupport_suffix_decode_2 772 034 14 261 32 043 035 229
cert_ridgeSupport_suffix_decode_2 772 033 14 293 32 043 034 261
cert_ridgeSupport_suffix_decode_2 772 032 14 325 32 043 033 293
cert_ridgeSupport_suffix_decode_2 772 031 14 357 32 043 032 325
cert_ridgeSupport_suffix_decode_2 772 030 14 389 32 043 031 357
cert_ridgeSupport_suffix_decode_2 772 029 14 421 32 043 030 389
cert_ridgeSupport_suffix_decode_2 772 028 14 453 32 043 029 421
cert_ridgeSupport_suffix_decode_2 772 027 14 485 32 043 028 453
cert_ridgeSupport_suffix_decode_2 772 026 14 517 32 043 027 485
cert_ridgeSupport_suffix_decode_2 772 025 14 549 32 043 026 517
cert_ridgeSupport_suffix_decode_2 772 024 14 581 32 043 025 549
cert_ridgeSupport_suffix_decode_2 772 023 14 613 32 043 024 581
cert_ridgeSupport_suffix_decode_2 772 022 14 645 32 043 023 613
cert_ridgeSupport_suffix_decode_2 772 021 14 677 32 043 022 645
cert_ridgeSupport_suffix_decode_2 772 020 14 709 32 043 021 677
cert_ridgeSupport_suffix_decode_2 772 019 14 741 32 043 020 709
cert_ridgeSupport_suffix_decode_2 772 018 14 773 32 043 019 741
cert_ridgeSupport_suffix_decode_2 772 017 14 805 32 043 018 773
cert_ridgeSupport_suffix_decode_2 772 016 14 837 32 043 017 805
cert_ridgeSupport_suffix_decode_2 772 015 14 869 32 043 016 837
cert_ridgeSupport_suffix_decode_2 772 014 14 901 32 043 015 869
cert_ridgeSupport_suffix_decode_2 772 013 14 933 32 043 014 901
cert_ridgeSupport_suffix_decode_2 772 012 14 965 32 043 013 933
cert_ridgeSupport_suffix_decode_2 772 011 14 997 32 043 012 965
cert_ridgeSupport_suffix_decode_2 772 010 14 1029 32 043 011 997
cert_ridgeSupport_suffix_decode_2 772 009 14 1061 32 043 010 1029
cert_ridgeSupport_suffix_decode_2 772 008 14 1093 32 043 009 1061
cert_ridgeSupport_suffix_decode_2 772 007 14 1125 32 043 008 1093
cert_ridgeSupport_suffix_decode_2 772 006 14 1157 32 043 007 1125
cert_ridgeSupport_suffix_decode_2 772 005 14 1189 32 043 006 1157
cert_ridgeSupport_suffix_decode_2 772 004 14 1221 32 043 005 1189
cert_ridgeSupport_suffix_decode_2 772 003 14 1253 32 043 004 1221
cert_ridgeSupport_suffix_decode_2 772 002 14 1285 32 043 003 1253
cert_ridgeSupport_suffix_decode_2 772 001 14 1317 32 043 002 1285
cert_ridgeSupport_suffix_decode_2 772 000 14 1349 32 043 001 1317
cert_ridgeSupport_eq_3 772
theorem ridgeTest_large_772 : ridgeTest 772 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport772_eq]
    simp only [ridgeSupport772_suffix_000, ridgeSupport772_suffix_001, ridgeSupport772_suffix_002, ridgeSupport772_suffix_003, ridgeSupport772_suffix_004, ridgeSupport772_suffix_005, ridgeSupport772_suffix_006, ridgeSupport772_suffix_007, ridgeSupport772_suffix_008, ridgeSupport772_suffix_009, ridgeSupport772_suffix_010, ridgeSupport772_suffix_011, ridgeSupport772_suffix_012, ridgeSupport772_suffix_013, ridgeSupport772_suffix_014, ridgeSupport772_suffix_015, ridgeSupport772_suffix_016, ridgeSupport772_suffix_017, ridgeSupport772_suffix_018, ridgeSupport772_suffix_019, ridgeSupport772_suffix_020, ridgeSupport772_suffix_021, ridgeSupport772_suffix_022, ridgeSupport772_suffix_023, ridgeSupport772_suffix_024, ridgeSupport772_suffix_025, ridgeSupport772_suffix_026, ridgeSupport772_suffix_027, ridgeSupport772_suffix_028, ridgeSupport772_suffix_029, ridgeSupport772_suffix_030, ridgeSupport772_suffix_031, ridgeSupport772_suffix_032, ridgeSupport772_suffix_033, ridgeSupport772_suffix_034, ridgeSupport772_suffix_035, ridgeSupport772_suffix_036, ridgeSupport772_suffix_037, ridgeSupport772_suffix_038, ridgeSupport772_suffix_039, ridgeSupport772_suffix_040, ridgeSupport772_suffix_041, ridgeSupport772_suffix_042, ridgeSupport772_suffix_043, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport772_000_mask, ridgeSupport772_001_mask, ridgeSupport772_002_mask, ridgeSupport772_003_mask, ridgeSupport772_004_mask, ridgeSupport772_005_mask, ridgeSupport772_006_mask, ridgeSupport772_007_mask, ridgeSupport772_008_mask, ridgeSupport772_009_mask, ridgeSupport772_010_mask, ridgeSupport772_011_mask, ridgeSupport772_012_mask, ridgeSupport772_013_mask, ridgeSupport772_014_mask, ridgeSupport772_015_mask, ridgeSupport772_016_mask, ridgeSupport772_017_mask, ridgeSupport772_018_mask, ridgeSupport772_019_mask, ridgeSupport772_020_mask, ridgeSupport772_021_mask, ridgeSupport772_022_mask, ridgeSupport772_023_mask, ridgeSupport772_024_mask, ridgeSupport772_025_mask, ridgeSupport772_026_mask, ridgeSupport772_027_mask, ridgeSupport772_028_mask, ridgeSupport772_029_mask, ridgeSupport772_030_mask, ridgeSupport772_031_mask, ridgeSupport772_032_mask, ridgeSupport772_033_mask, ridgeSupport772_034_mask, ridgeSupport772_035_mask, ridgeSupport772_036_mask, ridgeSupport772_037_mask, ridgeSupport772_038_mask, ridgeSupport772_039_mask, ridgeSupport772_040_mask, ridgeSupport772_041_mask, ridgeSupport772_042_mask]
    decide +kernel
  · rw [ridgeSupport772_eq]
    simp only [ridgeSupport772_suffix_000, ridgeSupport772_suffix_001, ridgeSupport772_suffix_002, ridgeSupport772_suffix_003, ridgeSupport772_suffix_004, ridgeSupport772_suffix_005, ridgeSupport772_suffix_006, ridgeSupport772_suffix_007, ridgeSupport772_suffix_008, ridgeSupport772_suffix_009, ridgeSupport772_suffix_010, ridgeSupport772_suffix_011, ridgeSupport772_suffix_012, ridgeSupport772_suffix_013, ridgeSupport772_suffix_014, ridgeSupport772_suffix_015, ridgeSupport772_suffix_016, ridgeSupport772_suffix_017, ridgeSupport772_suffix_018, ridgeSupport772_suffix_019, ridgeSupport772_suffix_020, ridgeSupport772_suffix_021, ridgeSupport772_suffix_022, ridgeSupport772_suffix_023, ridgeSupport772_suffix_024, ridgeSupport772_suffix_025, ridgeSupport772_suffix_026, ridgeSupport772_suffix_027, ridgeSupport772_suffix_028, ridgeSupport772_suffix_029, ridgeSupport772_suffix_030, ridgeSupport772_suffix_031, ridgeSupport772_suffix_032, ridgeSupport772_suffix_033, ridgeSupport772_suffix_034, ridgeSupport772_suffix_035, ridgeSupport772_suffix_036, ridgeSupport772_suffix_037, ridgeSupport772_suffix_038, ridgeSupport772_suffix_039, ridgeSupport772_suffix_040, ridgeSupport772_suffix_041, ridgeSupport772_suffix_042, ridgeSupport772_suffix_043, List.all_append, List.all_nil, ridgeSupport772_000_checked, ridgeSupport772_001_checked, ridgeSupport772_002_checked, ridgeSupport772_003_checked, ridgeSupport772_004_checked, ridgeSupport772_005_checked, ridgeSupport772_006_checked, ridgeSupport772_007_checked, ridgeSupport772_008_checked, ridgeSupport772_009_checked, ridgeSupport772_010_checked, ridgeSupport772_011_checked, ridgeSupport772_012_checked, ridgeSupport772_013_checked, ridgeSupport772_014_checked, ridgeSupport772_015_checked, ridgeSupport772_016_checked, ridgeSupport772_017_checked, ridgeSupport772_018_checked, ridgeSupport772_019_checked, ridgeSupport772_020_checked, ridgeSupport772_021_checked, ridgeSupport772_022_checked, ridgeSupport772_023_checked, ridgeSupport772_024_checked, ridgeSupport772_025_checked, ridgeSupport772_026_checked, ridgeSupport772_027_checked, ridgeSupport772_028_checked, ridgeSupport772_029_checked, ridgeSupport772_030_checked, ridgeSupport772_031_checked, ridgeSupport772_032_checked, ridgeSupport772_033_checked, ridgeSupport772_034_checked, ridgeSupport772_035_checked, ridgeSupport772_036_checked, ridgeSupport772_037_checked, ridgeSupport772_038_checked, ridgeSupport772_039_checked, ridgeSupport772_040_checked, ridgeSupport772_041_checked, ridgeSupport772_042_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase01
