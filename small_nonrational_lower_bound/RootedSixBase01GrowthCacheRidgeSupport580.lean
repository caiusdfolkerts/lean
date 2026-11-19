module
prelude
public meta import LowerSchemas.FiniteRootedSixBase
public import BundledChecks.RootedSixBase01GrowthCacheRidgeSupport580Batch000
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
cert_ridgeSupport_suffix_decode 580 043 14
cert_ridgeSupport_suffix_decode_2 580 042 14 5 5 043 043 0
cert_ridgeSupport_suffix_decode_2 580 041 14 37 32 043 042 5
cert_ridgeSupport_suffix_decode_2 580 040 14 69 32 043 041 37
cert_ridgeSupport_suffix_decode_2 580 039 14 101 32 043 040 69
cert_ridgeSupport_suffix_decode_2 580 038 14 133 32 043 039 101
cert_ridgeSupport_suffix_decode_2 580 037 14 165 32 043 038 133
cert_ridgeSupport_suffix_decode_2 580 036 14 197 32 043 037 165
cert_ridgeSupport_suffix_decode_2 580 035 14 229 32 043 036 197
cert_ridgeSupport_suffix_decode_2 580 034 14 261 32 043 035 229
cert_ridgeSupport_suffix_decode_2 580 033 14 293 32 043 034 261
cert_ridgeSupport_suffix_decode_2 580 032 14 325 32 043 033 293
cert_ridgeSupport_suffix_decode_2 580 031 14 357 32 043 032 325
cert_ridgeSupport_suffix_decode_2 580 030 14 389 32 043 031 357
cert_ridgeSupport_suffix_decode_2 580 029 14 421 32 043 030 389
cert_ridgeSupport_suffix_decode_2 580 028 14 453 32 043 029 421
cert_ridgeSupport_suffix_decode_2 580 027 14 485 32 043 028 453
cert_ridgeSupport_suffix_decode_2 580 026 14 517 32 043 027 485
cert_ridgeSupport_suffix_decode_2 580 025 14 549 32 043 026 517
cert_ridgeSupport_suffix_decode_2 580 024 14 581 32 043 025 549
cert_ridgeSupport_suffix_decode_2 580 023 14 613 32 043 024 581
cert_ridgeSupport_suffix_decode_2 580 022 14 645 32 043 023 613
cert_ridgeSupport_suffix_decode_2 580 021 14 677 32 043 022 645
cert_ridgeSupport_suffix_decode_2 580 020 14 709 32 043 021 677
cert_ridgeSupport_suffix_decode_2 580 019 14 741 32 043 020 709
cert_ridgeSupport_suffix_decode_2 580 018 14 773 32 043 019 741
cert_ridgeSupport_suffix_decode_2 580 017 14 805 32 043 018 773
cert_ridgeSupport_suffix_decode_2 580 016 14 837 32 043 017 805
cert_ridgeSupport_suffix_decode_2 580 015 14 869 32 043 016 837
cert_ridgeSupport_suffix_decode_2 580 014 14 901 32 043 015 869
cert_ridgeSupport_suffix_decode_2 580 013 14 933 32 043 014 901
cert_ridgeSupport_suffix_decode_2 580 012 14 965 32 043 013 933
cert_ridgeSupport_suffix_decode_2 580 011 14 997 32 043 012 965
cert_ridgeSupport_suffix_decode_2 580 010 14 1029 32 043 011 997
cert_ridgeSupport_suffix_decode_2 580 009 14 1061 32 043 010 1029
cert_ridgeSupport_suffix_decode_2 580 008 14 1093 32 043 009 1061
cert_ridgeSupport_suffix_decode_2 580 007 14 1125 32 043 008 1093
cert_ridgeSupport_suffix_decode_2 580 006 14 1157 32 043 007 1125
cert_ridgeSupport_suffix_decode_2 580 005 14 1189 32 043 006 1157
cert_ridgeSupport_suffix_decode_2 580 004 14 1221 32 043 005 1189
cert_ridgeSupport_suffix_decode_2 580 003 14 1253 32 043 004 1221
cert_ridgeSupport_suffix_decode_2 580 002 14 1285 32 043 003 1253
cert_ridgeSupport_suffix_decode_2 580 001 14 1317 32 043 002 1285
cert_ridgeSupport_suffix_decode_2 580 000 14 1349 32 043 001 1317
cert_ridgeSupport_eq_3 580
theorem ridgeTest_large_580 : ridgeTest 580 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport580_eq]
    simp only [ridgeSupport580_suffix_000, ridgeSupport580_suffix_001, ridgeSupport580_suffix_002, ridgeSupport580_suffix_003, ridgeSupport580_suffix_004, ridgeSupport580_suffix_005, ridgeSupport580_suffix_006, ridgeSupport580_suffix_007, ridgeSupport580_suffix_008, ridgeSupport580_suffix_009, ridgeSupport580_suffix_010, ridgeSupport580_suffix_011, ridgeSupport580_suffix_012, ridgeSupport580_suffix_013, ridgeSupport580_suffix_014, ridgeSupport580_suffix_015, ridgeSupport580_suffix_016, ridgeSupport580_suffix_017, ridgeSupport580_suffix_018, ridgeSupport580_suffix_019, ridgeSupport580_suffix_020, ridgeSupport580_suffix_021, ridgeSupport580_suffix_022, ridgeSupport580_suffix_023, ridgeSupport580_suffix_024, ridgeSupport580_suffix_025, ridgeSupport580_suffix_026, ridgeSupport580_suffix_027, ridgeSupport580_suffix_028, ridgeSupport580_suffix_029, ridgeSupport580_suffix_030, ridgeSupport580_suffix_031, ridgeSupport580_suffix_032, ridgeSupport580_suffix_033, ridgeSupport580_suffix_034, ridgeSupport580_suffix_035, ridgeSupport580_suffix_036, ridgeSupport580_suffix_037, ridgeSupport580_suffix_038, ridgeSupport580_suffix_039, ridgeSupport580_suffix_040, ridgeSupport580_suffix_041, ridgeSupport580_suffix_042, ridgeSupport580_suffix_043, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport580_000_mask, ridgeSupport580_001_mask, ridgeSupport580_002_mask, ridgeSupport580_003_mask, ridgeSupport580_004_mask, ridgeSupport580_005_mask, ridgeSupport580_006_mask, ridgeSupport580_007_mask, ridgeSupport580_008_mask, ridgeSupport580_009_mask, ridgeSupport580_010_mask, ridgeSupport580_011_mask, ridgeSupport580_012_mask, ridgeSupport580_013_mask, ridgeSupport580_014_mask, ridgeSupport580_015_mask, ridgeSupport580_016_mask, ridgeSupport580_017_mask, ridgeSupport580_018_mask, ridgeSupport580_019_mask, ridgeSupport580_020_mask, ridgeSupport580_021_mask, ridgeSupport580_022_mask, ridgeSupport580_023_mask, ridgeSupport580_024_mask, ridgeSupport580_025_mask, ridgeSupport580_026_mask, ridgeSupport580_027_mask, ridgeSupport580_028_mask, ridgeSupport580_029_mask, ridgeSupport580_030_mask, ridgeSupport580_031_mask, ridgeSupport580_032_mask, ridgeSupport580_033_mask, ridgeSupport580_034_mask, ridgeSupport580_035_mask, ridgeSupport580_036_mask, ridgeSupport580_037_mask, ridgeSupport580_038_mask, ridgeSupport580_039_mask, ridgeSupport580_040_mask, ridgeSupport580_041_mask, ridgeSupport580_042_mask]
    decide +kernel
  · rw [ridgeSupport580_eq]
    simp only [ridgeSupport580_suffix_000, ridgeSupport580_suffix_001, ridgeSupport580_suffix_002, ridgeSupport580_suffix_003, ridgeSupport580_suffix_004, ridgeSupport580_suffix_005, ridgeSupport580_suffix_006, ridgeSupport580_suffix_007, ridgeSupport580_suffix_008, ridgeSupport580_suffix_009, ridgeSupport580_suffix_010, ridgeSupport580_suffix_011, ridgeSupport580_suffix_012, ridgeSupport580_suffix_013, ridgeSupport580_suffix_014, ridgeSupport580_suffix_015, ridgeSupport580_suffix_016, ridgeSupport580_suffix_017, ridgeSupport580_suffix_018, ridgeSupport580_suffix_019, ridgeSupport580_suffix_020, ridgeSupport580_suffix_021, ridgeSupport580_suffix_022, ridgeSupport580_suffix_023, ridgeSupport580_suffix_024, ridgeSupport580_suffix_025, ridgeSupport580_suffix_026, ridgeSupport580_suffix_027, ridgeSupport580_suffix_028, ridgeSupport580_suffix_029, ridgeSupport580_suffix_030, ridgeSupport580_suffix_031, ridgeSupport580_suffix_032, ridgeSupport580_suffix_033, ridgeSupport580_suffix_034, ridgeSupport580_suffix_035, ridgeSupport580_suffix_036, ridgeSupport580_suffix_037, ridgeSupport580_suffix_038, ridgeSupport580_suffix_039, ridgeSupport580_suffix_040, ridgeSupport580_suffix_041, ridgeSupport580_suffix_042, ridgeSupport580_suffix_043, List.all_append, List.all_nil, ridgeSupport580_000_checked, ridgeSupport580_001_checked, ridgeSupport580_002_checked, ridgeSupport580_003_checked, ridgeSupport580_004_checked, ridgeSupport580_005_checked, ridgeSupport580_006_checked, ridgeSupport580_007_checked, ridgeSupport580_008_checked, ridgeSupport580_009_checked, ridgeSupport580_010_checked, ridgeSupport580_011_checked, ridgeSupport580_012_checked, ridgeSupport580_013_checked, ridgeSupport580_014_checked, ridgeSupport580_015_checked, ridgeSupport580_016_checked, ridgeSupport580_017_checked, ridgeSupport580_018_checked, ridgeSupport580_019_checked, ridgeSupport580_020_checked, ridgeSupport580_021_checked, ridgeSupport580_022_checked, ridgeSupport580_023_checked, ridgeSupport580_024_checked, ridgeSupport580_025_checked, ridgeSupport580_026_checked, ridgeSupport580_027_checked, ridgeSupport580_028_checked, ridgeSupport580_029_checked, ridgeSupport580_030_checked, ridgeSupport580_031_checked, ridgeSupport580_032_checked, ridgeSupport580_033_checked, ridgeSupport580_034_checked, ridgeSupport580_035_checked, ridgeSupport580_036_checked, ridgeSupport580_037_checked, ridgeSupport580_038_checked, ridgeSupport580_039_checked, ridgeSupport580_040_checked, ridgeSupport580_041_checked, ridgeSupport580_042_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase01
