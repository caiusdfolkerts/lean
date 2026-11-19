module
prelude
public meta import LowerSchemas.FiniteRootedSixBase
public import BundledChecks.RootedSixBase01GrowthCacheRidgeSupport388Batch000
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
cert_ridgeSupport_suffix_decode 388 043 14
cert_ridgeSupport_suffix_decode_2 388 042 14 5 5 043 043 0
cert_ridgeSupport_suffix_decode_2 388 041 14 37 32 043 042 5
cert_ridgeSupport_suffix_decode_2 388 040 14 69 32 043 041 37
cert_ridgeSupport_suffix_decode_2 388 039 14 101 32 043 040 69
cert_ridgeSupport_suffix_decode_2 388 038 14 133 32 043 039 101
cert_ridgeSupport_suffix_decode_2 388 037 14 165 32 043 038 133
cert_ridgeSupport_suffix_decode_2 388 036 14 197 32 043 037 165
cert_ridgeSupport_suffix_decode_2 388 035 14 229 32 043 036 197
cert_ridgeSupport_suffix_decode_2 388 034 14 261 32 043 035 229
cert_ridgeSupport_suffix_decode_2 388 033 14 293 32 043 034 261
cert_ridgeSupport_suffix_decode_2 388 032 14 325 32 043 033 293
cert_ridgeSupport_suffix_decode_2 388 031 14 357 32 043 032 325
cert_ridgeSupport_suffix_decode_2 388 030 14 389 32 043 031 357
cert_ridgeSupport_suffix_decode_2 388 029 14 421 32 043 030 389
cert_ridgeSupport_suffix_decode_2 388 028 14 453 32 043 029 421
cert_ridgeSupport_suffix_decode_2 388 027 14 485 32 043 028 453
cert_ridgeSupport_suffix_decode_2 388 026 14 517 32 043 027 485
cert_ridgeSupport_suffix_decode_2 388 025 14 549 32 043 026 517
cert_ridgeSupport_suffix_decode_2 388 024 14 581 32 043 025 549
cert_ridgeSupport_suffix_decode_2 388 023 14 613 32 043 024 581
cert_ridgeSupport_suffix_decode_2 388 022 14 645 32 043 023 613
cert_ridgeSupport_suffix_decode_2 388 021 14 677 32 043 022 645
cert_ridgeSupport_suffix_decode_2 388 020 14 709 32 043 021 677
cert_ridgeSupport_suffix_decode_2 388 019 14 741 32 043 020 709
cert_ridgeSupport_suffix_decode_2 388 018 14 773 32 043 019 741
cert_ridgeSupport_suffix_decode_2 388 017 14 805 32 043 018 773
cert_ridgeSupport_suffix_decode_2 388 016 14 837 32 043 017 805
cert_ridgeSupport_suffix_decode_2 388 015 14 869 32 043 016 837
cert_ridgeSupport_suffix_decode_2 388 014 14 901 32 043 015 869
cert_ridgeSupport_suffix_decode_2 388 013 14 933 32 043 014 901
cert_ridgeSupport_suffix_decode_2 388 012 14 965 32 043 013 933
cert_ridgeSupport_suffix_decode_2 388 011 14 997 32 043 012 965
cert_ridgeSupport_suffix_decode_2 388 010 14 1029 32 043 011 997
cert_ridgeSupport_suffix_decode_2 388 009 14 1061 32 043 010 1029
cert_ridgeSupport_suffix_decode_2 388 008 14 1093 32 043 009 1061
cert_ridgeSupport_suffix_decode_2 388 007 14 1125 32 043 008 1093
cert_ridgeSupport_suffix_decode_2 388 006 14 1157 32 043 007 1125
cert_ridgeSupport_suffix_decode_2 388 005 14 1189 32 043 006 1157
cert_ridgeSupport_suffix_decode_2 388 004 14 1221 32 043 005 1189
cert_ridgeSupport_suffix_decode_2 388 003 14 1253 32 043 004 1221
cert_ridgeSupport_suffix_decode_2 388 002 14 1285 32 043 003 1253
cert_ridgeSupport_suffix_decode_2 388 001 14 1317 32 043 002 1285
cert_ridgeSupport_suffix_decode_2 388 000 14 1349 32 043 001 1317
cert_ridgeSupport_eq_3 388
theorem ridgeTest_large_388 : ridgeTest 388 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport388_eq]
    simp only [ridgeSupport388_suffix_000, ridgeSupport388_suffix_001, ridgeSupport388_suffix_002, ridgeSupport388_suffix_003, ridgeSupport388_suffix_004, ridgeSupport388_suffix_005, ridgeSupport388_suffix_006, ridgeSupport388_suffix_007, ridgeSupport388_suffix_008, ridgeSupport388_suffix_009, ridgeSupport388_suffix_010, ridgeSupport388_suffix_011, ridgeSupport388_suffix_012, ridgeSupport388_suffix_013, ridgeSupport388_suffix_014, ridgeSupport388_suffix_015, ridgeSupport388_suffix_016, ridgeSupport388_suffix_017, ridgeSupport388_suffix_018, ridgeSupport388_suffix_019, ridgeSupport388_suffix_020, ridgeSupport388_suffix_021, ridgeSupport388_suffix_022, ridgeSupport388_suffix_023, ridgeSupport388_suffix_024, ridgeSupport388_suffix_025, ridgeSupport388_suffix_026, ridgeSupport388_suffix_027, ridgeSupport388_suffix_028, ridgeSupport388_suffix_029, ridgeSupport388_suffix_030, ridgeSupport388_suffix_031, ridgeSupport388_suffix_032, ridgeSupport388_suffix_033, ridgeSupport388_suffix_034, ridgeSupport388_suffix_035, ridgeSupport388_suffix_036, ridgeSupport388_suffix_037, ridgeSupport388_suffix_038, ridgeSupport388_suffix_039, ridgeSupport388_suffix_040, ridgeSupport388_suffix_041, ridgeSupport388_suffix_042, ridgeSupport388_suffix_043, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport388_000_mask, ridgeSupport388_001_mask, ridgeSupport388_002_mask, ridgeSupport388_003_mask, ridgeSupport388_004_mask, ridgeSupport388_005_mask, ridgeSupport388_006_mask, ridgeSupport388_007_mask, ridgeSupport388_008_mask, ridgeSupport388_009_mask, ridgeSupport388_010_mask, ridgeSupport388_011_mask, ridgeSupport388_012_mask, ridgeSupport388_013_mask, ridgeSupport388_014_mask, ridgeSupport388_015_mask, ridgeSupport388_016_mask, ridgeSupport388_017_mask, ridgeSupport388_018_mask, ridgeSupport388_019_mask, ridgeSupport388_020_mask, ridgeSupport388_021_mask, ridgeSupport388_022_mask, ridgeSupport388_023_mask, ridgeSupport388_024_mask, ridgeSupport388_025_mask, ridgeSupport388_026_mask, ridgeSupport388_027_mask, ridgeSupport388_028_mask, ridgeSupport388_029_mask, ridgeSupport388_030_mask, ridgeSupport388_031_mask, ridgeSupport388_032_mask, ridgeSupport388_033_mask, ridgeSupport388_034_mask, ridgeSupport388_035_mask, ridgeSupport388_036_mask, ridgeSupport388_037_mask, ridgeSupport388_038_mask, ridgeSupport388_039_mask, ridgeSupport388_040_mask, ridgeSupport388_041_mask, ridgeSupport388_042_mask]
    decide +kernel
  · rw [ridgeSupport388_eq]
    simp only [ridgeSupport388_suffix_000, ridgeSupport388_suffix_001, ridgeSupport388_suffix_002, ridgeSupport388_suffix_003, ridgeSupport388_suffix_004, ridgeSupport388_suffix_005, ridgeSupport388_suffix_006, ridgeSupport388_suffix_007, ridgeSupport388_suffix_008, ridgeSupport388_suffix_009, ridgeSupport388_suffix_010, ridgeSupport388_suffix_011, ridgeSupport388_suffix_012, ridgeSupport388_suffix_013, ridgeSupport388_suffix_014, ridgeSupport388_suffix_015, ridgeSupport388_suffix_016, ridgeSupport388_suffix_017, ridgeSupport388_suffix_018, ridgeSupport388_suffix_019, ridgeSupport388_suffix_020, ridgeSupport388_suffix_021, ridgeSupport388_suffix_022, ridgeSupport388_suffix_023, ridgeSupport388_suffix_024, ridgeSupport388_suffix_025, ridgeSupport388_suffix_026, ridgeSupport388_suffix_027, ridgeSupport388_suffix_028, ridgeSupport388_suffix_029, ridgeSupport388_suffix_030, ridgeSupport388_suffix_031, ridgeSupport388_suffix_032, ridgeSupport388_suffix_033, ridgeSupport388_suffix_034, ridgeSupport388_suffix_035, ridgeSupport388_suffix_036, ridgeSupport388_suffix_037, ridgeSupport388_suffix_038, ridgeSupport388_suffix_039, ridgeSupport388_suffix_040, ridgeSupport388_suffix_041, ridgeSupport388_suffix_042, ridgeSupport388_suffix_043, List.all_append, List.all_nil, ridgeSupport388_000_checked, ridgeSupport388_001_checked, ridgeSupport388_002_checked, ridgeSupport388_003_checked, ridgeSupport388_004_checked, ridgeSupport388_005_checked, ridgeSupport388_006_checked, ridgeSupport388_007_checked, ridgeSupport388_008_checked, ridgeSupport388_009_checked, ridgeSupport388_010_checked, ridgeSupport388_011_checked, ridgeSupport388_012_checked, ridgeSupport388_013_checked, ridgeSupport388_014_checked, ridgeSupport388_015_checked, ridgeSupport388_016_checked, ridgeSupport388_017_checked, ridgeSupport388_018_checked, ridgeSupport388_019_checked, ridgeSupport388_020_checked, ridgeSupport388_021_checked, ridgeSupport388_022_checked, ridgeSupport388_023_checked, ridgeSupport388_024_checked, ridgeSupport388_025_checked, ridgeSupport388_026_checked, ridgeSupport388_027_checked, ridgeSupport388_028_checked, ridgeSupport388_029_checked, ridgeSupport388_030_checked, ridgeSupport388_031_checked, ridgeSupport388_032_checked, ridgeSupport388_033_checked, ridgeSupport388_034_checked, ridgeSupport388_035_checked, ridgeSupport388_036_checked, ridgeSupport388_037_checked, ridgeSupport388_038_checked, ridgeSupport388_039_checked, ridgeSupport388_040_checked, ridgeSupport388_041_checked, ridgeSupport388_042_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase01
