module
prelude
public meta import LowerSchemas.FiniteRootedSixBase.Part0
public import BundledChecks.RootedSixBase01GrowthCacheRidgeSupport324Batch000
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
cert_ridgeSupport_suffix_decode 324 043 14
cert_ridgeSupport_suffix_decode_2 324 042 14 5 5 043 043 0
cert_ridgeSupport_suffix_decode_2 324 041 14 37 32 043 042 5
cert_ridgeSupport_suffix_decode_2 324 040 14 69 32 043 041 37
cert_ridgeSupport_suffix_decode_2 324 039 14 101 32 043 040 69
cert_ridgeSupport_suffix_decode_2 324 038 14 133 32 043 039 101
cert_ridgeSupport_suffix_decode_2 324 037 14 165 32 043 038 133
cert_ridgeSupport_suffix_decode_2 324 036 14 197 32 043 037 165
cert_ridgeSupport_suffix_decode_2 324 035 14 229 32 043 036 197
cert_ridgeSupport_suffix_decode_2 324 034 14 261 32 043 035 229
cert_ridgeSupport_suffix_decode_2 324 033 14 293 32 043 034 261
cert_ridgeSupport_suffix_decode_2 324 032 14 325 32 043 033 293
cert_ridgeSupport_suffix_decode_2 324 031 14 357 32 043 032 325
cert_ridgeSupport_suffix_decode_2 324 030 14 389 32 043 031 357
cert_ridgeSupport_suffix_decode_2 324 029 14 421 32 043 030 389
cert_ridgeSupport_suffix_decode_2 324 028 14 453 32 043 029 421
cert_ridgeSupport_suffix_decode_2 324 027 14 485 32 043 028 453
cert_ridgeSupport_suffix_decode_2 324 026 14 517 32 043 027 485
cert_ridgeSupport_suffix_decode_2 324 025 14 549 32 043 026 517
cert_ridgeSupport_suffix_decode_2 324 024 14 581 32 043 025 549
cert_ridgeSupport_suffix_decode_2 324 023 14 613 32 043 024 581
cert_ridgeSupport_suffix_decode_2 324 022 14 645 32 043 023 613
cert_ridgeSupport_suffix_decode_2 324 021 14 677 32 043 022 645
cert_ridgeSupport_suffix_decode_2 324 020 14 709 32 043 021 677
cert_ridgeSupport_suffix_decode_2 324 019 14 741 32 043 020 709
cert_ridgeSupport_suffix_decode_2 324 018 14 773 32 043 019 741
cert_ridgeSupport_suffix_decode_2 324 017 14 805 32 043 018 773
cert_ridgeSupport_suffix_decode_2 324 016 14 837 32 043 017 805
cert_ridgeSupport_suffix_decode_2 324 015 14 869 32 043 016 837
cert_ridgeSupport_suffix_decode_2 324 014 14 901 32 043 015 869
cert_ridgeSupport_suffix_decode_2 324 013 14 933 32 043 014 901
cert_ridgeSupport_suffix_decode_2 324 012 14 965 32 043 013 933
cert_ridgeSupport_suffix_decode_2 324 011 14 997 32 043 012 965
cert_ridgeSupport_suffix_decode_2 324 010 14 1029 32 043 011 997
cert_ridgeSupport_suffix_decode_2 324 009 14 1061 32 043 010 1029
cert_ridgeSupport_suffix_decode_2 324 008 14 1093 32 043 009 1061
cert_ridgeSupport_suffix_decode_2 324 007 14 1125 32 043 008 1093
cert_ridgeSupport_suffix_decode_2 324 006 14 1157 32 043 007 1125
cert_ridgeSupport_suffix_decode_2 324 005 14 1189 32 043 006 1157
cert_ridgeSupport_suffix_decode_2 324 004 14 1221 32 043 005 1189
cert_ridgeSupport_suffix_decode_2 324 003 14 1253 32 043 004 1221
cert_ridgeSupport_suffix_decode_2 324 002 14 1285 32 043 003 1253
cert_ridgeSupport_suffix_decode_2 324 001 14 1317 32 043 002 1285
cert_ridgeSupport_suffix_decode_2 324 000 14 1349 32 043 001 1317
cert_ridgeSupport_eq_3 324
theorem ridgeTest_large_324 : ridgeTest 324 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport324_eq]
    simp only [ridgeSupport324_suffix_000, ridgeSupport324_suffix_001, ridgeSupport324_suffix_002, ridgeSupport324_suffix_003, ridgeSupport324_suffix_004, ridgeSupport324_suffix_005, ridgeSupport324_suffix_006, ridgeSupport324_suffix_007, ridgeSupport324_suffix_008, ridgeSupport324_suffix_009, ridgeSupport324_suffix_010, ridgeSupport324_suffix_011, ridgeSupport324_suffix_012, ridgeSupport324_suffix_013, ridgeSupport324_suffix_014, ridgeSupport324_suffix_015, ridgeSupport324_suffix_016, ridgeSupport324_suffix_017, ridgeSupport324_suffix_018, ridgeSupport324_suffix_019, ridgeSupport324_suffix_020, ridgeSupport324_suffix_021, ridgeSupport324_suffix_022, ridgeSupport324_suffix_023, ridgeSupport324_suffix_024, ridgeSupport324_suffix_025, ridgeSupport324_suffix_026, ridgeSupport324_suffix_027, ridgeSupport324_suffix_028, ridgeSupport324_suffix_029, ridgeSupport324_suffix_030, ridgeSupport324_suffix_031, ridgeSupport324_suffix_032, ridgeSupport324_suffix_033, ridgeSupport324_suffix_034, ridgeSupport324_suffix_035, ridgeSupport324_suffix_036, ridgeSupport324_suffix_037, ridgeSupport324_suffix_038, ridgeSupport324_suffix_039, ridgeSupport324_suffix_040, ridgeSupport324_suffix_041, ridgeSupport324_suffix_042, ridgeSupport324_suffix_043, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport324_000_mask, ridgeSupport324_001_mask, ridgeSupport324_002_mask, ridgeSupport324_003_mask, ridgeSupport324_004_mask, ridgeSupport324_005_mask, ridgeSupport324_006_mask, ridgeSupport324_007_mask, ridgeSupport324_008_mask, ridgeSupport324_009_mask, ridgeSupport324_010_mask, ridgeSupport324_011_mask, ridgeSupport324_012_mask, ridgeSupport324_013_mask, ridgeSupport324_014_mask, ridgeSupport324_015_mask, ridgeSupport324_016_mask, ridgeSupport324_017_mask, ridgeSupport324_018_mask, ridgeSupport324_019_mask, ridgeSupport324_020_mask, ridgeSupport324_021_mask, ridgeSupport324_022_mask, ridgeSupport324_023_mask, ridgeSupport324_024_mask, ridgeSupport324_025_mask, ridgeSupport324_026_mask, ridgeSupport324_027_mask, ridgeSupport324_028_mask, ridgeSupport324_029_mask, ridgeSupport324_030_mask, ridgeSupport324_031_mask, ridgeSupport324_032_mask, ridgeSupport324_033_mask, ridgeSupport324_034_mask, ridgeSupport324_035_mask, ridgeSupport324_036_mask, ridgeSupport324_037_mask, ridgeSupport324_038_mask, ridgeSupport324_039_mask, ridgeSupport324_040_mask, ridgeSupport324_041_mask, ridgeSupport324_042_mask]
    decide +kernel
  · rw [ridgeSupport324_eq]
    simp only [ridgeSupport324_suffix_000, ridgeSupport324_suffix_001, ridgeSupport324_suffix_002, ridgeSupport324_suffix_003, ridgeSupport324_suffix_004, ridgeSupport324_suffix_005, ridgeSupport324_suffix_006, ridgeSupport324_suffix_007, ridgeSupport324_suffix_008, ridgeSupport324_suffix_009, ridgeSupport324_suffix_010, ridgeSupport324_suffix_011, ridgeSupport324_suffix_012, ridgeSupport324_suffix_013, ridgeSupport324_suffix_014, ridgeSupport324_suffix_015, ridgeSupport324_suffix_016, ridgeSupport324_suffix_017, ridgeSupport324_suffix_018, ridgeSupport324_suffix_019, ridgeSupport324_suffix_020, ridgeSupport324_suffix_021, ridgeSupport324_suffix_022, ridgeSupport324_suffix_023, ridgeSupport324_suffix_024, ridgeSupport324_suffix_025, ridgeSupport324_suffix_026, ridgeSupport324_suffix_027, ridgeSupport324_suffix_028, ridgeSupport324_suffix_029, ridgeSupport324_suffix_030, ridgeSupport324_suffix_031, ridgeSupport324_suffix_032, ridgeSupport324_suffix_033, ridgeSupport324_suffix_034, ridgeSupport324_suffix_035, ridgeSupport324_suffix_036, ridgeSupport324_suffix_037, ridgeSupport324_suffix_038, ridgeSupport324_suffix_039, ridgeSupport324_suffix_040, ridgeSupport324_suffix_041, ridgeSupport324_suffix_042, ridgeSupport324_suffix_043, List.all_append, List.all_nil, ridgeSupport324_000_checked, ridgeSupport324_001_checked, ridgeSupport324_002_checked, ridgeSupport324_003_checked, ridgeSupport324_004_checked, ridgeSupport324_005_checked, ridgeSupport324_006_checked, ridgeSupport324_007_checked, ridgeSupport324_008_checked, ridgeSupport324_009_checked, ridgeSupport324_010_checked, ridgeSupport324_011_checked, ridgeSupport324_012_checked, ridgeSupport324_013_checked, ridgeSupport324_014_checked, ridgeSupport324_015_checked, ridgeSupport324_016_checked, ridgeSupport324_017_checked, ridgeSupport324_018_checked, ridgeSupport324_019_checked, ridgeSupport324_020_checked, ridgeSupport324_021_checked, ridgeSupport324_022_checked, ridgeSupport324_023_checked, ridgeSupport324_024_checked, ridgeSupport324_025_checked, ridgeSupport324_026_checked, ridgeSupport324_027_checked, ridgeSupport324_028_checked, ridgeSupport324_029_checked, ridgeSupport324_030_checked, ridgeSupport324_031_checked, ridgeSupport324_032_checked, ridgeSupport324_033_checked, ridgeSupport324_034_checked, ridgeSupport324_035_checked, ridgeSupport324_036_checked, ridgeSupport324_037_checked, ridgeSupport324_038_checked, ridgeSupport324_039_checked, ridgeSupport324_040_checked, ridgeSupport324_041_checked, ridgeSupport324_042_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase01
