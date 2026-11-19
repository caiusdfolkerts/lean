module
prelude
public meta import LowerSchemas.FiniteRootedSixBase.Part0
public import BundledChecks.RootedSixBase01GrowthCacheRidgeSupport196Batch000
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
cert_ridgeSupport_suffix_decode 196 043 14
cert_ridgeSupport_suffix_decode_2 196 042 14 5 5 043 043 0
cert_ridgeSupport_suffix_decode_2 196 041 14 37 32 043 042 5
cert_ridgeSupport_suffix_decode_2 196 040 14 69 32 043 041 37
cert_ridgeSupport_suffix_decode_2 196 039 14 101 32 043 040 69
cert_ridgeSupport_suffix_decode_2 196 038 14 133 32 043 039 101
cert_ridgeSupport_suffix_decode_2 196 037 14 165 32 043 038 133
cert_ridgeSupport_suffix_decode_2 196 036 14 197 32 043 037 165
cert_ridgeSupport_suffix_decode_2 196 035 14 229 32 043 036 197
cert_ridgeSupport_suffix_decode_2 196 034 14 261 32 043 035 229
cert_ridgeSupport_suffix_decode_2 196 033 14 293 32 043 034 261
cert_ridgeSupport_suffix_decode_2 196 032 14 325 32 043 033 293
cert_ridgeSupport_suffix_decode_2 196 031 14 357 32 043 032 325
cert_ridgeSupport_suffix_decode_2 196 030 14 389 32 043 031 357
cert_ridgeSupport_suffix_decode_2 196 029 14 421 32 043 030 389
cert_ridgeSupport_suffix_decode_2 196 028 14 453 32 043 029 421
cert_ridgeSupport_suffix_decode_2 196 027 14 485 32 043 028 453
cert_ridgeSupport_suffix_decode_2 196 026 14 517 32 043 027 485
cert_ridgeSupport_suffix_decode_2 196 025 14 549 32 043 026 517
cert_ridgeSupport_suffix_decode_2 196 024 14 581 32 043 025 549
cert_ridgeSupport_suffix_decode_2 196 023 14 613 32 043 024 581
cert_ridgeSupport_suffix_decode_2 196 022 14 645 32 043 023 613
cert_ridgeSupport_suffix_decode_2 196 021 14 677 32 043 022 645
cert_ridgeSupport_suffix_decode_2 196 020 14 709 32 043 021 677
cert_ridgeSupport_suffix_decode_2 196 019 14 741 32 043 020 709
cert_ridgeSupport_suffix_decode_2 196 018 14 773 32 043 019 741
cert_ridgeSupport_suffix_decode_2 196 017 14 805 32 043 018 773
cert_ridgeSupport_suffix_decode_2 196 016 14 837 32 043 017 805
cert_ridgeSupport_suffix_decode_2 196 015 14 869 32 043 016 837
cert_ridgeSupport_suffix_decode_2 196 014 14 901 32 043 015 869
cert_ridgeSupport_suffix_decode_2 196 013 14 933 32 043 014 901
cert_ridgeSupport_suffix_decode_2 196 012 14 965 32 043 013 933
cert_ridgeSupport_suffix_decode_2 196 011 14 997 32 043 012 965
cert_ridgeSupport_suffix_decode_2 196 010 14 1029 32 043 011 997
cert_ridgeSupport_suffix_decode_2 196 009 14 1061 32 043 010 1029
cert_ridgeSupport_suffix_decode_2 196 008 14 1093 32 043 009 1061
cert_ridgeSupport_suffix_decode_2 196 007 14 1125 32 043 008 1093
cert_ridgeSupport_suffix_decode_2 196 006 14 1157 32 043 007 1125
cert_ridgeSupport_suffix_decode_2 196 005 14 1189 32 043 006 1157
cert_ridgeSupport_suffix_decode_2 196 004 14 1221 32 043 005 1189
cert_ridgeSupport_suffix_decode_2 196 003 14 1253 32 043 004 1221
cert_ridgeSupport_suffix_decode_2 196 002 14 1285 32 043 003 1253
cert_ridgeSupport_suffix_decode_2 196 001 14 1317 32 043 002 1285
cert_ridgeSupport_suffix_decode_2 196 000 14 1349 32 043 001 1317
cert_ridgeSupport_eq_3 196
theorem ridgeTest_large_196 : ridgeTest 196 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport196_eq]
    simp only [ridgeSupport196_suffix_000, ridgeSupport196_suffix_001, ridgeSupport196_suffix_002, ridgeSupport196_suffix_003, ridgeSupport196_suffix_004, ridgeSupport196_suffix_005, ridgeSupport196_suffix_006, ridgeSupport196_suffix_007, ridgeSupport196_suffix_008, ridgeSupport196_suffix_009, ridgeSupport196_suffix_010, ridgeSupport196_suffix_011, ridgeSupport196_suffix_012, ridgeSupport196_suffix_013, ridgeSupport196_suffix_014, ridgeSupport196_suffix_015, ridgeSupport196_suffix_016, ridgeSupport196_suffix_017, ridgeSupport196_suffix_018, ridgeSupport196_suffix_019, ridgeSupport196_suffix_020, ridgeSupport196_suffix_021, ridgeSupport196_suffix_022, ridgeSupport196_suffix_023, ridgeSupport196_suffix_024, ridgeSupport196_suffix_025, ridgeSupport196_suffix_026, ridgeSupport196_suffix_027, ridgeSupport196_suffix_028, ridgeSupport196_suffix_029, ridgeSupport196_suffix_030, ridgeSupport196_suffix_031, ridgeSupport196_suffix_032, ridgeSupport196_suffix_033, ridgeSupport196_suffix_034, ridgeSupport196_suffix_035, ridgeSupport196_suffix_036, ridgeSupport196_suffix_037, ridgeSupport196_suffix_038, ridgeSupport196_suffix_039, ridgeSupport196_suffix_040, ridgeSupport196_suffix_041, ridgeSupport196_suffix_042, ridgeSupport196_suffix_043, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport196_000_mask, ridgeSupport196_001_mask, ridgeSupport196_002_mask, ridgeSupport196_003_mask, ridgeSupport196_004_mask, ridgeSupport196_005_mask, ridgeSupport196_006_mask, ridgeSupport196_007_mask, ridgeSupport196_008_mask, ridgeSupport196_009_mask, ridgeSupport196_010_mask, ridgeSupport196_011_mask, ridgeSupport196_012_mask, ridgeSupport196_013_mask, ridgeSupport196_014_mask, ridgeSupport196_015_mask, ridgeSupport196_016_mask, ridgeSupport196_017_mask, ridgeSupport196_018_mask, ridgeSupport196_019_mask, ridgeSupport196_020_mask, ridgeSupport196_021_mask, ridgeSupport196_022_mask, ridgeSupport196_023_mask, ridgeSupport196_024_mask, ridgeSupport196_025_mask, ridgeSupport196_026_mask, ridgeSupport196_027_mask, ridgeSupport196_028_mask, ridgeSupport196_029_mask, ridgeSupport196_030_mask, ridgeSupport196_031_mask, ridgeSupport196_032_mask, ridgeSupport196_033_mask, ridgeSupport196_034_mask, ridgeSupport196_035_mask, ridgeSupport196_036_mask, ridgeSupport196_037_mask, ridgeSupport196_038_mask, ridgeSupport196_039_mask, ridgeSupport196_040_mask, ridgeSupport196_041_mask, ridgeSupport196_042_mask]
    decide +kernel
  · rw [ridgeSupport196_eq]
    simp only [ridgeSupport196_suffix_000, ridgeSupport196_suffix_001, ridgeSupport196_suffix_002, ridgeSupport196_suffix_003, ridgeSupport196_suffix_004, ridgeSupport196_suffix_005, ridgeSupport196_suffix_006, ridgeSupport196_suffix_007, ridgeSupport196_suffix_008, ridgeSupport196_suffix_009, ridgeSupport196_suffix_010, ridgeSupport196_suffix_011, ridgeSupport196_suffix_012, ridgeSupport196_suffix_013, ridgeSupport196_suffix_014, ridgeSupport196_suffix_015, ridgeSupport196_suffix_016, ridgeSupport196_suffix_017, ridgeSupport196_suffix_018, ridgeSupport196_suffix_019, ridgeSupport196_suffix_020, ridgeSupport196_suffix_021, ridgeSupport196_suffix_022, ridgeSupport196_suffix_023, ridgeSupport196_suffix_024, ridgeSupport196_suffix_025, ridgeSupport196_suffix_026, ridgeSupport196_suffix_027, ridgeSupport196_suffix_028, ridgeSupport196_suffix_029, ridgeSupport196_suffix_030, ridgeSupport196_suffix_031, ridgeSupport196_suffix_032, ridgeSupport196_suffix_033, ridgeSupport196_suffix_034, ridgeSupport196_suffix_035, ridgeSupport196_suffix_036, ridgeSupport196_suffix_037, ridgeSupport196_suffix_038, ridgeSupport196_suffix_039, ridgeSupport196_suffix_040, ridgeSupport196_suffix_041, ridgeSupport196_suffix_042, ridgeSupport196_suffix_043, List.all_append, List.all_nil, ridgeSupport196_000_checked, ridgeSupport196_001_checked, ridgeSupport196_002_checked, ridgeSupport196_003_checked, ridgeSupport196_004_checked, ridgeSupport196_005_checked, ridgeSupport196_006_checked, ridgeSupport196_007_checked, ridgeSupport196_008_checked, ridgeSupport196_009_checked, ridgeSupport196_010_checked, ridgeSupport196_011_checked, ridgeSupport196_012_checked, ridgeSupport196_013_checked, ridgeSupport196_014_checked, ridgeSupport196_015_checked, ridgeSupport196_016_checked, ridgeSupport196_017_checked, ridgeSupport196_018_checked, ridgeSupport196_019_checked, ridgeSupport196_020_checked, ridgeSupport196_021_checked, ridgeSupport196_022_checked, ridgeSupport196_023_checked, ridgeSupport196_024_checked, ridgeSupport196_025_checked, ridgeSupport196_026_checked, ridgeSupport196_027_checked, ridgeSupport196_028_checked, ridgeSupport196_029_checked, ridgeSupport196_030_checked, ridgeSupport196_031_checked, ridgeSupport196_032_checked, ridgeSupport196_033_checked, ridgeSupport196_034_checked, ridgeSupport196_035_checked, ridgeSupport196_036_checked, ridgeSupport196_037_checked, ridgeSupport196_038_checked, ridgeSupport196_039_checked, ridgeSupport196_040_checked, ridgeSupport196_041_checked, ridgeSupport196_042_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase01
