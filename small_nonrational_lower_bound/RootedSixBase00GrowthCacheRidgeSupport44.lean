module
prelude
public meta import LowerSchemas.FiniteRootedSixBase
public import BundledChecks.RootedSixBase00GrowthCacheRidgeSupport44Batch000
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
cert_ridgeSupport_suffix_decode 44 043 15
cert_ridgeSupport_suffix_decode_2 44 042 15 5 5 043 043 0
cert_ridgeSupport_suffix_decode_2 44 041 15 37 32 043 042 5
cert_ridgeSupport_suffix_decode_2 44 040 15 69 32 043 041 37
cert_ridgeSupport_suffix_decode_2 44 039 15 101 32 043 040 69
cert_ridgeSupport_suffix_decode_2 44 038 15 133 32 043 039 101
cert_ridgeSupport_suffix_decode_2 44 037 15 165 32 043 038 133
cert_ridgeSupport_suffix_decode_2 44 036 15 197 32 043 037 165
cert_ridgeSupport_suffix_decode_2 44 035 15 229 32 043 036 197
cert_ridgeSupport_suffix_decode_2 44 034 15 261 32 043 035 229
cert_ridgeSupport_suffix_decode_2 44 033 15 293 32 043 034 261
cert_ridgeSupport_suffix_decode_2 44 032 15 325 32 043 033 293
cert_ridgeSupport_suffix_decode_2 44 031 15 357 32 043 032 325
cert_ridgeSupport_suffix_decode_2 44 030 15 389 32 043 031 357
cert_ridgeSupport_suffix_decode_2 44 029 15 421 32 043 030 389
cert_ridgeSupport_suffix_decode_2 44 028 15 453 32 043 029 421
cert_ridgeSupport_suffix_decode_2 44 027 15 485 32 043 028 453
cert_ridgeSupport_suffix_decode_2 44 026 15 517 32 043 027 485
cert_ridgeSupport_suffix_decode_2 44 025 15 549 32 043 026 517
cert_ridgeSupport_suffix_decode_2 44 024 15 581 32 043 025 549
cert_ridgeSupport_suffix_decode_2 44 023 15 613 32 043 024 581
cert_ridgeSupport_suffix_decode_2 44 022 15 645 32 043 023 613
cert_ridgeSupport_suffix_decode_2 44 021 15 677 32 043 022 645
cert_ridgeSupport_suffix_decode_2 44 020 15 709 32 043 021 677
cert_ridgeSupport_suffix_decode_2 44 019 15 741 32 043 020 709
cert_ridgeSupport_suffix_decode_2 44 018 15 773 32 043 019 741
cert_ridgeSupport_suffix_decode_2 44 017 15 805 32 043 018 773
cert_ridgeSupport_suffix_decode_2 44 016 15 837 32 043 017 805
cert_ridgeSupport_suffix_decode_2 44 015 15 869 32 043 016 837
cert_ridgeSupport_suffix_decode_2 44 014 15 901 32 043 015 869
cert_ridgeSupport_suffix_decode_2 44 013 15 933 32 043 014 901
cert_ridgeSupport_suffix_decode_2 44 012 15 965 32 043 013 933
cert_ridgeSupport_suffix_decode_2 44 011 15 997 32 043 012 965
cert_ridgeSupport_suffix_decode_2 44 010 15 1029 32 043 011 997
cert_ridgeSupport_suffix_decode_2 44 009 15 1061 32 043 010 1029
cert_ridgeSupport_suffix_decode_2 44 008 15 1093 32 043 009 1061
cert_ridgeSupport_suffix_decode_2 44 007 15 1125 32 043 008 1093
cert_ridgeSupport_suffix_decode_2 44 006 15 1157 32 043 007 1125
cert_ridgeSupport_suffix_decode_2 44 005 15 1189 32 043 006 1157
cert_ridgeSupport_suffix_decode_2 44 004 15 1221 32 043 005 1189
cert_ridgeSupport_suffix_decode_2 44 003 15 1253 32 043 004 1221
cert_ridgeSupport_suffix_decode_2 44 002 15 1285 32 043 003 1253
cert_ridgeSupport_suffix_decode_2 44 001 15 1317 32 043 002 1285
cert_ridgeSupport_suffix_decode_2 44 000 15 1349 32 043 001 1317
cert_ridgeSupport_eq_3 44
theorem ridgeTest_large_44 : ridgeTest 44 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport44_eq]
    simp only [ridgeSupport44_suffix_000, ridgeSupport44_suffix_001, ridgeSupport44_suffix_002, ridgeSupport44_suffix_003, ridgeSupport44_suffix_004, ridgeSupport44_suffix_005, ridgeSupport44_suffix_006, ridgeSupport44_suffix_007, ridgeSupport44_suffix_008, ridgeSupport44_suffix_009, ridgeSupport44_suffix_010, ridgeSupport44_suffix_011, ridgeSupport44_suffix_012, ridgeSupport44_suffix_013, ridgeSupport44_suffix_014, ridgeSupport44_suffix_015, ridgeSupport44_suffix_016, ridgeSupport44_suffix_017, ridgeSupport44_suffix_018, ridgeSupport44_suffix_019, ridgeSupport44_suffix_020, ridgeSupport44_suffix_021, ridgeSupport44_suffix_022, ridgeSupport44_suffix_023, ridgeSupport44_suffix_024, ridgeSupport44_suffix_025, ridgeSupport44_suffix_026, ridgeSupport44_suffix_027, ridgeSupport44_suffix_028, ridgeSupport44_suffix_029, ridgeSupport44_suffix_030, ridgeSupport44_suffix_031, ridgeSupport44_suffix_032, ridgeSupport44_suffix_033, ridgeSupport44_suffix_034, ridgeSupport44_suffix_035, ridgeSupport44_suffix_036, ridgeSupport44_suffix_037, ridgeSupport44_suffix_038, ridgeSupport44_suffix_039, ridgeSupport44_suffix_040, ridgeSupport44_suffix_041, ridgeSupport44_suffix_042, ridgeSupport44_suffix_043, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport44_000_mask, ridgeSupport44_001_mask, ridgeSupport44_002_mask, ridgeSupport44_003_mask, ridgeSupport44_004_mask, ridgeSupport44_005_mask, ridgeSupport44_006_mask, ridgeSupport44_007_mask, ridgeSupport44_008_mask, ridgeSupport44_009_mask, ridgeSupport44_010_mask, ridgeSupport44_011_mask, ridgeSupport44_012_mask, ridgeSupport44_013_mask, ridgeSupport44_014_mask, ridgeSupport44_015_mask, ridgeSupport44_016_mask, ridgeSupport44_017_mask, ridgeSupport44_018_mask, ridgeSupport44_019_mask, ridgeSupport44_020_mask, ridgeSupport44_021_mask, ridgeSupport44_022_mask, ridgeSupport44_023_mask, ridgeSupport44_024_mask, ridgeSupport44_025_mask, ridgeSupport44_026_mask, ridgeSupport44_027_mask, ridgeSupport44_028_mask, ridgeSupport44_029_mask, ridgeSupport44_030_mask, ridgeSupport44_031_mask, ridgeSupport44_032_mask, ridgeSupport44_033_mask, ridgeSupport44_034_mask, ridgeSupport44_035_mask, ridgeSupport44_036_mask, ridgeSupport44_037_mask, ridgeSupport44_038_mask, ridgeSupport44_039_mask, ridgeSupport44_040_mask, ridgeSupport44_041_mask, ridgeSupport44_042_mask]
    decide +kernel
  · rw [ridgeSupport44_eq]
    simp only [ridgeSupport44_suffix_000, ridgeSupport44_suffix_001, ridgeSupport44_suffix_002, ridgeSupport44_suffix_003, ridgeSupport44_suffix_004, ridgeSupport44_suffix_005, ridgeSupport44_suffix_006, ridgeSupport44_suffix_007, ridgeSupport44_suffix_008, ridgeSupport44_suffix_009, ridgeSupport44_suffix_010, ridgeSupport44_suffix_011, ridgeSupport44_suffix_012, ridgeSupport44_suffix_013, ridgeSupport44_suffix_014, ridgeSupport44_suffix_015, ridgeSupport44_suffix_016, ridgeSupport44_suffix_017, ridgeSupport44_suffix_018, ridgeSupport44_suffix_019, ridgeSupport44_suffix_020, ridgeSupport44_suffix_021, ridgeSupport44_suffix_022, ridgeSupport44_suffix_023, ridgeSupport44_suffix_024, ridgeSupport44_suffix_025, ridgeSupport44_suffix_026, ridgeSupport44_suffix_027, ridgeSupport44_suffix_028, ridgeSupport44_suffix_029, ridgeSupport44_suffix_030, ridgeSupport44_suffix_031, ridgeSupport44_suffix_032, ridgeSupport44_suffix_033, ridgeSupport44_suffix_034, ridgeSupport44_suffix_035, ridgeSupport44_suffix_036, ridgeSupport44_suffix_037, ridgeSupport44_suffix_038, ridgeSupport44_suffix_039, ridgeSupport44_suffix_040, ridgeSupport44_suffix_041, ridgeSupport44_suffix_042, ridgeSupport44_suffix_043, List.all_append, List.all_nil, ridgeSupport44_000_checked, ridgeSupport44_001_checked, ridgeSupport44_002_checked, ridgeSupport44_003_checked, ridgeSupport44_004_checked, ridgeSupport44_005_checked, ridgeSupport44_006_checked, ridgeSupport44_007_checked, ridgeSupport44_008_checked, ridgeSupport44_009_checked, ridgeSupport44_010_checked, ridgeSupport44_011_checked, ridgeSupport44_012_checked, ridgeSupport44_013_checked, ridgeSupport44_014_checked, ridgeSupport44_015_checked, ridgeSupport44_016_checked, ridgeSupport44_017_checked, ridgeSupport44_018_checked, ridgeSupport44_019_checked, ridgeSupport44_020_checked, ridgeSupport44_021_checked, ridgeSupport44_022_checked, ridgeSupport44_023_checked, ridgeSupport44_024_checked, ridgeSupport44_025_checked, ridgeSupport44_026_checked, ridgeSupport44_027_checked, ridgeSupport44_028_checked, ridgeSupport44_029_checked, ridgeSupport44_030_checked, ridgeSupport44_031_checked, ridgeSupport44_032_checked, ridgeSupport44_033_checked, ridgeSupport44_034_checked, ridgeSupport44_035_checked, ridgeSupport44_036_checked, ridgeSupport44_037_checked, ridgeSupport44_038_checked, ridgeSupport44_039_checked, ridgeSupport44_040_checked, ridgeSupport44_041_checked, ridgeSupport44_042_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase00
