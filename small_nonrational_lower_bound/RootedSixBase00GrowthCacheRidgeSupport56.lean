module
prelude
public meta import LowerSchemas.FiniteRootedSixBase
public import BundledChecks.RootedSixBase00GrowthCacheRidgeSupport56Batch000
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
cert_ridgeSupport_suffix_decode 56 043 15
cert_ridgeSupport_suffix_decode_2 56 042 15 5 5 043 043 0
cert_ridgeSupport_suffix_decode_2 56 041 15 37 32 043 042 5
cert_ridgeSupport_suffix_decode_2 56 040 15 69 32 043 041 37
cert_ridgeSupport_suffix_decode_2 56 039 15 101 32 043 040 69
cert_ridgeSupport_suffix_decode_2 56 038 15 133 32 043 039 101
cert_ridgeSupport_suffix_decode_2 56 037 15 165 32 043 038 133
cert_ridgeSupport_suffix_decode_2 56 036 15 197 32 043 037 165
cert_ridgeSupport_suffix_decode_2 56 035 15 229 32 043 036 197
cert_ridgeSupport_suffix_decode_2 56 034 15 261 32 043 035 229
cert_ridgeSupport_suffix_decode_2 56 033 15 293 32 043 034 261
cert_ridgeSupport_suffix_decode_2 56 032 15 325 32 043 033 293
cert_ridgeSupport_suffix_decode_2 56 031 15 357 32 043 032 325
cert_ridgeSupport_suffix_decode_2 56 030 15 389 32 043 031 357
cert_ridgeSupport_suffix_decode_2 56 029 15 421 32 043 030 389
cert_ridgeSupport_suffix_decode_2 56 028 15 453 32 043 029 421
cert_ridgeSupport_suffix_decode_2 56 027 15 485 32 043 028 453
cert_ridgeSupport_suffix_decode_2 56 026 15 517 32 043 027 485
cert_ridgeSupport_suffix_decode_2 56 025 15 549 32 043 026 517
cert_ridgeSupport_suffix_decode_2 56 024 15 581 32 043 025 549
cert_ridgeSupport_suffix_decode_2 56 023 15 613 32 043 024 581
cert_ridgeSupport_suffix_decode_2 56 022 15 645 32 043 023 613
cert_ridgeSupport_suffix_decode_2 56 021 15 677 32 043 022 645
cert_ridgeSupport_suffix_decode_2 56 020 15 709 32 043 021 677
cert_ridgeSupport_suffix_decode_2 56 019 15 741 32 043 020 709
cert_ridgeSupport_suffix_decode_2 56 018 15 773 32 043 019 741
cert_ridgeSupport_suffix_decode_2 56 017 15 805 32 043 018 773
cert_ridgeSupport_suffix_decode_2 56 016 15 837 32 043 017 805
cert_ridgeSupport_suffix_decode_2 56 015 15 869 32 043 016 837
cert_ridgeSupport_suffix_decode_2 56 014 15 901 32 043 015 869
cert_ridgeSupport_suffix_decode_2 56 013 15 933 32 043 014 901
cert_ridgeSupport_suffix_decode_2 56 012 15 965 32 043 013 933
cert_ridgeSupport_suffix_decode_2 56 011 15 997 32 043 012 965
cert_ridgeSupport_suffix_decode_2 56 010 15 1029 32 043 011 997
cert_ridgeSupport_suffix_decode_2 56 009 15 1061 32 043 010 1029
cert_ridgeSupport_suffix_decode_2 56 008 15 1093 32 043 009 1061
cert_ridgeSupport_suffix_decode_2 56 007 15 1125 32 043 008 1093
cert_ridgeSupport_suffix_decode_2 56 006 15 1157 32 043 007 1125
cert_ridgeSupport_suffix_decode_2 56 005 15 1189 32 043 006 1157
cert_ridgeSupport_suffix_decode_2 56 004 15 1221 32 043 005 1189
cert_ridgeSupport_suffix_decode_2 56 003 15 1253 32 043 004 1221
cert_ridgeSupport_suffix_decode_2 56 002 15 1285 32 043 003 1253
cert_ridgeSupport_suffix_decode_2 56 001 15 1317 32 043 002 1285
cert_ridgeSupport_suffix_decode_2 56 000 15 1349 32 043 001 1317
cert_ridgeSupport_eq_3 56
theorem ridgeTest_large_56 : ridgeTest 56 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport56_eq]
    simp only [ridgeSupport56_suffix_000, ridgeSupport56_suffix_001, ridgeSupport56_suffix_002, ridgeSupport56_suffix_003, ridgeSupport56_suffix_004, ridgeSupport56_suffix_005, ridgeSupport56_suffix_006, ridgeSupport56_suffix_007, ridgeSupport56_suffix_008, ridgeSupport56_suffix_009, ridgeSupport56_suffix_010, ridgeSupport56_suffix_011, ridgeSupport56_suffix_012, ridgeSupport56_suffix_013, ridgeSupport56_suffix_014, ridgeSupport56_suffix_015, ridgeSupport56_suffix_016, ridgeSupport56_suffix_017, ridgeSupport56_suffix_018, ridgeSupport56_suffix_019, ridgeSupport56_suffix_020, ridgeSupport56_suffix_021, ridgeSupport56_suffix_022, ridgeSupport56_suffix_023, ridgeSupport56_suffix_024, ridgeSupport56_suffix_025, ridgeSupport56_suffix_026, ridgeSupport56_suffix_027, ridgeSupport56_suffix_028, ridgeSupport56_suffix_029, ridgeSupport56_suffix_030, ridgeSupport56_suffix_031, ridgeSupport56_suffix_032, ridgeSupport56_suffix_033, ridgeSupport56_suffix_034, ridgeSupport56_suffix_035, ridgeSupport56_suffix_036, ridgeSupport56_suffix_037, ridgeSupport56_suffix_038, ridgeSupport56_suffix_039, ridgeSupport56_suffix_040, ridgeSupport56_suffix_041, ridgeSupport56_suffix_042, ridgeSupport56_suffix_043, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport56_000_mask, ridgeSupport56_001_mask, ridgeSupport56_002_mask, ridgeSupport56_003_mask, ridgeSupport56_004_mask, ridgeSupport56_005_mask, ridgeSupport56_006_mask, ridgeSupport56_007_mask, ridgeSupport56_008_mask, ridgeSupport56_009_mask, ridgeSupport56_010_mask, ridgeSupport56_011_mask, ridgeSupport56_012_mask, ridgeSupport56_013_mask, ridgeSupport56_014_mask, ridgeSupport56_015_mask, ridgeSupport56_016_mask, ridgeSupport56_017_mask, ridgeSupport56_018_mask, ridgeSupport56_019_mask, ridgeSupport56_020_mask, ridgeSupport56_021_mask, ridgeSupport56_022_mask, ridgeSupport56_023_mask, ridgeSupport56_024_mask, ridgeSupport56_025_mask, ridgeSupport56_026_mask, ridgeSupport56_027_mask, ridgeSupport56_028_mask, ridgeSupport56_029_mask, ridgeSupport56_030_mask, ridgeSupport56_031_mask, ridgeSupport56_032_mask, ridgeSupport56_033_mask, ridgeSupport56_034_mask, ridgeSupport56_035_mask, ridgeSupport56_036_mask, ridgeSupport56_037_mask, ridgeSupport56_038_mask, ridgeSupport56_039_mask, ridgeSupport56_040_mask, ridgeSupport56_041_mask, ridgeSupport56_042_mask]
    decide +kernel
  · rw [ridgeSupport56_eq]
    simp only [ridgeSupport56_suffix_000, ridgeSupport56_suffix_001, ridgeSupport56_suffix_002, ridgeSupport56_suffix_003, ridgeSupport56_suffix_004, ridgeSupport56_suffix_005, ridgeSupport56_suffix_006, ridgeSupport56_suffix_007, ridgeSupport56_suffix_008, ridgeSupport56_suffix_009, ridgeSupport56_suffix_010, ridgeSupport56_suffix_011, ridgeSupport56_suffix_012, ridgeSupport56_suffix_013, ridgeSupport56_suffix_014, ridgeSupport56_suffix_015, ridgeSupport56_suffix_016, ridgeSupport56_suffix_017, ridgeSupport56_suffix_018, ridgeSupport56_suffix_019, ridgeSupport56_suffix_020, ridgeSupport56_suffix_021, ridgeSupport56_suffix_022, ridgeSupport56_suffix_023, ridgeSupport56_suffix_024, ridgeSupport56_suffix_025, ridgeSupport56_suffix_026, ridgeSupport56_suffix_027, ridgeSupport56_suffix_028, ridgeSupport56_suffix_029, ridgeSupport56_suffix_030, ridgeSupport56_suffix_031, ridgeSupport56_suffix_032, ridgeSupport56_suffix_033, ridgeSupport56_suffix_034, ridgeSupport56_suffix_035, ridgeSupport56_suffix_036, ridgeSupport56_suffix_037, ridgeSupport56_suffix_038, ridgeSupport56_suffix_039, ridgeSupport56_suffix_040, ridgeSupport56_suffix_041, ridgeSupport56_suffix_042, ridgeSupport56_suffix_043, List.all_append, List.all_nil, ridgeSupport56_000_checked, ridgeSupport56_001_checked, ridgeSupport56_002_checked, ridgeSupport56_003_checked, ridgeSupport56_004_checked, ridgeSupport56_005_checked, ridgeSupport56_006_checked, ridgeSupport56_007_checked, ridgeSupport56_008_checked, ridgeSupport56_009_checked, ridgeSupport56_010_checked, ridgeSupport56_011_checked, ridgeSupport56_012_checked, ridgeSupport56_013_checked, ridgeSupport56_014_checked, ridgeSupport56_015_checked, ridgeSupport56_016_checked, ridgeSupport56_017_checked, ridgeSupport56_018_checked, ridgeSupport56_019_checked, ridgeSupport56_020_checked, ridgeSupport56_021_checked, ridgeSupport56_022_checked, ridgeSupport56_023_checked, ridgeSupport56_024_checked, ridgeSupport56_025_checked, ridgeSupport56_026_checked, ridgeSupport56_027_checked, ridgeSupport56_028_checked, ridgeSupport56_029_checked, ridgeSupport56_030_checked, ridgeSupport56_031_checked, ridgeSupport56_032_checked, ridgeSupport56_033_checked, ridgeSupport56_034_checked, ridgeSupport56_035_checked, ridgeSupport56_036_checked, ridgeSupport56_037_checked, ridgeSupport56_038_checked, ridgeSupport56_039_checked, ridgeSupport56_040_checked, ridgeSupport56_041_checked, ridgeSupport56_042_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase00
