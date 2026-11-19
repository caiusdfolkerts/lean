module
prelude
public meta import LowerSchemas.FiniteRootedSixExtra
public import BundledChecks.RootedSixExtra00GrowthCacheRidgeSupport448Batch000
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra00
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
cert_ridgeSupport_suffix_decode_3 448 047 14
cert_ridgeSupport_suffix_decode_4 448 046 14 23 23 047 047 0
cert_ridgeSupport_suffix_decode_4 448 045 14 55 32 047 046 23
cert_ridgeSupport_suffix_decode_4 448 044 14 87 32 047 045 55
cert_ridgeSupport_suffix_decode_4 448 043 14 119 32 047 044 87
cert_ridgeSupport_suffix_decode_4 448 042 14 151 32 047 043 119
cert_ridgeSupport_suffix_decode_4 448 041 14 183 32 047 042 151
cert_ridgeSupport_suffix_decode_4 448 040 14 215 32 047 041 183
cert_ridgeSupport_suffix_decode_4 448 039 14 247 32 047 040 215
cert_ridgeSupport_suffix_decode_4 448 038 14 279 32 047 039 247
cert_ridgeSupport_suffix_decode_4 448 037 14 311 32 047 038 279
cert_ridgeSupport_suffix_decode_4 448 036 14 343 32 047 037 311
cert_ridgeSupport_suffix_decode_4 448 035 14 375 32 047 036 343
cert_ridgeSupport_suffix_decode_4 448 034 14 407 32 047 035 375
cert_ridgeSupport_suffix_decode_4 448 033 14 439 32 047 034 407
cert_ridgeSupport_suffix_decode_4 448 032 14 471 32 047 033 439
cert_ridgeSupport_suffix_decode_4 448 031 14 503 32 047 032 471
cert_ridgeSupport_suffix_decode_4 448 030 14 535 32 047 031 503
cert_ridgeSupport_suffix_decode_4 448 029 14 567 32 047 030 535
cert_ridgeSupport_suffix_decode_4 448 028 14 599 32 047 029 567
cert_ridgeSupport_suffix_decode_4 448 027 14 631 32 047 028 599
cert_ridgeSupport_suffix_decode_4 448 026 14 663 32 047 027 631
cert_ridgeSupport_suffix_decode_4 448 025 14 695 32 047 026 663
cert_ridgeSupport_suffix_decode_4 448 024 14 727 32 047 025 695
cert_ridgeSupport_suffix_decode_4 448 023 14 759 32 047 024 727
cert_ridgeSupport_suffix_decode_4 448 022 14 791 32 047 023 759
cert_ridgeSupport_suffix_decode_4 448 021 14 823 32 047 022 791
cert_ridgeSupport_suffix_decode_4 448 020 14 855 32 047 021 823
cert_ridgeSupport_suffix_decode_4 448 019 14 887 32 047 020 855
cert_ridgeSupport_suffix_decode_4 448 018 14 919 32 047 019 887
cert_ridgeSupport_suffix_decode_4 448 017 14 951 32 047 018 919
cert_ridgeSupport_suffix_decode_4 448 016 14 983 32 047 017 951
cert_ridgeSupport_suffix_decode_4 448 015 14 1015 32 047 016 983
cert_ridgeSupport_suffix_decode_4 448 014 14 1047 32 047 015 1015
cert_ridgeSupport_suffix_decode_4 448 013 14 1079 32 047 014 1047
cert_ridgeSupport_suffix_decode_4 448 012 14 1111 32 047 013 1079
cert_ridgeSupport_suffix_decode_4 448 011 14 1143 32 047 012 1111
cert_ridgeSupport_suffix_decode_4 448 010 14 1175 32 047 011 1143
cert_ridgeSupport_suffix_decode_4 448 009 14 1207 32 047 010 1175
cert_ridgeSupport_suffix_decode_4 448 008 14 1239 32 047 009 1207
cert_ridgeSupport_suffix_decode_4 448 007 14 1271 32 047 008 1239
cert_ridgeSupport_suffix_decode_4 448 006 14 1303 32 047 007 1271
cert_ridgeSupport_suffix_decode_4 448 005 14 1335 32 047 006 1303
cert_ridgeSupport_suffix_decode_4 448 004 14 1367 32 047 005 1335
cert_ridgeSupport_suffix_decode_4 448 003 14 1399 32 047 004 1367
cert_ridgeSupport_suffix_decode_4 448 002 14 1431 32 047 003 1399
cert_ridgeSupport_suffix_decode_4 448 001 14 1463 32 047 002 1431
cert_ridgeSupport_suffix_decode_4 448 000 14 1495 32 047 001 1463
cert_ridgeSupport_eq_4 448
theorem ridgeTest_large_448 : ridgeTest 448 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport448_eq]
    simp only [ridgeSupport448_suffix_000, ridgeSupport448_suffix_001, ridgeSupport448_suffix_002, ridgeSupport448_suffix_003, ridgeSupport448_suffix_004, ridgeSupport448_suffix_005, ridgeSupport448_suffix_006, ridgeSupport448_suffix_007, ridgeSupport448_suffix_008, ridgeSupport448_suffix_009, ridgeSupport448_suffix_010, ridgeSupport448_suffix_011, ridgeSupport448_suffix_012, ridgeSupport448_suffix_013, ridgeSupport448_suffix_014, ridgeSupport448_suffix_015, ridgeSupport448_suffix_016, ridgeSupport448_suffix_017, ridgeSupport448_suffix_018, ridgeSupport448_suffix_019, ridgeSupport448_suffix_020, ridgeSupport448_suffix_021, ridgeSupport448_suffix_022, ridgeSupport448_suffix_023, ridgeSupport448_suffix_024, ridgeSupport448_suffix_025, ridgeSupport448_suffix_026, ridgeSupport448_suffix_027, ridgeSupport448_suffix_028, ridgeSupport448_suffix_029, ridgeSupport448_suffix_030, ridgeSupport448_suffix_031, ridgeSupport448_suffix_032, ridgeSupport448_suffix_033, ridgeSupport448_suffix_034, ridgeSupport448_suffix_035, ridgeSupport448_suffix_036, ridgeSupport448_suffix_037, ridgeSupport448_suffix_038, ridgeSupport448_suffix_039, ridgeSupport448_suffix_040, ridgeSupport448_suffix_041, ridgeSupport448_suffix_042, ridgeSupport448_suffix_043, ridgeSupport448_suffix_044, ridgeSupport448_suffix_045, ridgeSupport448_suffix_046, ridgeSupport448_suffix_047, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport448_000_mask, ridgeSupport448_001_mask, ridgeSupport448_002_mask, ridgeSupport448_003_mask, ridgeSupport448_004_mask, ridgeSupport448_005_mask, ridgeSupport448_006_mask, ridgeSupport448_007_mask, ridgeSupport448_008_mask, ridgeSupport448_009_mask, ridgeSupport448_010_mask, ridgeSupport448_011_mask, ridgeSupport448_012_mask, ridgeSupport448_013_mask, ridgeSupport448_014_mask, ridgeSupport448_015_mask, ridgeSupport448_016_mask, ridgeSupport448_017_mask, ridgeSupport448_018_mask, ridgeSupport448_019_mask, ridgeSupport448_020_mask, ridgeSupport448_021_mask, ridgeSupport448_022_mask, ridgeSupport448_023_mask, ridgeSupport448_024_mask, ridgeSupport448_025_mask, ridgeSupport448_026_mask, ridgeSupport448_027_mask, ridgeSupport448_028_mask, ridgeSupport448_029_mask, ridgeSupport448_030_mask, ridgeSupport448_031_mask, ridgeSupport448_032_mask, ridgeSupport448_033_mask, ridgeSupport448_034_mask, ridgeSupport448_035_mask, ridgeSupport448_036_mask, ridgeSupport448_037_mask, ridgeSupport448_038_mask, ridgeSupport448_039_mask, ridgeSupport448_040_mask, ridgeSupport448_041_mask, ridgeSupport448_042_mask, ridgeSupport448_043_mask, ridgeSupport448_044_mask, ridgeSupport448_045_mask, ridgeSupport448_046_mask]
    decide +kernel
  · rw [ridgeSupport448_eq]
    simp only [ridgeSupport448_suffix_000, ridgeSupport448_suffix_001, ridgeSupport448_suffix_002, ridgeSupport448_suffix_003, ridgeSupport448_suffix_004, ridgeSupport448_suffix_005, ridgeSupport448_suffix_006, ridgeSupport448_suffix_007, ridgeSupport448_suffix_008, ridgeSupport448_suffix_009, ridgeSupport448_suffix_010, ridgeSupport448_suffix_011, ridgeSupport448_suffix_012, ridgeSupport448_suffix_013, ridgeSupport448_suffix_014, ridgeSupport448_suffix_015, ridgeSupport448_suffix_016, ridgeSupport448_suffix_017, ridgeSupport448_suffix_018, ridgeSupport448_suffix_019, ridgeSupport448_suffix_020, ridgeSupport448_suffix_021, ridgeSupport448_suffix_022, ridgeSupport448_suffix_023, ridgeSupport448_suffix_024, ridgeSupport448_suffix_025, ridgeSupport448_suffix_026, ridgeSupport448_suffix_027, ridgeSupport448_suffix_028, ridgeSupport448_suffix_029, ridgeSupport448_suffix_030, ridgeSupport448_suffix_031, ridgeSupport448_suffix_032, ridgeSupport448_suffix_033, ridgeSupport448_suffix_034, ridgeSupport448_suffix_035, ridgeSupport448_suffix_036, ridgeSupport448_suffix_037, ridgeSupport448_suffix_038, ridgeSupport448_suffix_039, ridgeSupport448_suffix_040, ridgeSupport448_suffix_041, ridgeSupport448_suffix_042, ridgeSupport448_suffix_043, ridgeSupport448_suffix_044, ridgeSupport448_suffix_045, ridgeSupport448_suffix_046, ridgeSupport448_suffix_047, List.all_append, List.all_nil, ridgeSupport448_000_checked, ridgeSupport448_001_checked, ridgeSupport448_002_checked, ridgeSupport448_003_checked, ridgeSupport448_004_checked, ridgeSupport448_005_checked, ridgeSupport448_006_checked, ridgeSupport448_007_checked, ridgeSupport448_008_checked, ridgeSupport448_009_checked, ridgeSupport448_010_checked, ridgeSupport448_011_checked, ridgeSupport448_012_checked, ridgeSupport448_013_checked, ridgeSupport448_014_checked, ridgeSupport448_015_checked, ridgeSupport448_016_checked, ridgeSupport448_017_checked, ridgeSupport448_018_checked, ridgeSupport448_019_checked, ridgeSupport448_020_checked, ridgeSupport448_021_checked, ridgeSupport448_022_checked, ridgeSupport448_023_checked, ridgeSupport448_024_checked, ridgeSupport448_025_checked, ridgeSupport448_026_checked, ridgeSupport448_027_checked, ridgeSupport448_028_checked, ridgeSupport448_029_checked, ridgeSupport448_030_checked, ridgeSupport448_031_checked, ridgeSupport448_032_checked, ridgeSupport448_033_checked, ridgeSupport448_034_checked, ridgeSupport448_035_checked, ridgeSupport448_036_checked, ridgeSupport448_037_checked, ridgeSupport448_038_checked, ridgeSupport448_039_checked, ridgeSupport448_040_checked, ridgeSupport448_041_checked, ridgeSupport448_042_checked, ridgeSupport448_043_checked, ridgeSupport448_044_checked, ridgeSupport448_045_checked, ridgeSupport448_046_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixExtra00
