module
prelude
public meta import LowerSchemas.FiniteRootedSixExtra
public import BundledChecks.RootedSixExtra00GrowthCacheRidgeSupport896Batch000
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra00
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
cert_ridgeSupport_suffix_decode_3 896 047 14
cert_ridgeSupport_suffix_decode_4 896 046 14 23 23 047 047 0
cert_ridgeSupport_suffix_decode_4 896 045 14 55 32 047 046 23
cert_ridgeSupport_suffix_decode_4 896 044 14 87 32 047 045 55
cert_ridgeSupport_suffix_decode_4 896 043 14 119 32 047 044 87
cert_ridgeSupport_suffix_decode_4 896 042 14 151 32 047 043 119
cert_ridgeSupport_suffix_decode_4 896 041 14 183 32 047 042 151
cert_ridgeSupport_suffix_decode_4 896 040 14 215 32 047 041 183
cert_ridgeSupport_suffix_decode_4 896 039 14 247 32 047 040 215
cert_ridgeSupport_suffix_decode_4 896 038 14 279 32 047 039 247
cert_ridgeSupport_suffix_decode_4 896 037 14 311 32 047 038 279
cert_ridgeSupport_suffix_decode_4 896 036 14 343 32 047 037 311
cert_ridgeSupport_suffix_decode_4 896 035 14 375 32 047 036 343
cert_ridgeSupport_suffix_decode_4 896 034 14 407 32 047 035 375
cert_ridgeSupport_suffix_decode_4 896 033 14 439 32 047 034 407
cert_ridgeSupport_suffix_decode_4 896 032 14 471 32 047 033 439
cert_ridgeSupport_suffix_decode_4 896 031 14 503 32 047 032 471
cert_ridgeSupport_suffix_decode_4 896 030 14 535 32 047 031 503
cert_ridgeSupport_suffix_decode_4 896 029 14 567 32 047 030 535
cert_ridgeSupport_suffix_decode_4 896 028 14 599 32 047 029 567
cert_ridgeSupport_suffix_decode_4 896 027 14 631 32 047 028 599
cert_ridgeSupport_suffix_decode_4 896 026 14 663 32 047 027 631
cert_ridgeSupport_suffix_decode_4 896 025 14 695 32 047 026 663
cert_ridgeSupport_suffix_decode_4 896 024 14 727 32 047 025 695
cert_ridgeSupport_suffix_decode_4 896 023 14 759 32 047 024 727
cert_ridgeSupport_suffix_decode_4 896 022 14 791 32 047 023 759
cert_ridgeSupport_suffix_decode_4 896 021 14 823 32 047 022 791
cert_ridgeSupport_suffix_decode_4 896 020 14 855 32 047 021 823
cert_ridgeSupport_suffix_decode_4 896 019 14 887 32 047 020 855
cert_ridgeSupport_suffix_decode_4 896 018 14 919 32 047 019 887
cert_ridgeSupport_suffix_decode_4 896 017 14 951 32 047 018 919
cert_ridgeSupport_suffix_decode_4 896 016 14 983 32 047 017 951
cert_ridgeSupport_suffix_decode_4 896 015 14 1015 32 047 016 983
cert_ridgeSupport_suffix_decode_4 896 014 14 1047 32 047 015 1015
cert_ridgeSupport_suffix_decode_4 896 013 14 1079 32 047 014 1047
cert_ridgeSupport_suffix_decode_4 896 012 14 1111 32 047 013 1079
cert_ridgeSupport_suffix_decode_4 896 011 14 1143 32 047 012 1111
cert_ridgeSupport_suffix_decode_4 896 010 14 1175 32 047 011 1143
cert_ridgeSupport_suffix_decode_4 896 009 14 1207 32 047 010 1175
cert_ridgeSupport_suffix_decode_4 896 008 14 1239 32 047 009 1207
cert_ridgeSupport_suffix_decode_4 896 007 14 1271 32 047 008 1239
cert_ridgeSupport_suffix_decode_4 896 006 14 1303 32 047 007 1271
cert_ridgeSupport_suffix_decode_4 896 005 14 1335 32 047 006 1303
cert_ridgeSupport_suffix_decode_4 896 004 14 1367 32 047 005 1335
cert_ridgeSupport_suffix_decode_4 896 003 14 1399 32 047 004 1367
cert_ridgeSupport_suffix_decode_4 896 002 14 1431 32 047 003 1399
cert_ridgeSupport_suffix_decode_4 896 001 14 1463 32 047 002 1431
cert_ridgeSupport_suffix_decode_4 896 000 14 1495 32 047 001 1463
cert_ridgeSupport_eq_4 896
theorem ridgeTest_large_896 : ridgeTest 896 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport896_eq]
    simp only [ridgeSupport896_suffix_000, ridgeSupport896_suffix_001, ridgeSupport896_suffix_002, ridgeSupport896_suffix_003, ridgeSupport896_suffix_004, ridgeSupport896_suffix_005, ridgeSupport896_suffix_006, ridgeSupport896_suffix_007, ridgeSupport896_suffix_008, ridgeSupport896_suffix_009, ridgeSupport896_suffix_010, ridgeSupport896_suffix_011, ridgeSupport896_suffix_012, ridgeSupport896_suffix_013, ridgeSupport896_suffix_014, ridgeSupport896_suffix_015, ridgeSupport896_suffix_016, ridgeSupport896_suffix_017, ridgeSupport896_suffix_018, ridgeSupport896_suffix_019, ridgeSupport896_suffix_020, ridgeSupport896_suffix_021, ridgeSupport896_suffix_022, ridgeSupport896_suffix_023, ridgeSupport896_suffix_024, ridgeSupport896_suffix_025, ridgeSupport896_suffix_026, ridgeSupport896_suffix_027, ridgeSupport896_suffix_028, ridgeSupport896_suffix_029, ridgeSupport896_suffix_030, ridgeSupport896_suffix_031, ridgeSupport896_suffix_032, ridgeSupport896_suffix_033, ridgeSupport896_suffix_034, ridgeSupport896_suffix_035, ridgeSupport896_suffix_036, ridgeSupport896_suffix_037, ridgeSupport896_suffix_038, ridgeSupport896_suffix_039, ridgeSupport896_suffix_040, ridgeSupport896_suffix_041, ridgeSupport896_suffix_042, ridgeSupport896_suffix_043, ridgeSupport896_suffix_044, ridgeSupport896_suffix_045, ridgeSupport896_suffix_046, ridgeSupport896_suffix_047, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport896_000_mask, ridgeSupport896_001_mask, ridgeSupport896_002_mask, ridgeSupport896_003_mask, ridgeSupport896_004_mask, ridgeSupport896_005_mask, ridgeSupport896_006_mask, ridgeSupport896_007_mask, ridgeSupport896_008_mask, ridgeSupport896_009_mask, ridgeSupport896_010_mask, ridgeSupport896_011_mask, ridgeSupport896_012_mask, ridgeSupport896_013_mask, ridgeSupport896_014_mask, ridgeSupport896_015_mask, ridgeSupport896_016_mask, ridgeSupport896_017_mask, ridgeSupport896_018_mask, ridgeSupport896_019_mask, ridgeSupport896_020_mask, ridgeSupport896_021_mask, ridgeSupport896_022_mask, ridgeSupport896_023_mask, ridgeSupport896_024_mask, ridgeSupport896_025_mask, ridgeSupport896_026_mask, ridgeSupport896_027_mask, ridgeSupport896_028_mask, ridgeSupport896_029_mask, ridgeSupport896_030_mask, ridgeSupport896_031_mask, ridgeSupport896_032_mask, ridgeSupport896_033_mask, ridgeSupport896_034_mask, ridgeSupport896_035_mask, ridgeSupport896_036_mask, ridgeSupport896_037_mask, ridgeSupport896_038_mask, ridgeSupport896_039_mask, ridgeSupport896_040_mask, ridgeSupport896_041_mask, ridgeSupport896_042_mask, ridgeSupport896_043_mask, ridgeSupport896_044_mask, ridgeSupport896_045_mask, ridgeSupport896_046_mask]
    decide +kernel
  · rw [ridgeSupport896_eq]
    simp only [ridgeSupport896_suffix_000, ridgeSupport896_suffix_001, ridgeSupport896_suffix_002, ridgeSupport896_suffix_003, ridgeSupport896_suffix_004, ridgeSupport896_suffix_005, ridgeSupport896_suffix_006, ridgeSupport896_suffix_007, ridgeSupport896_suffix_008, ridgeSupport896_suffix_009, ridgeSupport896_suffix_010, ridgeSupport896_suffix_011, ridgeSupport896_suffix_012, ridgeSupport896_suffix_013, ridgeSupport896_suffix_014, ridgeSupport896_suffix_015, ridgeSupport896_suffix_016, ridgeSupport896_suffix_017, ridgeSupport896_suffix_018, ridgeSupport896_suffix_019, ridgeSupport896_suffix_020, ridgeSupport896_suffix_021, ridgeSupport896_suffix_022, ridgeSupport896_suffix_023, ridgeSupport896_suffix_024, ridgeSupport896_suffix_025, ridgeSupport896_suffix_026, ridgeSupport896_suffix_027, ridgeSupport896_suffix_028, ridgeSupport896_suffix_029, ridgeSupport896_suffix_030, ridgeSupport896_suffix_031, ridgeSupport896_suffix_032, ridgeSupport896_suffix_033, ridgeSupport896_suffix_034, ridgeSupport896_suffix_035, ridgeSupport896_suffix_036, ridgeSupport896_suffix_037, ridgeSupport896_suffix_038, ridgeSupport896_suffix_039, ridgeSupport896_suffix_040, ridgeSupport896_suffix_041, ridgeSupport896_suffix_042, ridgeSupport896_suffix_043, ridgeSupport896_suffix_044, ridgeSupport896_suffix_045, ridgeSupport896_suffix_046, ridgeSupport896_suffix_047, List.all_append, List.all_nil, ridgeSupport896_000_checked, ridgeSupport896_001_checked, ridgeSupport896_002_checked, ridgeSupport896_003_checked, ridgeSupport896_004_checked, ridgeSupport896_005_checked, ridgeSupport896_006_checked, ridgeSupport896_007_checked, ridgeSupport896_008_checked, ridgeSupport896_009_checked, ridgeSupport896_010_checked, ridgeSupport896_011_checked, ridgeSupport896_012_checked, ridgeSupport896_013_checked, ridgeSupport896_014_checked, ridgeSupport896_015_checked, ridgeSupport896_016_checked, ridgeSupport896_017_checked, ridgeSupport896_018_checked, ridgeSupport896_019_checked, ridgeSupport896_020_checked, ridgeSupport896_021_checked, ridgeSupport896_022_checked, ridgeSupport896_023_checked, ridgeSupport896_024_checked, ridgeSupport896_025_checked, ridgeSupport896_026_checked, ridgeSupport896_027_checked, ridgeSupport896_028_checked, ridgeSupport896_029_checked, ridgeSupport896_030_checked, ridgeSupport896_031_checked, ridgeSupport896_032_checked, ridgeSupport896_033_checked, ridgeSupport896_034_checked, ridgeSupport896_035_checked, ridgeSupport896_036_checked, ridgeSupport896_037_checked, ridgeSupport896_038_checked, ridgeSupport896_039_checked, ridgeSupport896_040_checked, ridgeSupport896_041_checked, ridgeSupport896_042_checked, ridgeSupport896_043_checked, ridgeSupport896_044_checked, ridgeSupport896_045_checked, ridgeSupport896_046_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixExtra00
