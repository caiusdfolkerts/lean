module
prelude
public meta import LowerSchemas.FiniteRootedSixExtra
public import BundledChecks.RootedSixExtra00GrowthCacheRidgeSupport832Batch000
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra00
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
cert_ridgeSupport_suffix_decode_3 832 047 14
cert_ridgeSupport_suffix_decode_4 832 046 14 23 23 047 047 0
cert_ridgeSupport_suffix_decode_4 832 045 14 55 32 047 046 23
cert_ridgeSupport_suffix_decode_4 832 044 14 87 32 047 045 55
cert_ridgeSupport_suffix_decode_4 832 043 14 119 32 047 044 87
cert_ridgeSupport_suffix_decode_4 832 042 14 151 32 047 043 119
cert_ridgeSupport_suffix_decode_4 832 041 14 183 32 047 042 151
cert_ridgeSupport_suffix_decode_4 832 040 14 215 32 047 041 183
cert_ridgeSupport_suffix_decode_4 832 039 14 247 32 047 040 215
cert_ridgeSupport_suffix_decode_4 832 038 14 279 32 047 039 247
cert_ridgeSupport_suffix_decode_4 832 037 14 311 32 047 038 279
cert_ridgeSupport_suffix_decode_4 832 036 14 343 32 047 037 311
cert_ridgeSupport_suffix_decode_4 832 035 14 375 32 047 036 343
cert_ridgeSupport_suffix_decode_4 832 034 14 407 32 047 035 375
cert_ridgeSupport_suffix_decode_4 832 033 14 439 32 047 034 407
cert_ridgeSupport_suffix_decode_4 832 032 14 471 32 047 033 439
cert_ridgeSupport_suffix_decode_4 832 031 14 503 32 047 032 471
cert_ridgeSupport_suffix_decode_4 832 030 14 535 32 047 031 503
cert_ridgeSupport_suffix_decode_4 832 029 14 567 32 047 030 535
cert_ridgeSupport_suffix_decode_4 832 028 14 599 32 047 029 567
cert_ridgeSupport_suffix_decode_4 832 027 14 631 32 047 028 599
cert_ridgeSupport_suffix_decode_4 832 026 14 663 32 047 027 631
cert_ridgeSupport_suffix_decode_4 832 025 14 695 32 047 026 663
cert_ridgeSupport_suffix_decode_4 832 024 14 727 32 047 025 695
cert_ridgeSupport_suffix_decode_4 832 023 14 759 32 047 024 727
cert_ridgeSupport_suffix_decode_4 832 022 14 791 32 047 023 759
cert_ridgeSupport_suffix_decode_4 832 021 14 823 32 047 022 791
cert_ridgeSupport_suffix_decode_4 832 020 14 855 32 047 021 823
cert_ridgeSupport_suffix_decode_4 832 019 14 887 32 047 020 855
cert_ridgeSupport_suffix_decode_4 832 018 14 919 32 047 019 887
cert_ridgeSupport_suffix_decode_4 832 017 14 951 32 047 018 919
cert_ridgeSupport_suffix_decode_4 832 016 14 983 32 047 017 951
cert_ridgeSupport_suffix_decode_4 832 015 14 1015 32 047 016 983
cert_ridgeSupport_suffix_decode_4 832 014 14 1047 32 047 015 1015
cert_ridgeSupport_suffix_decode_4 832 013 14 1079 32 047 014 1047
cert_ridgeSupport_suffix_decode_4 832 012 14 1111 32 047 013 1079
cert_ridgeSupport_suffix_decode_4 832 011 14 1143 32 047 012 1111
cert_ridgeSupport_suffix_decode_4 832 010 14 1175 32 047 011 1143
cert_ridgeSupport_suffix_decode_4 832 009 14 1207 32 047 010 1175
cert_ridgeSupport_suffix_decode_4 832 008 14 1239 32 047 009 1207
cert_ridgeSupport_suffix_decode_4 832 007 14 1271 32 047 008 1239
cert_ridgeSupport_suffix_decode_4 832 006 14 1303 32 047 007 1271
cert_ridgeSupport_suffix_decode_4 832 005 14 1335 32 047 006 1303
cert_ridgeSupport_suffix_decode_4 832 004 14 1367 32 047 005 1335
cert_ridgeSupport_suffix_decode_4 832 003 14 1399 32 047 004 1367
cert_ridgeSupport_suffix_decode_4 832 002 14 1431 32 047 003 1399
cert_ridgeSupport_suffix_decode_4 832 001 14 1463 32 047 002 1431
cert_ridgeSupport_suffix_decode_4 832 000 14 1495 32 047 001 1463
cert_ridgeSupport_eq_4 832
theorem ridgeTest_large_832 : ridgeTest 832 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport832_eq]
    simp only [ridgeSupport832_suffix_000, ridgeSupport832_suffix_001, ridgeSupport832_suffix_002, ridgeSupport832_suffix_003, ridgeSupport832_suffix_004, ridgeSupport832_suffix_005, ridgeSupport832_suffix_006, ridgeSupport832_suffix_007, ridgeSupport832_suffix_008, ridgeSupport832_suffix_009, ridgeSupport832_suffix_010, ridgeSupport832_suffix_011, ridgeSupport832_suffix_012, ridgeSupport832_suffix_013, ridgeSupport832_suffix_014, ridgeSupport832_suffix_015, ridgeSupport832_suffix_016, ridgeSupport832_suffix_017, ridgeSupport832_suffix_018, ridgeSupport832_suffix_019, ridgeSupport832_suffix_020, ridgeSupport832_suffix_021, ridgeSupport832_suffix_022, ridgeSupport832_suffix_023, ridgeSupport832_suffix_024, ridgeSupport832_suffix_025, ridgeSupport832_suffix_026, ridgeSupport832_suffix_027, ridgeSupport832_suffix_028, ridgeSupport832_suffix_029, ridgeSupport832_suffix_030, ridgeSupport832_suffix_031, ridgeSupport832_suffix_032, ridgeSupport832_suffix_033, ridgeSupport832_suffix_034, ridgeSupport832_suffix_035, ridgeSupport832_suffix_036, ridgeSupport832_suffix_037, ridgeSupport832_suffix_038, ridgeSupport832_suffix_039, ridgeSupport832_suffix_040, ridgeSupport832_suffix_041, ridgeSupport832_suffix_042, ridgeSupport832_suffix_043, ridgeSupport832_suffix_044, ridgeSupport832_suffix_045, ridgeSupport832_suffix_046, ridgeSupport832_suffix_047, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport832_000_mask, ridgeSupport832_001_mask, ridgeSupport832_002_mask, ridgeSupport832_003_mask, ridgeSupport832_004_mask, ridgeSupport832_005_mask, ridgeSupport832_006_mask, ridgeSupport832_007_mask, ridgeSupport832_008_mask, ridgeSupport832_009_mask, ridgeSupport832_010_mask, ridgeSupport832_011_mask, ridgeSupport832_012_mask, ridgeSupport832_013_mask, ridgeSupport832_014_mask, ridgeSupport832_015_mask, ridgeSupport832_016_mask, ridgeSupport832_017_mask, ridgeSupport832_018_mask, ridgeSupport832_019_mask, ridgeSupport832_020_mask, ridgeSupport832_021_mask, ridgeSupport832_022_mask, ridgeSupport832_023_mask, ridgeSupport832_024_mask, ridgeSupport832_025_mask, ridgeSupport832_026_mask, ridgeSupport832_027_mask, ridgeSupport832_028_mask, ridgeSupport832_029_mask, ridgeSupport832_030_mask, ridgeSupport832_031_mask, ridgeSupport832_032_mask, ridgeSupport832_033_mask, ridgeSupport832_034_mask, ridgeSupport832_035_mask, ridgeSupport832_036_mask, ridgeSupport832_037_mask, ridgeSupport832_038_mask, ridgeSupport832_039_mask, ridgeSupport832_040_mask, ridgeSupport832_041_mask, ridgeSupport832_042_mask, ridgeSupport832_043_mask, ridgeSupport832_044_mask, ridgeSupport832_045_mask, ridgeSupport832_046_mask]
    decide +kernel
  · rw [ridgeSupport832_eq]
    simp only [ridgeSupport832_suffix_000, ridgeSupport832_suffix_001, ridgeSupport832_suffix_002, ridgeSupport832_suffix_003, ridgeSupport832_suffix_004, ridgeSupport832_suffix_005, ridgeSupport832_suffix_006, ridgeSupport832_suffix_007, ridgeSupport832_suffix_008, ridgeSupport832_suffix_009, ridgeSupport832_suffix_010, ridgeSupport832_suffix_011, ridgeSupport832_suffix_012, ridgeSupport832_suffix_013, ridgeSupport832_suffix_014, ridgeSupport832_suffix_015, ridgeSupport832_suffix_016, ridgeSupport832_suffix_017, ridgeSupport832_suffix_018, ridgeSupport832_suffix_019, ridgeSupport832_suffix_020, ridgeSupport832_suffix_021, ridgeSupport832_suffix_022, ridgeSupport832_suffix_023, ridgeSupport832_suffix_024, ridgeSupport832_suffix_025, ridgeSupport832_suffix_026, ridgeSupport832_suffix_027, ridgeSupport832_suffix_028, ridgeSupport832_suffix_029, ridgeSupport832_suffix_030, ridgeSupport832_suffix_031, ridgeSupport832_suffix_032, ridgeSupport832_suffix_033, ridgeSupport832_suffix_034, ridgeSupport832_suffix_035, ridgeSupport832_suffix_036, ridgeSupport832_suffix_037, ridgeSupport832_suffix_038, ridgeSupport832_suffix_039, ridgeSupport832_suffix_040, ridgeSupport832_suffix_041, ridgeSupport832_suffix_042, ridgeSupport832_suffix_043, ridgeSupport832_suffix_044, ridgeSupport832_suffix_045, ridgeSupport832_suffix_046, ridgeSupport832_suffix_047, List.all_append, List.all_nil, ridgeSupport832_000_checked, ridgeSupport832_001_checked, ridgeSupport832_002_checked, ridgeSupport832_003_checked, ridgeSupport832_004_checked, ridgeSupport832_005_checked, ridgeSupport832_006_checked, ridgeSupport832_007_checked, ridgeSupport832_008_checked, ridgeSupport832_009_checked, ridgeSupport832_010_checked, ridgeSupport832_011_checked, ridgeSupport832_012_checked, ridgeSupport832_013_checked, ridgeSupport832_014_checked, ridgeSupport832_015_checked, ridgeSupport832_016_checked, ridgeSupport832_017_checked, ridgeSupport832_018_checked, ridgeSupport832_019_checked, ridgeSupport832_020_checked, ridgeSupport832_021_checked, ridgeSupport832_022_checked, ridgeSupport832_023_checked, ridgeSupport832_024_checked, ridgeSupport832_025_checked, ridgeSupport832_026_checked, ridgeSupport832_027_checked, ridgeSupport832_028_checked, ridgeSupport832_029_checked, ridgeSupport832_030_checked, ridgeSupport832_031_checked, ridgeSupport832_032_checked, ridgeSupport832_033_checked, ridgeSupport832_034_checked, ridgeSupport832_035_checked, ridgeSupport832_036_checked, ridgeSupport832_037_checked, ridgeSupport832_038_checked, ridgeSupport832_039_checked, ridgeSupport832_040_checked, ridgeSupport832_041_checked, ridgeSupport832_042_checked, ridgeSupport832_043_checked, ridgeSupport832_044_checked, ridgeSupport832_045_checked, ridgeSupport832_046_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixExtra00
