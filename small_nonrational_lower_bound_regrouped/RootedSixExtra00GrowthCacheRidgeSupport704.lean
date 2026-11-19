module
prelude
public meta import LowerSchemas.FiniteRootedSixExtra
public import BundledChecks.RootedSixExtra00GrowthCacheRidgeSupport704Batch000
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra00
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
cert_ridgeSupport_suffix_decode_3 704 047 14
cert_ridgeSupport_suffix_decode_4 704 046 14 23 23 047 047 0
cert_ridgeSupport_suffix_decode_4 704 045 14 55 32 047 046 23
cert_ridgeSupport_suffix_decode_4 704 044 14 87 32 047 045 55
cert_ridgeSupport_suffix_decode_4 704 043 14 119 32 047 044 87
cert_ridgeSupport_suffix_decode_4 704 042 14 151 32 047 043 119
cert_ridgeSupport_suffix_decode_4 704 041 14 183 32 047 042 151
cert_ridgeSupport_suffix_decode_4 704 040 14 215 32 047 041 183
cert_ridgeSupport_suffix_decode_4 704 039 14 247 32 047 040 215
cert_ridgeSupport_suffix_decode_4 704 038 14 279 32 047 039 247
cert_ridgeSupport_suffix_decode_4 704 037 14 311 32 047 038 279
cert_ridgeSupport_suffix_decode_4 704 036 14 343 32 047 037 311
cert_ridgeSupport_suffix_decode_4 704 035 14 375 32 047 036 343
cert_ridgeSupport_suffix_decode_4 704 034 14 407 32 047 035 375
cert_ridgeSupport_suffix_decode_4 704 033 14 439 32 047 034 407
cert_ridgeSupport_suffix_decode_4 704 032 14 471 32 047 033 439
cert_ridgeSupport_suffix_decode_4 704 031 14 503 32 047 032 471
cert_ridgeSupport_suffix_decode_4 704 030 14 535 32 047 031 503
cert_ridgeSupport_suffix_decode_4 704 029 14 567 32 047 030 535
cert_ridgeSupport_suffix_decode_4 704 028 14 599 32 047 029 567
cert_ridgeSupport_suffix_decode_4 704 027 14 631 32 047 028 599
cert_ridgeSupport_suffix_decode_4 704 026 14 663 32 047 027 631
cert_ridgeSupport_suffix_decode_4 704 025 14 695 32 047 026 663
cert_ridgeSupport_suffix_decode_4 704 024 14 727 32 047 025 695
cert_ridgeSupport_suffix_decode_4 704 023 14 759 32 047 024 727
cert_ridgeSupport_suffix_decode_4 704 022 14 791 32 047 023 759
cert_ridgeSupport_suffix_decode_4 704 021 14 823 32 047 022 791
cert_ridgeSupport_suffix_decode_4 704 020 14 855 32 047 021 823
cert_ridgeSupport_suffix_decode_4 704 019 14 887 32 047 020 855
cert_ridgeSupport_suffix_decode_4 704 018 14 919 32 047 019 887
cert_ridgeSupport_suffix_decode_4 704 017 14 951 32 047 018 919
cert_ridgeSupport_suffix_decode_4 704 016 14 983 32 047 017 951
cert_ridgeSupport_suffix_decode_4 704 015 14 1015 32 047 016 983
cert_ridgeSupport_suffix_decode_4 704 014 14 1047 32 047 015 1015
cert_ridgeSupport_suffix_decode_4 704 013 14 1079 32 047 014 1047
cert_ridgeSupport_suffix_decode_4 704 012 14 1111 32 047 013 1079
cert_ridgeSupport_suffix_decode_4 704 011 14 1143 32 047 012 1111
cert_ridgeSupport_suffix_decode_4 704 010 14 1175 32 047 011 1143
cert_ridgeSupport_suffix_decode_4 704 009 14 1207 32 047 010 1175
cert_ridgeSupport_suffix_decode_4 704 008 14 1239 32 047 009 1207
cert_ridgeSupport_suffix_decode_4 704 007 14 1271 32 047 008 1239
cert_ridgeSupport_suffix_decode_4 704 006 14 1303 32 047 007 1271
cert_ridgeSupport_suffix_decode_4 704 005 14 1335 32 047 006 1303
cert_ridgeSupport_suffix_decode_4 704 004 14 1367 32 047 005 1335
cert_ridgeSupport_suffix_decode_4 704 003 14 1399 32 047 004 1367
cert_ridgeSupport_suffix_decode_4 704 002 14 1431 32 047 003 1399
cert_ridgeSupport_suffix_decode_4 704 001 14 1463 32 047 002 1431
cert_ridgeSupport_suffix_decode_4 704 000 14 1495 32 047 001 1463
cert_ridgeSupport_eq_4 704
theorem ridgeTest_large_704 : ridgeTest 704 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport704_eq]
    simp only [ridgeSupport704_suffix_000, ridgeSupport704_suffix_001, ridgeSupport704_suffix_002, ridgeSupport704_suffix_003, ridgeSupport704_suffix_004, ridgeSupport704_suffix_005, ridgeSupport704_suffix_006, ridgeSupport704_suffix_007, ridgeSupport704_suffix_008, ridgeSupport704_suffix_009, ridgeSupport704_suffix_010, ridgeSupport704_suffix_011, ridgeSupport704_suffix_012, ridgeSupport704_suffix_013, ridgeSupport704_suffix_014, ridgeSupport704_suffix_015, ridgeSupport704_suffix_016, ridgeSupport704_suffix_017, ridgeSupport704_suffix_018, ridgeSupport704_suffix_019, ridgeSupport704_suffix_020, ridgeSupport704_suffix_021, ridgeSupport704_suffix_022, ridgeSupport704_suffix_023, ridgeSupport704_suffix_024, ridgeSupport704_suffix_025, ridgeSupport704_suffix_026, ridgeSupport704_suffix_027, ridgeSupport704_suffix_028, ridgeSupport704_suffix_029, ridgeSupport704_suffix_030, ridgeSupport704_suffix_031, ridgeSupport704_suffix_032, ridgeSupport704_suffix_033, ridgeSupport704_suffix_034, ridgeSupport704_suffix_035, ridgeSupport704_suffix_036, ridgeSupport704_suffix_037, ridgeSupport704_suffix_038, ridgeSupport704_suffix_039, ridgeSupport704_suffix_040, ridgeSupport704_suffix_041, ridgeSupport704_suffix_042, ridgeSupport704_suffix_043, ridgeSupport704_suffix_044, ridgeSupport704_suffix_045, ridgeSupport704_suffix_046, ridgeSupport704_suffix_047, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport704_000_mask, ridgeSupport704_001_mask, ridgeSupport704_002_mask, ridgeSupport704_003_mask, ridgeSupport704_004_mask, ridgeSupport704_005_mask, ridgeSupport704_006_mask, ridgeSupport704_007_mask, ridgeSupport704_008_mask, ridgeSupport704_009_mask, ridgeSupport704_010_mask, ridgeSupport704_011_mask, ridgeSupport704_012_mask, ridgeSupport704_013_mask, ridgeSupport704_014_mask, ridgeSupport704_015_mask, ridgeSupport704_016_mask, ridgeSupport704_017_mask, ridgeSupport704_018_mask, ridgeSupport704_019_mask, ridgeSupport704_020_mask, ridgeSupport704_021_mask, ridgeSupport704_022_mask, ridgeSupport704_023_mask, ridgeSupport704_024_mask, ridgeSupport704_025_mask, ridgeSupport704_026_mask, ridgeSupport704_027_mask, ridgeSupport704_028_mask, ridgeSupport704_029_mask, ridgeSupport704_030_mask, ridgeSupport704_031_mask, ridgeSupport704_032_mask, ridgeSupport704_033_mask, ridgeSupport704_034_mask, ridgeSupport704_035_mask, ridgeSupport704_036_mask, ridgeSupport704_037_mask, ridgeSupport704_038_mask, ridgeSupport704_039_mask, ridgeSupport704_040_mask, ridgeSupport704_041_mask, ridgeSupport704_042_mask, ridgeSupport704_043_mask, ridgeSupport704_044_mask, ridgeSupport704_045_mask, ridgeSupport704_046_mask]
    decide +kernel
  · rw [ridgeSupport704_eq]
    simp only [ridgeSupport704_suffix_000, ridgeSupport704_suffix_001, ridgeSupport704_suffix_002, ridgeSupport704_suffix_003, ridgeSupport704_suffix_004, ridgeSupport704_suffix_005, ridgeSupport704_suffix_006, ridgeSupport704_suffix_007, ridgeSupport704_suffix_008, ridgeSupport704_suffix_009, ridgeSupport704_suffix_010, ridgeSupport704_suffix_011, ridgeSupport704_suffix_012, ridgeSupport704_suffix_013, ridgeSupport704_suffix_014, ridgeSupport704_suffix_015, ridgeSupport704_suffix_016, ridgeSupport704_suffix_017, ridgeSupport704_suffix_018, ridgeSupport704_suffix_019, ridgeSupport704_suffix_020, ridgeSupport704_suffix_021, ridgeSupport704_suffix_022, ridgeSupport704_suffix_023, ridgeSupport704_suffix_024, ridgeSupport704_suffix_025, ridgeSupport704_suffix_026, ridgeSupport704_suffix_027, ridgeSupport704_suffix_028, ridgeSupport704_suffix_029, ridgeSupport704_suffix_030, ridgeSupport704_suffix_031, ridgeSupport704_suffix_032, ridgeSupport704_suffix_033, ridgeSupport704_suffix_034, ridgeSupport704_suffix_035, ridgeSupport704_suffix_036, ridgeSupport704_suffix_037, ridgeSupport704_suffix_038, ridgeSupport704_suffix_039, ridgeSupport704_suffix_040, ridgeSupport704_suffix_041, ridgeSupport704_suffix_042, ridgeSupport704_suffix_043, ridgeSupport704_suffix_044, ridgeSupport704_suffix_045, ridgeSupport704_suffix_046, ridgeSupport704_suffix_047, List.all_append, List.all_nil, ridgeSupport704_000_checked, ridgeSupport704_001_checked, ridgeSupport704_002_checked, ridgeSupport704_003_checked, ridgeSupport704_004_checked, ridgeSupport704_005_checked, ridgeSupport704_006_checked, ridgeSupport704_007_checked, ridgeSupport704_008_checked, ridgeSupport704_009_checked, ridgeSupport704_010_checked, ridgeSupport704_011_checked, ridgeSupport704_012_checked, ridgeSupport704_013_checked, ridgeSupport704_014_checked, ridgeSupport704_015_checked, ridgeSupport704_016_checked, ridgeSupport704_017_checked, ridgeSupport704_018_checked, ridgeSupport704_019_checked, ridgeSupport704_020_checked, ridgeSupport704_021_checked, ridgeSupport704_022_checked, ridgeSupport704_023_checked, ridgeSupport704_024_checked, ridgeSupport704_025_checked, ridgeSupport704_026_checked, ridgeSupport704_027_checked, ridgeSupport704_028_checked, ridgeSupport704_029_checked, ridgeSupport704_030_checked, ridgeSupport704_031_checked, ridgeSupport704_032_checked, ridgeSupport704_033_checked, ridgeSupport704_034_checked, ridgeSupport704_035_checked, ridgeSupport704_036_checked, ridgeSupport704_037_checked, ridgeSupport704_038_checked, ridgeSupport704_039_checked, ridgeSupport704_040_checked, ridgeSupport704_041_checked, ridgeSupport704_042_checked, ridgeSupport704_043_checked, ridgeSupport704_044_checked, ridgeSupport704_045_checked, ridgeSupport704_046_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixExtra00
