module
prelude
public meta import LowerSchemas.FiniteRootedSixBase
public import BundledChecks.RootedSixBase02GrowthCacheRidgeSupport448Batch000
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase02
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
cert_ridgeSupport_suffix_decode 448 055 13
cert_ridgeSupport_suffix_decode_2 448 054 13 7 7 055 055 0
cert_ridgeSupport_suffix_decode_2 448 053 13 39 32 055 054 7
cert_ridgeSupport_suffix_decode_2 448 052 13 71 32 055 053 39
cert_ridgeSupport_suffix_decode_2 448 051 13 103 32 055 052 71
cert_ridgeSupport_suffix_decode_2 448 050 13 135 32 055 051 103
cert_ridgeSupport_suffix_decode_2 448 049 13 167 32 055 050 135
cert_ridgeSupport_suffix_decode_2 448 048 13 199 32 055 049 167
cert_ridgeSupport_suffix_decode_2 448 047 13 231 32 055 048 199
cert_ridgeSupport_suffix_decode_2 448 046 13 263 32 055 047 231
cert_ridgeSupport_suffix_decode_2 448 045 13 295 32 055 046 263
cert_ridgeSupport_suffix_decode_2 448 044 13 327 32 055 045 295
cert_ridgeSupport_suffix_decode_2 448 043 13 359 32 055 044 327
cert_ridgeSupport_suffix_decode_2 448 042 13 391 32 055 043 359
cert_ridgeSupport_suffix_decode_2 448 041 13 423 32 055 042 391
cert_ridgeSupport_suffix_decode_2 448 040 13 455 32 055 041 423
cert_ridgeSupport_suffix_decode_2 448 039 13 487 32 055 040 455
cert_ridgeSupport_suffix_decode_2 448 038 13 519 32 055 039 487
cert_ridgeSupport_suffix_decode_2 448 037 13 551 32 055 038 519
cert_ridgeSupport_suffix_decode_2 448 036 13 583 32 055 037 551
cert_ridgeSupport_suffix_decode_2 448 035 13 615 32 055 036 583
cert_ridgeSupport_suffix_decode_2 448 034 13 647 32 055 035 615
cert_ridgeSupport_suffix_decode_2 448 033 13 679 32 055 034 647
cert_ridgeSupport_suffix_decode_2 448 032 13 711 32 055 033 679
cert_ridgeSupport_suffix_decode_2 448 031 13 743 32 055 032 711
cert_ridgeSupport_suffix_decode_2 448 030 13 775 32 055 031 743
cert_ridgeSupport_suffix_decode_2 448 029 13 807 32 055 030 775
cert_ridgeSupport_suffix_decode_2 448 028 13 839 32 055 029 807
cert_ridgeSupport_suffix_decode_2 448 027 13 871 32 055 028 839
cert_ridgeSupport_suffix_decode_2 448 026 13 903 32 055 027 871
cert_ridgeSupport_suffix_decode_2 448 025 13 935 32 055 026 903
cert_ridgeSupport_suffix_decode_2 448 024 13 967 32 055 025 935
cert_ridgeSupport_suffix_decode_2 448 023 13 999 32 055 024 967
cert_ridgeSupport_suffix_decode_2 448 022 13 1031 32 055 023 999
cert_ridgeSupport_suffix_decode_2 448 021 13 1063 32 055 022 1031
cert_ridgeSupport_suffix_decode_2 448 020 13 1095 32 055 021 1063
cert_ridgeSupport_suffix_decode_2 448 019 13 1127 32 055 020 1095
cert_ridgeSupport_suffix_decode_2 448 018 13 1159 32 055 019 1127
cert_ridgeSupport_suffix_decode_2 448 017 13 1191 32 055 018 1159
cert_ridgeSupport_suffix_decode_2 448 016 13 1223 32 055 017 1191
cert_ridgeSupport_suffix_decode_2 448 015 13 1255 32 055 016 1223
cert_ridgeSupport_suffix_decode_2 448 014 13 1287 32 055 015 1255
cert_ridgeSupport_suffix_decode_2 448 013 13 1319 32 055 014 1287
cert_ridgeSupport_suffix_decode_2 448 012 13 1351 32 055 013 1319
cert_ridgeSupport_suffix_decode_2 448 011 13 1383 32 055 012 1351
cert_ridgeSupport_suffix_decode_2 448 010 13 1415 32 055 011 1383
cert_ridgeSupport_suffix_decode_2 448 009 13 1447 32 055 010 1415
cert_ridgeSupport_suffix_decode_2 448 008 13 1479 32 055 009 1447
cert_ridgeSupport_suffix_decode_2 448 007 13 1511 32 055 008 1479
cert_ridgeSupport_suffix_decode_2 448 006 13 1543 32 055 007 1511
cert_ridgeSupport_suffix_decode_2 448 005 13 1575 32 055 006 1543
cert_ridgeSupport_suffix_decode_2 448 004 13 1607 32 055 005 1575
cert_ridgeSupport_suffix_decode_2 448 003 13 1639 32 055 004 1607
cert_ridgeSupport_suffix_decode_2 448 002 13 1671 32 055 003 1639
cert_ridgeSupport_suffix_decode_2 448 001 13 1703 32 055 002 1671
cert_ridgeSupport_suffix_decode_2 448 000 13 1735 32 055 001 1703
cert_ridgeSupport_eq 448
theorem ridgeTest_large_448 : ridgeTest 448 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport448_eq]
    simp only [ridgeSupport448_suffix_000, ridgeSupport448_suffix_001, ridgeSupport448_suffix_002, ridgeSupport448_suffix_003, ridgeSupport448_suffix_004, ridgeSupport448_suffix_005, ridgeSupport448_suffix_006, ridgeSupport448_suffix_007, ridgeSupport448_suffix_008, ridgeSupport448_suffix_009, ridgeSupport448_suffix_010, ridgeSupport448_suffix_011, ridgeSupport448_suffix_012, ridgeSupport448_suffix_013, ridgeSupport448_suffix_014, ridgeSupport448_suffix_015, ridgeSupport448_suffix_016, ridgeSupport448_suffix_017, ridgeSupport448_suffix_018, ridgeSupport448_suffix_019, ridgeSupport448_suffix_020, ridgeSupport448_suffix_021, ridgeSupport448_suffix_022, ridgeSupport448_suffix_023, ridgeSupport448_suffix_024, ridgeSupport448_suffix_025, ridgeSupport448_suffix_026, ridgeSupport448_suffix_027, ridgeSupport448_suffix_028, ridgeSupport448_suffix_029, ridgeSupport448_suffix_030, ridgeSupport448_suffix_031, ridgeSupport448_suffix_032, ridgeSupport448_suffix_033, ridgeSupport448_suffix_034, ridgeSupport448_suffix_035, ridgeSupport448_suffix_036, ridgeSupport448_suffix_037, ridgeSupport448_suffix_038, ridgeSupport448_suffix_039, ridgeSupport448_suffix_040, ridgeSupport448_suffix_041, ridgeSupport448_suffix_042, ridgeSupport448_suffix_043, ridgeSupport448_suffix_044, ridgeSupport448_suffix_045, ridgeSupport448_suffix_046, ridgeSupport448_suffix_047, ridgeSupport448_suffix_048, ridgeSupport448_suffix_049, ridgeSupport448_suffix_050, ridgeSupport448_suffix_051, ridgeSupport448_suffix_052, ridgeSupport448_suffix_053, ridgeSupport448_suffix_054, ridgeSupport448_suffix_055, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport448_000_mask, ridgeSupport448_001_mask, ridgeSupport448_002_mask, ridgeSupport448_003_mask, ridgeSupport448_004_mask, ridgeSupport448_005_mask, ridgeSupport448_006_mask, ridgeSupport448_007_mask, ridgeSupport448_008_mask, ridgeSupport448_009_mask, ridgeSupport448_010_mask, ridgeSupport448_011_mask, ridgeSupport448_012_mask, ridgeSupport448_013_mask, ridgeSupport448_014_mask, ridgeSupport448_015_mask, ridgeSupport448_016_mask, ridgeSupport448_017_mask, ridgeSupport448_018_mask, ridgeSupport448_019_mask, ridgeSupport448_020_mask, ridgeSupport448_021_mask, ridgeSupport448_022_mask, ridgeSupport448_023_mask, ridgeSupport448_024_mask, ridgeSupport448_025_mask, ridgeSupport448_026_mask, ridgeSupport448_027_mask, ridgeSupport448_028_mask, ridgeSupport448_029_mask, ridgeSupport448_030_mask, ridgeSupport448_031_mask, ridgeSupport448_032_mask, ridgeSupport448_033_mask, ridgeSupport448_034_mask, ridgeSupport448_035_mask, ridgeSupport448_036_mask, ridgeSupport448_037_mask, ridgeSupport448_038_mask, ridgeSupport448_039_mask, ridgeSupport448_040_mask, ridgeSupport448_041_mask, ridgeSupport448_042_mask, ridgeSupport448_043_mask, ridgeSupport448_044_mask, ridgeSupport448_045_mask, ridgeSupport448_046_mask, ridgeSupport448_047_mask, ridgeSupport448_048_mask, ridgeSupport448_049_mask, ridgeSupport448_050_mask, ridgeSupport448_051_mask, ridgeSupport448_052_mask, ridgeSupport448_053_mask, ridgeSupport448_054_mask]
    decide +kernel
  · rw [ridgeSupport448_eq]
    simp only [ridgeSupport448_suffix_000, ridgeSupport448_suffix_001, ridgeSupport448_suffix_002, ridgeSupport448_suffix_003, ridgeSupport448_suffix_004, ridgeSupport448_suffix_005, ridgeSupport448_suffix_006, ridgeSupport448_suffix_007, ridgeSupport448_suffix_008, ridgeSupport448_suffix_009, ridgeSupport448_suffix_010, ridgeSupport448_suffix_011, ridgeSupport448_suffix_012, ridgeSupport448_suffix_013, ridgeSupport448_suffix_014, ridgeSupport448_suffix_015, ridgeSupport448_suffix_016, ridgeSupport448_suffix_017, ridgeSupport448_suffix_018, ridgeSupport448_suffix_019, ridgeSupport448_suffix_020, ridgeSupport448_suffix_021, ridgeSupport448_suffix_022, ridgeSupport448_suffix_023, ridgeSupport448_suffix_024, ridgeSupport448_suffix_025, ridgeSupport448_suffix_026, ridgeSupport448_suffix_027, ridgeSupport448_suffix_028, ridgeSupport448_suffix_029, ridgeSupport448_suffix_030, ridgeSupport448_suffix_031, ridgeSupport448_suffix_032, ridgeSupport448_suffix_033, ridgeSupport448_suffix_034, ridgeSupport448_suffix_035, ridgeSupport448_suffix_036, ridgeSupport448_suffix_037, ridgeSupport448_suffix_038, ridgeSupport448_suffix_039, ridgeSupport448_suffix_040, ridgeSupport448_suffix_041, ridgeSupport448_suffix_042, ridgeSupport448_suffix_043, ridgeSupport448_suffix_044, ridgeSupport448_suffix_045, ridgeSupport448_suffix_046, ridgeSupport448_suffix_047, ridgeSupport448_suffix_048, ridgeSupport448_suffix_049, ridgeSupport448_suffix_050, ridgeSupport448_suffix_051, ridgeSupport448_suffix_052, ridgeSupport448_suffix_053, ridgeSupport448_suffix_054, ridgeSupport448_suffix_055, List.all_append, List.all_nil, ridgeSupport448_000_checked, ridgeSupport448_001_checked, ridgeSupport448_002_checked, ridgeSupport448_003_checked, ridgeSupport448_004_checked, ridgeSupport448_005_checked, ridgeSupport448_006_checked, ridgeSupport448_007_checked, ridgeSupport448_008_checked, ridgeSupport448_009_checked, ridgeSupport448_010_checked, ridgeSupport448_011_checked, ridgeSupport448_012_checked, ridgeSupport448_013_checked, ridgeSupport448_014_checked, ridgeSupport448_015_checked, ridgeSupport448_016_checked, ridgeSupport448_017_checked, ridgeSupport448_018_checked, ridgeSupport448_019_checked, ridgeSupport448_020_checked, ridgeSupport448_021_checked, ridgeSupport448_022_checked, ridgeSupport448_023_checked, ridgeSupport448_024_checked, ridgeSupport448_025_checked, ridgeSupport448_026_checked, ridgeSupport448_027_checked, ridgeSupport448_028_checked, ridgeSupport448_029_checked, ridgeSupport448_030_checked, ridgeSupport448_031_checked, ridgeSupport448_032_checked, ridgeSupport448_033_checked, ridgeSupport448_034_checked, ridgeSupport448_035_checked, ridgeSupport448_036_checked, ridgeSupport448_037_checked, ridgeSupport448_038_checked, ridgeSupport448_039_checked, ridgeSupport448_040_checked, ridgeSupport448_041_checked, ridgeSupport448_042_checked, ridgeSupport448_043_checked, ridgeSupport448_044_checked, ridgeSupport448_045_checked, ridgeSupport448_046_checked, ridgeSupport448_047_checked, ridgeSupport448_048_checked, ridgeSupport448_049_checked, ridgeSupport448_050_checked, ridgeSupport448_051_checked, ridgeSupport448_052_checked, ridgeSupport448_053_checked, ridgeSupport448_054_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase02
