module
prelude
public meta import LowerSchemas.FiniteRootedSixBase
public import BundledChecks.RootedSixBase02GrowthCacheRidgeSupport704Batch000
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase02
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
cert_ridgeSupport_suffix_decode 704 055 13
cert_ridgeSupport_suffix_decode_2 704 054 13 7 7 055 055 0
cert_ridgeSupport_suffix_decode_2 704 053 13 39 32 055 054 7
cert_ridgeSupport_suffix_decode_2 704 052 13 71 32 055 053 39
cert_ridgeSupport_suffix_decode_2 704 051 13 103 32 055 052 71
cert_ridgeSupport_suffix_decode_2 704 050 13 135 32 055 051 103
cert_ridgeSupport_suffix_decode_2 704 049 13 167 32 055 050 135
cert_ridgeSupport_suffix_decode_2 704 048 13 199 32 055 049 167
cert_ridgeSupport_suffix_decode_2 704 047 13 231 32 055 048 199
cert_ridgeSupport_suffix_decode_2 704 046 13 263 32 055 047 231
cert_ridgeSupport_suffix_decode_2 704 045 13 295 32 055 046 263
cert_ridgeSupport_suffix_decode_2 704 044 13 327 32 055 045 295
cert_ridgeSupport_suffix_decode_2 704 043 13 359 32 055 044 327
cert_ridgeSupport_suffix_decode_2 704 042 13 391 32 055 043 359
cert_ridgeSupport_suffix_decode_2 704 041 13 423 32 055 042 391
cert_ridgeSupport_suffix_decode_2 704 040 13 455 32 055 041 423
cert_ridgeSupport_suffix_decode_2 704 039 13 487 32 055 040 455
cert_ridgeSupport_suffix_decode_2 704 038 13 519 32 055 039 487
cert_ridgeSupport_suffix_decode_2 704 037 13 551 32 055 038 519
cert_ridgeSupport_suffix_decode_2 704 036 13 583 32 055 037 551
cert_ridgeSupport_suffix_decode_2 704 035 13 615 32 055 036 583
cert_ridgeSupport_suffix_decode_2 704 034 13 647 32 055 035 615
cert_ridgeSupport_suffix_decode_2 704 033 13 679 32 055 034 647
cert_ridgeSupport_suffix_decode_2 704 032 13 711 32 055 033 679
cert_ridgeSupport_suffix_decode_2 704 031 13 743 32 055 032 711
cert_ridgeSupport_suffix_decode_2 704 030 13 775 32 055 031 743
cert_ridgeSupport_suffix_decode_2 704 029 13 807 32 055 030 775
cert_ridgeSupport_suffix_decode_2 704 028 13 839 32 055 029 807
cert_ridgeSupport_suffix_decode_2 704 027 13 871 32 055 028 839
cert_ridgeSupport_suffix_decode_2 704 026 13 903 32 055 027 871
cert_ridgeSupport_suffix_decode_2 704 025 13 935 32 055 026 903
cert_ridgeSupport_suffix_decode_2 704 024 13 967 32 055 025 935
cert_ridgeSupport_suffix_decode_2 704 023 13 999 32 055 024 967
cert_ridgeSupport_suffix_decode_2 704 022 13 1031 32 055 023 999
cert_ridgeSupport_suffix_decode_2 704 021 13 1063 32 055 022 1031
cert_ridgeSupport_suffix_decode_2 704 020 13 1095 32 055 021 1063
cert_ridgeSupport_suffix_decode_2 704 019 13 1127 32 055 020 1095
cert_ridgeSupport_suffix_decode_2 704 018 13 1159 32 055 019 1127
cert_ridgeSupport_suffix_decode_2 704 017 13 1191 32 055 018 1159
cert_ridgeSupport_suffix_decode_2 704 016 13 1223 32 055 017 1191
cert_ridgeSupport_suffix_decode_2 704 015 13 1255 32 055 016 1223
cert_ridgeSupport_suffix_decode_2 704 014 13 1287 32 055 015 1255
cert_ridgeSupport_suffix_decode_2 704 013 13 1319 32 055 014 1287
cert_ridgeSupport_suffix_decode_2 704 012 13 1351 32 055 013 1319
cert_ridgeSupport_suffix_decode_2 704 011 13 1383 32 055 012 1351
cert_ridgeSupport_suffix_decode_2 704 010 13 1415 32 055 011 1383
cert_ridgeSupport_suffix_decode_2 704 009 13 1447 32 055 010 1415
cert_ridgeSupport_suffix_decode_2 704 008 13 1479 32 055 009 1447
cert_ridgeSupport_suffix_decode_2 704 007 13 1511 32 055 008 1479
cert_ridgeSupport_suffix_decode_2 704 006 13 1543 32 055 007 1511
cert_ridgeSupport_suffix_decode_2 704 005 13 1575 32 055 006 1543
cert_ridgeSupport_suffix_decode_2 704 004 13 1607 32 055 005 1575
cert_ridgeSupport_suffix_decode_2 704 003 13 1639 32 055 004 1607
cert_ridgeSupport_suffix_decode_2 704 002 13 1671 32 055 003 1639
cert_ridgeSupport_suffix_decode_2 704 001 13 1703 32 055 002 1671
cert_ridgeSupport_suffix_decode_2 704 000 13 1735 32 055 001 1703
cert_ridgeSupport_eq 704
theorem ridgeTest_large_704 : ridgeTest 704 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport704_eq]
    simp only [ridgeSupport704_suffix_000, ridgeSupport704_suffix_001, ridgeSupport704_suffix_002, ridgeSupport704_suffix_003, ridgeSupport704_suffix_004, ridgeSupport704_suffix_005, ridgeSupport704_suffix_006, ridgeSupport704_suffix_007, ridgeSupport704_suffix_008, ridgeSupport704_suffix_009, ridgeSupport704_suffix_010, ridgeSupport704_suffix_011, ridgeSupport704_suffix_012, ridgeSupport704_suffix_013, ridgeSupport704_suffix_014, ridgeSupport704_suffix_015, ridgeSupport704_suffix_016, ridgeSupport704_suffix_017, ridgeSupport704_suffix_018, ridgeSupport704_suffix_019, ridgeSupport704_suffix_020, ridgeSupport704_suffix_021, ridgeSupport704_suffix_022, ridgeSupport704_suffix_023, ridgeSupport704_suffix_024, ridgeSupport704_suffix_025, ridgeSupport704_suffix_026, ridgeSupport704_suffix_027, ridgeSupport704_suffix_028, ridgeSupport704_suffix_029, ridgeSupport704_suffix_030, ridgeSupport704_suffix_031, ridgeSupport704_suffix_032, ridgeSupport704_suffix_033, ridgeSupport704_suffix_034, ridgeSupport704_suffix_035, ridgeSupport704_suffix_036, ridgeSupport704_suffix_037, ridgeSupport704_suffix_038, ridgeSupport704_suffix_039, ridgeSupport704_suffix_040, ridgeSupport704_suffix_041, ridgeSupport704_suffix_042, ridgeSupport704_suffix_043, ridgeSupport704_suffix_044, ridgeSupport704_suffix_045, ridgeSupport704_suffix_046, ridgeSupport704_suffix_047, ridgeSupport704_suffix_048, ridgeSupport704_suffix_049, ridgeSupport704_suffix_050, ridgeSupport704_suffix_051, ridgeSupport704_suffix_052, ridgeSupport704_suffix_053, ridgeSupport704_suffix_054, ridgeSupport704_suffix_055, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport704_000_mask, ridgeSupport704_001_mask, ridgeSupport704_002_mask, ridgeSupport704_003_mask, ridgeSupport704_004_mask, ridgeSupport704_005_mask, ridgeSupport704_006_mask, ridgeSupport704_007_mask, ridgeSupport704_008_mask, ridgeSupport704_009_mask, ridgeSupport704_010_mask, ridgeSupport704_011_mask, ridgeSupport704_012_mask, ridgeSupport704_013_mask, ridgeSupport704_014_mask, ridgeSupport704_015_mask, ridgeSupport704_016_mask, ridgeSupport704_017_mask, ridgeSupport704_018_mask, ridgeSupport704_019_mask, ridgeSupport704_020_mask, ridgeSupport704_021_mask, ridgeSupport704_022_mask, ridgeSupport704_023_mask, ridgeSupport704_024_mask, ridgeSupport704_025_mask, ridgeSupport704_026_mask, ridgeSupport704_027_mask, ridgeSupport704_028_mask, ridgeSupport704_029_mask, ridgeSupport704_030_mask, ridgeSupport704_031_mask, ridgeSupport704_032_mask, ridgeSupport704_033_mask, ridgeSupport704_034_mask, ridgeSupport704_035_mask, ridgeSupport704_036_mask, ridgeSupport704_037_mask, ridgeSupport704_038_mask, ridgeSupport704_039_mask, ridgeSupport704_040_mask, ridgeSupport704_041_mask, ridgeSupport704_042_mask, ridgeSupport704_043_mask, ridgeSupport704_044_mask, ridgeSupport704_045_mask, ridgeSupport704_046_mask, ridgeSupport704_047_mask, ridgeSupport704_048_mask, ridgeSupport704_049_mask, ridgeSupport704_050_mask, ridgeSupport704_051_mask, ridgeSupport704_052_mask, ridgeSupport704_053_mask, ridgeSupport704_054_mask]
    decide +kernel
  · rw [ridgeSupport704_eq]
    simp only [ridgeSupport704_suffix_000, ridgeSupport704_suffix_001, ridgeSupport704_suffix_002, ridgeSupport704_suffix_003, ridgeSupport704_suffix_004, ridgeSupport704_suffix_005, ridgeSupport704_suffix_006, ridgeSupport704_suffix_007, ridgeSupport704_suffix_008, ridgeSupport704_suffix_009, ridgeSupport704_suffix_010, ridgeSupport704_suffix_011, ridgeSupport704_suffix_012, ridgeSupport704_suffix_013, ridgeSupport704_suffix_014, ridgeSupport704_suffix_015, ridgeSupport704_suffix_016, ridgeSupport704_suffix_017, ridgeSupport704_suffix_018, ridgeSupport704_suffix_019, ridgeSupport704_suffix_020, ridgeSupport704_suffix_021, ridgeSupport704_suffix_022, ridgeSupport704_suffix_023, ridgeSupport704_suffix_024, ridgeSupport704_suffix_025, ridgeSupport704_suffix_026, ridgeSupport704_suffix_027, ridgeSupport704_suffix_028, ridgeSupport704_suffix_029, ridgeSupport704_suffix_030, ridgeSupport704_suffix_031, ridgeSupport704_suffix_032, ridgeSupport704_suffix_033, ridgeSupport704_suffix_034, ridgeSupport704_suffix_035, ridgeSupport704_suffix_036, ridgeSupport704_suffix_037, ridgeSupport704_suffix_038, ridgeSupport704_suffix_039, ridgeSupport704_suffix_040, ridgeSupport704_suffix_041, ridgeSupport704_suffix_042, ridgeSupport704_suffix_043, ridgeSupport704_suffix_044, ridgeSupport704_suffix_045, ridgeSupport704_suffix_046, ridgeSupport704_suffix_047, ridgeSupport704_suffix_048, ridgeSupport704_suffix_049, ridgeSupport704_suffix_050, ridgeSupport704_suffix_051, ridgeSupport704_suffix_052, ridgeSupport704_suffix_053, ridgeSupport704_suffix_054, ridgeSupport704_suffix_055, List.all_append, List.all_nil, ridgeSupport704_000_checked, ridgeSupport704_001_checked, ridgeSupport704_002_checked, ridgeSupport704_003_checked, ridgeSupport704_004_checked, ridgeSupport704_005_checked, ridgeSupport704_006_checked, ridgeSupport704_007_checked, ridgeSupport704_008_checked, ridgeSupport704_009_checked, ridgeSupport704_010_checked, ridgeSupport704_011_checked, ridgeSupport704_012_checked, ridgeSupport704_013_checked, ridgeSupport704_014_checked, ridgeSupport704_015_checked, ridgeSupport704_016_checked, ridgeSupport704_017_checked, ridgeSupport704_018_checked, ridgeSupport704_019_checked, ridgeSupport704_020_checked, ridgeSupport704_021_checked, ridgeSupport704_022_checked, ridgeSupport704_023_checked, ridgeSupport704_024_checked, ridgeSupport704_025_checked, ridgeSupport704_026_checked, ridgeSupport704_027_checked, ridgeSupport704_028_checked, ridgeSupport704_029_checked, ridgeSupport704_030_checked, ridgeSupport704_031_checked, ridgeSupport704_032_checked, ridgeSupport704_033_checked, ridgeSupport704_034_checked, ridgeSupport704_035_checked, ridgeSupport704_036_checked, ridgeSupport704_037_checked, ridgeSupport704_038_checked, ridgeSupport704_039_checked, ridgeSupport704_040_checked, ridgeSupport704_041_checked, ridgeSupport704_042_checked, ridgeSupport704_043_checked, ridgeSupport704_044_checked, ridgeSupport704_045_checked, ridgeSupport704_046_checked, ridgeSupport704_047_checked, ridgeSupport704_048_checked, ridgeSupport704_049_checked, ridgeSupport704_050_checked, ridgeSupport704_051_checked, ridgeSupport704_052_checked, ridgeSupport704_053_checked, ridgeSupport704_054_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase02
