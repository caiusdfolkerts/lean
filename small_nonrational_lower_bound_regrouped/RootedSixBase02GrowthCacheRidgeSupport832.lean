module
prelude
public meta import LowerSchemas.FiniteRootedSixBase.Part0
public import BundledChecks.RootedSixBase02GrowthCacheRidgeSupport832Batch000
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase02
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
cert_ridgeSupport_suffix_decode 832 055 13
cert_ridgeSupport_suffix_decode_2 832 054 13 7 7 055 055 0
cert_ridgeSupport_suffix_decode_2 832 053 13 39 32 055 054 7
cert_ridgeSupport_suffix_decode_2 832 052 13 71 32 055 053 39
cert_ridgeSupport_suffix_decode_2 832 051 13 103 32 055 052 71
cert_ridgeSupport_suffix_decode_2 832 050 13 135 32 055 051 103
cert_ridgeSupport_suffix_decode_2 832 049 13 167 32 055 050 135
cert_ridgeSupport_suffix_decode_2 832 048 13 199 32 055 049 167
cert_ridgeSupport_suffix_decode_2 832 047 13 231 32 055 048 199
cert_ridgeSupport_suffix_decode_2 832 046 13 263 32 055 047 231
cert_ridgeSupport_suffix_decode_2 832 045 13 295 32 055 046 263
cert_ridgeSupport_suffix_decode_2 832 044 13 327 32 055 045 295
cert_ridgeSupport_suffix_decode_2 832 043 13 359 32 055 044 327
cert_ridgeSupport_suffix_decode_2 832 042 13 391 32 055 043 359
cert_ridgeSupport_suffix_decode_2 832 041 13 423 32 055 042 391
cert_ridgeSupport_suffix_decode_2 832 040 13 455 32 055 041 423
cert_ridgeSupport_suffix_decode_2 832 039 13 487 32 055 040 455
cert_ridgeSupport_suffix_decode_2 832 038 13 519 32 055 039 487
cert_ridgeSupport_suffix_decode_2 832 037 13 551 32 055 038 519
cert_ridgeSupport_suffix_decode_2 832 036 13 583 32 055 037 551
cert_ridgeSupport_suffix_decode_2 832 035 13 615 32 055 036 583
cert_ridgeSupport_suffix_decode_2 832 034 13 647 32 055 035 615
cert_ridgeSupport_suffix_decode_2 832 033 13 679 32 055 034 647
cert_ridgeSupport_suffix_decode_2 832 032 13 711 32 055 033 679
cert_ridgeSupport_suffix_decode_2 832 031 13 743 32 055 032 711
cert_ridgeSupport_suffix_decode_2 832 030 13 775 32 055 031 743
cert_ridgeSupport_suffix_decode_2 832 029 13 807 32 055 030 775
cert_ridgeSupport_suffix_decode_2 832 028 13 839 32 055 029 807
cert_ridgeSupport_suffix_decode_2 832 027 13 871 32 055 028 839
cert_ridgeSupport_suffix_decode_2 832 026 13 903 32 055 027 871
cert_ridgeSupport_suffix_decode_2 832 025 13 935 32 055 026 903
cert_ridgeSupport_suffix_decode_2 832 024 13 967 32 055 025 935
cert_ridgeSupport_suffix_decode_2 832 023 13 999 32 055 024 967
cert_ridgeSupport_suffix_decode_2 832 022 13 1031 32 055 023 999
cert_ridgeSupport_suffix_decode_2 832 021 13 1063 32 055 022 1031
cert_ridgeSupport_suffix_decode_2 832 020 13 1095 32 055 021 1063
cert_ridgeSupport_suffix_decode_2 832 019 13 1127 32 055 020 1095
cert_ridgeSupport_suffix_decode_2 832 018 13 1159 32 055 019 1127
cert_ridgeSupport_suffix_decode_2 832 017 13 1191 32 055 018 1159
cert_ridgeSupport_suffix_decode_2 832 016 13 1223 32 055 017 1191
cert_ridgeSupport_suffix_decode_2 832 015 13 1255 32 055 016 1223
cert_ridgeSupport_suffix_decode_2 832 014 13 1287 32 055 015 1255
cert_ridgeSupport_suffix_decode_2 832 013 13 1319 32 055 014 1287
cert_ridgeSupport_suffix_decode_2 832 012 13 1351 32 055 013 1319
cert_ridgeSupport_suffix_decode_2 832 011 13 1383 32 055 012 1351
cert_ridgeSupport_suffix_decode_2 832 010 13 1415 32 055 011 1383
cert_ridgeSupport_suffix_decode_2 832 009 13 1447 32 055 010 1415
cert_ridgeSupport_suffix_decode_2 832 008 13 1479 32 055 009 1447
cert_ridgeSupport_suffix_decode_2 832 007 13 1511 32 055 008 1479
cert_ridgeSupport_suffix_decode_2 832 006 13 1543 32 055 007 1511
cert_ridgeSupport_suffix_decode_2 832 005 13 1575 32 055 006 1543
cert_ridgeSupport_suffix_decode_2 832 004 13 1607 32 055 005 1575
cert_ridgeSupport_suffix_decode_2 832 003 13 1639 32 055 004 1607
cert_ridgeSupport_suffix_decode_2 832 002 13 1671 32 055 003 1639
cert_ridgeSupport_suffix_decode_2 832 001 13 1703 32 055 002 1671
cert_ridgeSupport_suffix_decode_2 832 000 13 1735 32 055 001 1703
cert_ridgeSupport_eq 832
theorem ridgeTest_large_832 : ridgeTest 832 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport832_eq]
    simp only [ridgeSupport832_suffix_000, ridgeSupport832_suffix_001, ridgeSupport832_suffix_002, ridgeSupport832_suffix_003, ridgeSupport832_suffix_004, ridgeSupport832_suffix_005, ridgeSupport832_suffix_006, ridgeSupport832_suffix_007, ridgeSupport832_suffix_008, ridgeSupport832_suffix_009, ridgeSupport832_suffix_010, ridgeSupport832_suffix_011, ridgeSupport832_suffix_012, ridgeSupport832_suffix_013, ridgeSupport832_suffix_014, ridgeSupport832_suffix_015, ridgeSupport832_suffix_016, ridgeSupport832_suffix_017, ridgeSupport832_suffix_018, ridgeSupport832_suffix_019, ridgeSupport832_suffix_020, ridgeSupport832_suffix_021, ridgeSupport832_suffix_022, ridgeSupport832_suffix_023, ridgeSupport832_suffix_024, ridgeSupport832_suffix_025, ridgeSupport832_suffix_026, ridgeSupport832_suffix_027, ridgeSupport832_suffix_028, ridgeSupport832_suffix_029, ridgeSupport832_suffix_030, ridgeSupport832_suffix_031, ridgeSupport832_suffix_032, ridgeSupport832_suffix_033, ridgeSupport832_suffix_034, ridgeSupport832_suffix_035, ridgeSupport832_suffix_036, ridgeSupport832_suffix_037, ridgeSupport832_suffix_038, ridgeSupport832_suffix_039, ridgeSupport832_suffix_040, ridgeSupport832_suffix_041, ridgeSupport832_suffix_042, ridgeSupport832_suffix_043, ridgeSupport832_suffix_044, ridgeSupport832_suffix_045, ridgeSupport832_suffix_046, ridgeSupport832_suffix_047, ridgeSupport832_suffix_048, ridgeSupport832_suffix_049, ridgeSupport832_suffix_050, ridgeSupport832_suffix_051, ridgeSupport832_suffix_052, ridgeSupport832_suffix_053, ridgeSupport832_suffix_054, ridgeSupport832_suffix_055, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport832_000_mask, ridgeSupport832_001_mask, ridgeSupport832_002_mask, ridgeSupport832_003_mask, ridgeSupport832_004_mask, ridgeSupport832_005_mask, ridgeSupport832_006_mask, ridgeSupport832_007_mask, ridgeSupport832_008_mask, ridgeSupport832_009_mask, ridgeSupport832_010_mask, ridgeSupport832_011_mask, ridgeSupport832_012_mask, ridgeSupport832_013_mask, ridgeSupport832_014_mask, ridgeSupport832_015_mask, ridgeSupport832_016_mask, ridgeSupport832_017_mask, ridgeSupport832_018_mask, ridgeSupport832_019_mask, ridgeSupport832_020_mask, ridgeSupport832_021_mask, ridgeSupport832_022_mask, ridgeSupport832_023_mask, ridgeSupport832_024_mask, ridgeSupport832_025_mask, ridgeSupport832_026_mask, ridgeSupport832_027_mask, ridgeSupport832_028_mask, ridgeSupport832_029_mask, ridgeSupport832_030_mask, ridgeSupport832_031_mask, ridgeSupport832_032_mask, ridgeSupport832_033_mask, ridgeSupport832_034_mask, ridgeSupport832_035_mask, ridgeSupport832_036_mask, ridgeSupport832_037_mask, ridgeSupport832_038_mask, ridgeSupport832_039_mask, ridgeSupport832_040_mask, ridgeSupport832_041_mask, ridgeSupport832_042_mask, ridgeSupport832_043_mask, ridgeSupport832_044_mask, ridgeSupport832_045_mask, ridgeSupport832_046_mask, ridgeSupport832_047_mask, ridgeSupport832_048_mask, ridgeSupport832_049_mask, ridgeSupport832_050_mask, ridgeSupport832_051_mask, ridgeSupport832_052_mask, ridgeSupport832_053_mask, ridgeSupport832_054_mask]
    decide +kernel
  · rw [ridgeSupport832_eq]
    simp only [ridgeSupport832_suffix_000, ridgeSupport832_suffix_001, ridgeSupport832_suffix_002, ridgeSupport832_suffix_003, ridgeSupport832_suffix_004, ridgeSupport832_suffix_005, ridgeSupport832_suffix_006, ridgeSupport832_suffix_007, ridgeSupport832_suffix_008, ridgeSupport832_suffix_009, ridgeSupport832_suffix_010, ridgeSupport832_suffix_011, ridgeSupport832_suffix_012, ridgeSupport832_suffix_013, ridgeSupport832_suffix_014, ridgeSupport832_suffix_015, ridgeSupport832_suffix_016, ridgeSupport832_suffix_017, ridgeSupport832_suffix_018, ridgeSupport832_suffix_019, ridgeSupport832_suffix_020, ridgeSupport832_suffix_021, ridgeSupport832_suffix_022, ridgeSupport832_suffix_023, ridgeSupport832_suffix_024, ridgeSupport832_suffix_025, ridgeSupport832_suffix_026, ridgeSupport832_suffix_027, ridgeSupport832_suffix_028, ridgeSupport832_suffix_029, ridgeSupport832_suffix_030, ridgeSupport832_suffix_031, ridgeSupport832_suffix_032, ridgeSupport832_suffix_033, ridgeSupport832_suffix_034, ridgeSupport832_suffix_035, ridgeSupport832_suffix_036, ridgeSupport832_suffix_037, ridgeSupport832_suffix_038, ridgeSupport832_suffix_039, ridgeSupport832_suffix_040, ridgeSupport832_suffix_041, ridgeSupport832_suffix_042, ridgeSupport832_suffix_043, ridgeSupport832_suffix_044, ridgeSupport832_suffix_045, ridgeSupport832_suffix_046, ridgeSupport832_suffix_047, ridgeSupport832_suffix_048, ridgeSupport832_suffix_049, ridgeSupport832_suffix_050, ridgeSupport832_suffix_051, ridgeSupport832_suffix_052, ridgeSupport832_suffix_053, ridgeSupport832_suffix_054, ridgeSupport832_suffix_055, List.all_append, List.all_nil, ridgeSupport832_000_checked, ridgeSupport832_001_checked, ridgeSupport832_002_checked, ridgeSupport832_003_checked, ridgeSupport832_004_checked, ridgeSupport832_005_checked, ridgeSupport832_006_checked, ridgeSupport832_007_checked, ridgeSupport832_008_checked, ridgeSupport832_009_checked, ridgeSupport832_010_checked, ridgeSupport832_011_checked, ridgeSupport832_012_checked, ridgeSupport832_013_checked, ridgeSupport832_014_checked, ridgeSupport832_015_checked, ridgeSupport832_016_checked, ridgeSupport832_017_checked, ridgeSupport832_018_checked, ridgeSupport832_019_checked, ridgeSupport832_020_checked, ridgeSupport832_021_checked, ridgeSupport832_022_checked, ridgeSupport832_023_checked, ridgeSupport832_024_checked, ridgeSupport832_025_checked, ridgeSupport832_026_checked, ridgeSupport832_027_checked, ridgeSupport832_028_checked, ridgeSupport832_029_checked, ridgeSupport832_030_checked, ridgeSupport832_031_checked, ridgeSupport832_032_checked, ridgeSupport832_033_checked, ridgeSupport832_034_checked, ridgeSupport832_035_checked, ridgeSupport832_036_checked, ridgeSupport832_037_checked, ridgeSupport832_038_checked, ridgeSupport832_039_checked, ridgeSupport832_040_checked, ridgeSupport832_041_checked, ridgeSupport832_042_checked, ridgeSupport832_043_checked, ridgeSupport832_044_checked, ridgeSupport832_045_checked, ridgeSupport832_046_checked, ridgeSupport832_047_checked, ridgeSupport832_048_checked, ridgeSupport832_049_checked, ridgeSupport832_050_checked, ridgeSupport832_051_checked, ridgeSupport832_052_checked, ridgeSupport832_053_checked, ridgeSupport832_054_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase02
