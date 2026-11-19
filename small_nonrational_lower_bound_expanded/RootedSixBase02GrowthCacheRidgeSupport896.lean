module
prelude
public meta import LowerSchemas.FiniteRootedSixBase.Part0
public import BundledChecks.RootedSixBase02GrowthCacheRidgeSupport896Batch000
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase02
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
cert_ridgeSupport_suffix_decode 896 055 13
cert_ridgeSupport_suffix_decode_2 896 054 13 7 7 055 055 0
cert_ridgeSupport_suffix_decode_2 896 053 13 39 32 055 054 7
cert_ridgeSupport_suffix_decode_2 896 052 13 71 32 055 053 39
cert_ridgeSupport_suffix_decode_2 896 051 13 103 32 055 052 71
cert_ridgeSupport_suffix_decode_2 896 050 13 135 32 055 051 103
cert_ridgeSupport_suffix_decode_2 896 049 13 167 32 055 050 135
cert_ridgeSupport_suffix_decode_2 896 048 13 199 32 055 049 167
cert_ridgeSupport_suffix_decode_2 896 047 13 231 32 055 048 199
cert_ridgeSupport_suffix_decode_2 896 046 13 263 32 055 047 231
cert_ridgeSupport_suffix_decode_2 896 045 13 295 32 055 046 263
cert_ridgeSupport_suffix_decode_2 896 044 13 327 32 055 045 295
cert_ridgeSupport_suffix_decode_2 896 043 13 359 32 055 044 327
cert_ridgeSupport_suffix_decode_2 896 042 13 391 32 055 043 359
cert_ridgeSupport_suffix_decode_2 896 041 13 423 32 055 042 391
cert_ridgeSupport_suffix_decode_2 896 040 13 455 32 055 041 423
cert_ridgeSupport_suffix_decode_2 896 039 13 487 32 055 040 455
cert_ridgeSupport_suffix_decode_2 896 038 13 519 32 055 039 487
cert_ridgeSupport_suffix_decode_2 896 037 13 551 32 055 038 519
cert_ridgeSupport_suffix_decode_2 896 036 13 583 32 055 037 551
cert_ridgeSupport_suffix_decode_2 896 035 13 615 32 055 036 583
cert_ridgeSupport_suffix_decode_2 896 034 13 647 32 055 035 615
cert_ridgeSupport_suffix_decode_2 896 033 13 679 32 055 034 647
cert_ridgeSupport_suffix_decode_2 896 032 13 711 32 055 033 679
cert_ridgeSupport_suffix_decode_2 896 031 13 743 32 055 032 711
cert_ridgeSupport_suffix_decode_2 896 030 13 775 32 055 031 743
cert_ridgeSupport_suffix_decode_2 896 029 13 807 32 055 030 775
cert_ridgeSupport_suffix_decode_2 896 028 13 839 32 055 029 807
cert_ridgeSupport_suffix_decode_2 896 027 13 871 32 055 028 839
cert_ridgeSupport_suffix_decode_2 896 026 13 903 32 055 027 871
cert_ridgeSupport_suffix_decode_2 896 025 13 935 32 055 026 903
cert_ridgeSupport_suffix_decode_2 896 024 13 967 32 055 025 935
cert_ridgeSupport_suffix_decode_2 896 023 13 999 32 055 024 967
cert_ridgeSupport_suffix_decode_2 896 022 13 1031 32 055 023 999
cert_ridgeSupport_suffix_decode_2 896 021 13 1063 32 055 022 1031
cert_ridgeSupport_suffix_decode_2 896 020 13 1095 32 055 021 1063
cert_ridgeSupport_suffix_decode_2 896 019 13 1127 32 055 020 1095
cert_ridgeSupport_suffix_decode_2 896 018 13 1159 32 055 019 1127
cert_ridgeSupport_suffix_decode_2 896 017 13 1191 32 055 018 1159
cert_ridgeSupport_suffix_decode_2 896 016 13 1223 32 055 017 1191
cert_ridgeSupport_suffix_decode_2 896 015 13 1255 32 055 016 1223
cert_ridgeSupport_suffix_decode_2 896 014 13 1287 32 055 015 1255
cert_ridgeSupport_suffix_decode_2 896 013 13 1319 32 055 014 1287
cert_ridgeSupport_suffix_decode_2 896 012 13 1351 32 055 013 1319
cert_ridgeSupport_suffix_decode_2 896 011 13 1383 32 055 012 1351
cert_ridgeSupport_suffix_decode_2 896 010 13 1415 32 055 011 1383
cert_ridgeSupport_suffix_decode_2 896 009 13 1447 32 055 010 1415
cert_ridgeSupport_suffix_decode_2 896 008 13 1479 32 055 009 1447
cert_ridgeSupport_suffix_decode_2 896 007 13 1511 32 055 008 1479
cert_ridgeSupport_suffix_decode_2 896 006 13 1543 32 055 007 1511
cert_ridgeSupport_suffix_decode_2 896 005 13 1575 32 055 006 1543
cert_ridgeSupport_suffix_decode_2 896 004 13 1607 32 055 005 1575
cert_ridgeSupport_suffix_decode_2 896 003 13 1639 32 055 004 1607
cert_ridgeSupport_suffix_decode_2 896 002 13 1671 32 055 003 1639
cert_ridgeSupport_suffix_decode_2 896 001 13 1703 32 055 002 1671
cert_ridgeSupport_suffix_decode_2 896 000 13 1735 32 055 001 1703
cert_ridgeSupport_eq 896
theorem ridgeTest_large_896 : ridgeTest 896 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport896_eq]
    simp only [ridgeSupport896_suffix_000, ridgeSupport896_suffix_001, ridgeSupport896_suffix_002, ridgeSupport896_suffix_003, ridgeSupport896_suffix_004, ridgeSupport896_suffix_005, ridgeSupport896_suffix_006, ridgeSupport896_suffix_007, ridgeSupport896_suffix_008, ridgeSupport896_suffix_009, ridgeSupport896_suffix_010, ridgeSupport896_suffix_011, ridgeSupport896_suffix_012, ridgeSupport896_suffix_013, ridgeSupport896_suffix_014, ridgeSupport896_suffix_015, ridgeSupport896_suffix_016, ridgeSupport896_suffix_017, ridgeSupport896_suffix_018, ridgeSupport896_suffix_019, ridgeSupport896_suffix_020, ridgeSupport896_suffix_021, ridgeSupport896_suffix_022, ridgeSupport896_suffix_023, ridgeSupport896_suffix_024, ridgeSupport896_suffix_025, ridgeSupport896_suffix_026, ridgeSupport896_suffix_027, ridgeSupport896_suffix_028, ridgeSupport896_suffix_029, ridgeSupport896_suffix_030, ridgeSupport896_suffix_031, ridgeSupport896_suffix_032, ridgeSupport896_suffix_033, ridgeSupport896_suffix_034, ridgeSupport896_suffix_035, ridgeSupport896_suffix_036, ridgeSupport896_suffix_037, ridgeSupport896_suffix_038, ridgeSupport896_suffix_039, ridgeSupport896_suffix_040, ridgeSupport896_suffix_041, ridgeSupport896_suffix_042, ridgeSupport896_suffix_043, ridgeSupport896_suffix_044, ridgeSupport896_suffix_045, ridgeSupport896_suffix_046, ridgeSupport896_suffix_047, ridgeSupport896_suffix_048, ridgeSupport896_suffix_049, ridgeSupport896_suffix_050, ridgeSupport896_suffix_051, ridgeSupport896_suffix_052, ridgeSupport896_suffix_053, ridgeSupport896_suffix_054, ridgeSupport896_suffix_055, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport896_000_mask, ridgeSupport896_001_mask, ridgeSupport896_002_mask, ridgeSupport896_003_mask, ridgeSupport896_004_mask, ridgeSupport896_005_mask, ridgeSupport896_006_mask, ridgeSupport896_007_mask, ridgeSupport896_008_mask, ridgeSupport896_009_mask, ridgeSupport896_010_mask, ridgeSupport896_011_mask, ridgeSupport896_012_mask, ridgeSupport896_013_mask, ridgeSupport896_014_mask, ridgeSupport896_015_mask, ridgeSupport896_016_mask, ridgeSupport896_017_mask, ridgeSupport896_018_mask, ridgeSupport896_019_mask, ridgeSupport896_020_mask, ridgeSupport896_021_mask, ridgeSupport896_022_mask, ridgeSupport896_023_mask, ridgeSupport896_024_mask, ridgeSupport896_025_mask, ridgeSupport896_026_mask, ridgeSupport896_027_mask, ridgeSupport896_028_mask, ridgeSupport896_029_mask, ridgeSupport896_030_mask, ridgeSupport896_031_mask, ridgeSupport896_032_mask, ridgeSupport896_033_mask, ridgeSupport896_034_mask, ridgeSupport896_035_mask, ridgeSupport896_036_mask, ridgeSupport896_037_mask, ridgeSupport896_038_mask, ridgeSupport896_039_mask, ridgeSupport896_040_mask, ridgeSupport896_041_mask, ridgeSupport896_042_mask, ridgeSupport896_043_mask, ridgeSupport896_044_mask, ridgeSupport896_045_mask, ridgeSupport896_046_mask, ridgeSupport896_047_mask, ridgeSupport896_048_mask, ridgeSupport896_049_mask, ridgeSupport896_050_mask, ridgeSupport896_051_mask, ridgeSupport896_052_mask, ridgeSupport896_053_mask, ridgeSupport896_054_mask]
    decide +kernel
  · rw [ridgeSupport896_eq]
    simp only [ridgeSupport896_suffix_000, ridgeSupport896_suffix_001, ridgeSupport896_suffix_002, ridgeSupport896_suffix_003, ridgeSupport896_suffix_004, ridgeSupport896_suffix_005, ridgeSupport896_suffix_006, ridgeSupport896_suffix_007, ridgeSupport896_suffix_008, ridgeSupport896_suffix_009, ridgeSupport896_suffix_010, ridgeSupport896_suffix_011, ridgeSupport896_suffix_012, ridgeSupport896_suffix_013, ridgeSupport896_suffix_014, ridgeSupport896_suffix_015, ridgeSupport896_suffix_016, ridgeSupport896_suffix_017, ridgeSupport896_suffix_018, ridgeSupport896_suffix_019, ridgeSupport896_suffix_020, ridgeSupport896_suffix_021, ridgeSupport896_suffix_022, ridgeSupport896_suffix_023, ridgeSupport896_suffix_024, ridgeSupport896_suffix_025, ridgeSupport896_suffix_026, ridgeSupport896_suffix_027, ridgeSupport896_suffix_028, ridgeSupport896_suffix_029, ridgeSupport896_suffix_030, ridgeSupport896_suffix_031, ridgeSupport896_suffix_032, ridgeSupport896_suffix_033, ridgeSupport896_suffix_034, ridgeSupport896_suffix_035, ridgeSupport896_suffix_036, ridgeSupport896_suffix_037, ridgeSupport896_suffix_038, ridgeSupport896_suffix_039, ridgeSupport896_suffix_040, ridgeSupport896_suffix_041, ridgeSupport896_suffix_042, ridgeSupport896_suffix_043, ridgeSupport896_suffix_044, ridgeSupport896_suffix_045, ridgeSupport896_suffix_046, ridgeSupport896_suffix_047, ridgeSupport896_suffix_048, ridgeSupport896_suffix_049, ridgeSupport896_suffix_050, ridgeSupport896_suffix_051, ridgeSupport896_suffix_052, ridgeSupport896_suffix_053, ridgeSupport896_suffix_054, ridgeSupport896_suffix_055, List.all_append, List.all_nil, ridgeSupport896_000_checked, ridgeSupport896_001_checked, ridgeSupport896_002_checked, ridgeSupport896_003_checked, ridgeSupport896_004_checked, ridgeSupport896_005_checked, ridgeSupport896_006_checked, ridgeSupport896_007_checked, ridgeSupport896_008_checked, ridgeSupport896_009_checked, ridgeSupport896_010_checked, ridgeSupport896_011_checked, ridgeSupport896_012_checked, ridgeSupport896_013_checked, ridgeSupport896_014_checked, ridgeSupport896_015_checked, ridgeSupport896_016_checked, ridgeSupport896_017_checked, ridgeSupport896_018_checked, ridgeSupport896_019_checked, ridgeSupport896_020_checked, ridgeSupport896_021_checked, ridgeSupport896_022_checked, ridgeSupport896_023_checked, ridgeSupport896_024_checked, ridgeSupport896_025_checked, ridgeSupport896_026_checked, ridgeSupport896_027_checked, ridgeSupport896_028_checked, ridgeSupport896_029_checked, ridgeSupport896_030_checked, ridgeSupport896_031_checked, ridgeSupport896_032_checked, ridgeSupport896_033_checked, ridgeSupport896_034_checked, ridgeSupport896_035_checked, ridgeSupport896_036_checked, ridgeSupport896_037_checked, ridgeSupport896_038_checked, ridgeSupport896_039_checked, ridgeSupport896_040_checked, ridgeSupport896_041_checked, ridgeSupport896_042_checked, ridgeSupport896_043_checked, ridgeSupport896_044_checked, ridgeSupport896_045_checked, ridgeSupport896_046_checked, ridgeSupport896_047_checked, ridgeSupport896_048_checked, ridgeSupport896_049_checked, ridgeSupport896_050_checked, ridgeSupport896_051_checked, ridgeSupport896_052_checked, ridgeSupport896_053_checked, ridgeSupport896_054_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase02
