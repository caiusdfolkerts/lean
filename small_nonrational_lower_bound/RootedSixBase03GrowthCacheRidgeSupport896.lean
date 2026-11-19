module
prelude
public meta import LowerSchemas.FiniteRootedSixBase
public import RootedSixBase03GrowthCacheRidgeSupport896Part000
public import RootedSixBase03GrowthCacheRidgeSupport896Part001
public import RootedSixBase03GrowthCacheRidgeSupport896Part002
public import RootedSixBase03GrowthCacheRidgeSupport896Part003
public import RootedSixBase03GrowthCacheRidgeSupport896Part004
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase03
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
cert_ridgeSupport_suffix_decode 896 037 13
cert_ridgeSupport_suffix_decode_2 896 036 13 7 7 037 037 0
cert_ridgeSupport_suffix_decode_2 896 035 13 39 32 037 036 7
cert_ridgeSupport_suffix_decode_2 896 034 13 71 32 037 035 39
cert_ridgeSupport_suffix_decode_2 896 033 13 103 32 037 034 71
cert_ridgeSupport_suffix_decode_2 896 032 13 135 32 037 033 103
cert_ridgeSupport_suffix_decode_2 896 031 13 167 32 037 032 135
cert_ridgeSupport_suffix_decode_2 896 030 13 199 32 037 031 167
cert_ridgeSupport_suffix_decode_2 896 029 13 231 32 037 030 199
cert_ridgeSupport_suffix_decode_2 896 028 13 263 32 037 029 231
cert_ridgeSupport_suffix_decode_2 896 027 13 295 32 037 028 263
cert_ridgeSupport_suffix_decode_2 896 026 13 327 32 037 027 295
cert_ridgeSupport_suffix_decode_2 896 025 13 359 32 037 026 327
cert_ridgeSupport_suffix_decode_2 896 024 13 391 32 037 025 359
cert_ridgeSupport_suffix_decode_2 896 023 13 423 32 037 024 391
cert_ridgeSupport_suffix_decode_2 896 022 13 455 32 037 023 423
cert_ridgeSupport_suffix_decode_2 896 021 13 487 32 037 022 455
cert_ridgeSupport_suffix_decode_2 896 020 13 519 32 037 021 487
cert_ridgeSupport_suffix_decode_2 896 019 13 551 32 037 020 519
cert_ridgeSupport_suffix_decode_2 896 018 13 583 32 037 019 551
cert_ridgeSupport_suffix_decode_2 896 017 13 615 32 037 018 583
cert_ridgeSupport_suffix_decode_2 896 016 13 647 32 037 017 615
cert_ridgeSupport_suffix_decode_2 896 015 13 679 32 037 016 647
cert_ridgeSupport_suffix_decode_2 896 014 13 711 32 037 015 679
cert_ridgeSupport_suffix_decode_2 896 013 13 743 32 037 014 711
cert_ridgeSupport_suffix_decode_2 896 012 13 775 32 037 013 743
cert_ridgeSupport_suffix_decode_2 896 011 13 807 32 037 012 775
cert_ridgeSupport_suffix_decode_2 896 010 13 839 32 037 011 807
cert_ridgeSupport_suffix_decode_2 896 009 13 871 32 037 010 839
cert_ridgeSupport_suffix_decode_2 896 008 13 903 32 037 009 871
cert_ridgeSupport_suffix_decode_2 896 007 13 935 32 037 008 903
cert_ridgeSupport_suffix_decode_2 896 006 13 967 32 037 007 935
cert_ridgeSupport_suffix_decode_2 896 005 13 999 32 037 006 967
cert_ridgeSupport_suffix_decode_2 896 004 13 1031 32 037 005 999
cert_ridgeSupport_suffix_decode_2 896 003 13 1063 32 037 004 1031
cert_ridgeSupport_suffix_decode_2 896 002 13 1095 32 037 003 1063
cert_ridgeSupport_suffix_decode_2 896 001 13 1127 32 037 002 1095
cert_ridgeSupport_suffix_decode_2 896 000 13 1159 32 037 001 1127
cert_ridgeSupport_eq_2 896
theorem ridgeTest_large_896 : ridgeTest 896 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [show candidateRows 896 = ridgeSupport896_suffix_000 from ridgeSupport896_eq]
    simp only [ridgeSupport896_suffix_000, ridgeSupport896_suffix_001, ridgeSupport896_suffix_002, ridgeSupport896_suffix_003, ridgeSupport896_suffix_004, ridgeSupport896_suffix_005, ridgeSupport896_suffix_006, ridgeSupport896_suffix_007, ridgeSupport896_suffix_008, ridgeSupport896_suffix_009, ridgeSupport896_suffix_010, ridgeSupport896_suffix_011, ridgeSupport896_suffix_012, ridgeSupport896_suffix_013, ridgeSupport896_suffix_014, ridgeSupport896_suffix_015, ridgeSupport896_suffix_016, ridgeSupport896_suffix_017, ridgeSupport896_suffix_018, ridgeSupport896_suffix_019, ridgeSupport896_suffix_020, ridgeSupport896_suffix_021, ridgeSupport896_suffix_022, ridgeSupport896_suffix_023, ridgeSupport896_suffix_024, ridgeSupport896_suffix_025, ridgeSupport896_suffix_026, ridgeSupport896_suffix_027, ridgeSupport896_suffix_028, ridgeSupport896_suffix_029, ridgeSupport896_suffix_030, ridgeSupport896_suffix_031, ridgeSupport896_suffix_032, ridgeSupport896_suffix_033, ridgeSupport896_suffix_034, ridgeSupport896_suffix_035, ridgeSupport896_suffix_036, ridgeSupport896_suffix_037, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport896_000_mask, ridgeSupport896_001_mask, ridgeSupport896_002_mask, ridgeSupport896_003_mask, ridgeSupport896_004_mask, ridgeSupport896_005_mask, ridgeSupport896_006_mask, ridgeSupport896_007_mask, ridgeSupport896_008_mask, ridgeSupport896_009_mask, ridgeSupport896_010_mask, ridgeSupport896_011_mask, ridgeSupport896_012_mask, ridgeSupport896_013_mask, ridgeSupport896_014_mask, ridgeSupport896_015_mask, ridgeSupport896_016_mask, ridgeSupport896_017_mask, ridgeSupport896_018_mask, ridgeSupport896_019_mask, ridgeSupport896_020_mask, ridgeSupport896_021_mask, ridgeSupport896_022_mask, ridgeSupport896_023_mask, ridgeSupport896_024_mask, ridgeSupport896_025_mask, ridgeSupport896_026_mask, ridgeSupport896_027_mask, ridgeSupport896_028_mask, ridgeSupport896_029_mask, ridgeSupport896_030_mask, ridgeSupport896_031_mask, ridgeSupport896_032_mask, ridgeSupport896_033_mask, ridgeSupport896_034_mask, ridgeSupport896_035_mask, ridgeSupport896_036_mask]
    decide +kernel
  · rw [show candidateRows 896 = ridgeSupport896_suffix_000 from ridgeSupport896_eq]
    simp only [ridgeSupport896_suffix_000, ridgeSupport896_suffix_001, ridgeSupport896_suffix_002, ridgeSupport896_suffix_003, ridgeSupport896_suffix_004, ridgeSupport896_suffix_005, ridgeSupport896_suffix_006, ridgeSupport896_suffix_007, ridgeSupport896_suffix_008, ridgeSupport896_suffix_009, ridgeSupport896_suffix_010, ridgeSupport896_suffix_011, ridgeSupport896_suffix_012, ridgeSupport896_suffix_013, ridgeSupport896_suffix_014, ridgeSupport896_suffix_015, ridgeSupport896_suffix_016, ridgeSupport896_suffix_017, ridgeSupport896_suffix_018, ridgeSupport896_suffix_019, ridgeSupport896_suffix_020, ridgeSupport896_suffix_021, ridgeSupport896_suffix_022, ridgeSupport896_suffix_023, ridgeSupport896_suffix_024, ridgeSupport896_suffix_025, ridgeSupport896_suffix_026, ridgeSupport896_suffix_027, ridgeSupport896_suffix_028, ridgeSupport896_suffix_029, ridgeSupport896_suffix_030, ridgeSupport896_suffix_031, ridgeSupport896_suffix_032, ridgeSupport896_suffix_033, ridgeSupport896_suffix_034, ridgeSupport896_suffix_035, ridgeSupport896_suffix_036, ridgeSupport896_suffix_037, List.all_append, List.all_nil, ridgeSupport896_000_checked, ridgeSupport896_001_checked, ridgeSupport896_002_checked, ridgeSupport896_003_checked, ridgeSupport896_004_checked, ridgeSupport896_005_checked, ridgeSupport896_006_checked, ridgeSupport896_007_checked, ridgeSupport896_008_checked, ridgeSupport896_009_checked, ridgeSupport896_010_checked, ridgeSupport896_011_checked, ridgeSupport896_012_checked, ridgeSupport896_013_checked, ridgeSupport896_014_checked, ridgeSupport896_015_checked, ridgeSupport896_016_checked, ridgeSupport896_017_checked, ridgeSupport896_018_checked, ridgeSupport896_019_checked, ridgeSupport896_020_checked, ridgeSupport896_021_checked, ridgeSupport896_022_checked, ridgeSupport896_023_checked, ridgeSupport896_024_checked, ridgeSupport896_025_checked, ridgeSupport896_026_checked, ridgeSupport896_027_checked, ridgeSupport896_028_checked, ridgeSupport896_029_checked, ridgeSupport896_030_checked, ridgeSupport896_031_checked, ridgeSupport896_032_checked, ridgeSupport896_033_checked, ridgeSupport896_034_checked, ridgeSupport896_035_checked, ridgeSupport896_036_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase03
