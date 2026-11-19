module
prelude
public meta import LowerSchemas.FiniteRootedSixBase
public import RootedSixBase03GrowthCacheRidgeSupport832Part000
public import RootedSixBase03GrowthCacheRidgeSupport832Part001
public import RootedSixBase03GrowthCacheRidgeSupport832Part002
public import RootedSixBase03GrowthCacheRidgeSupport832Part003
public import RootedSixBase03GrowthCacheRidgeSupport832Part004
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase03
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
cert_ridgeSupport_suffix_decode 832 037 13
cert_ridgeSupport_suffix_decode_2 832 036 13 7 7 037 037 0
cert_ridgeSupport_suffix_decode_2 832 035 13 39 32 037 036 7
cert_ridgeSupport_suffix_decode_2 832 034 13 71 32 037 035 39
cert_ridgeSupport_suffix_decode_2 832 033 13 103 32 037 034 71
cert_ridgeSupport_suffix_decode_2 832 032 13 135 32 037 033 103
cert_ridgeSupport_suffix_decode_2 832 031 13 167 32 037 032 135
cert_ridgeSupport_suffix_decode_2 832 030 13 199 32 037 031 167
cert_ridgeSupport_suffix_decode_2 832 029 13 231 32 037 030 199
cert_ridgeSupport_suffix_decode_2 832 028 13 263 32 037 029 231
cert_ridgeSupport_suffix_decode_2 832 027 13 295 32 037 028 263
cert_ridgeSupport_suffix_decode_2 832 026 13 327 32 037 027 295
cert_ridgeSupport_suffix_decode_2 832 025 13 359 32 037 026 327
cert_ridgeSupport_suffix_decode_2 832 024 13 391 32 037 025 359
cert_ridgeSupport_suffix_decode_2 832 023 13 423 32 037 024 391
cert_ridgeSupport_suffix_decode_2 832 022 13 455 32 037 023 423
cert_ridgeSupport_suffix_decode_2 832 021 13 487 32 037 022 455
cert_ridgeSupport_suffix_decode_2 832 020 13 519 32 037 021 487
cert_ridgeSupport_suffix_decode_2 832 019 13 551 32 037 020 519
cert_ridgeSupport_suffix_decode_2 832 018 13 583 32 037 019 551
cert_ridgeSupport_suffix_decode_2 832 017 13 615 32 037 018 583
cert_ridgeSupport_suffix_decode_2 832 016 13 647 32 037 017 615
cert_ridgeSupport_suffix_decode_2 832 015 13 679 32 037 016 647
cert_ridgeSupport_suffix_decode_2 832 014 13 711 32 037 015 679
cert_ridgeSupport_suffix_decode_2 832 013 13 743 32 037 014 711
cert_ridgeSupport_suffix_decode_2 832 012 13 775 32 037 013 743
cert_ridgeSupport_suffix_decode_2 832 011 13 807 32 037 012 775
cert_ridgeSupport_suffix_decode_2 832 010 13 839 32 037 011 807
cert_ridgeSupport_suffix_decode_2 832 009 13 871 32 037 010 839
cert_ridgeSupport_suffix_decode_2 832 008 13 903 32 037 009 871
cert_ridgeSupport_suffix_decode_2 832 007 13 935 32 037 008 903
cert_ridgeSupport_suffix_decode_2 832 006 13 967 32 037 007 935
cert_ridgeSupport_suffix_decode_2 832 005 13 999 32 037 006 967
cert_ridgeSupport_suffix_decode_2 832 004 13 1031 32 037 005 999
cert_ridgeSupport_suffix_decode_2 832 003 13 1063 32 037 004 1031
cert_ridgeSupport_suffix_decode_2 832 002 13 1095 32 037 003 1063
cert_ridgeSupport_suffix_decode_2 832 001 13 1127 32 037 002 1095
cert_ridgeSupport_suffix_decode_2 832 000 13 1159 32 037 001 1127
cert_ridgeSupport_eq_2 832
theorem ridgeTest_large_832 : ridgeTest 832 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [show candidateRows 832 = ridgeSupport832_suffix_000 from ridgeSupport832_eq]
    simp only [ridgeSupport832_suffix_000, ridgeSupport832_suffix_001, ridgeSupport832_suffix_002, ridgeSupport832_suffix_003, ridgeSupport832_suffix_004, ridgeSupport832_suffix_005, ridgeSupport832_suffix_006, ridgeSupport832_suffix_007, ridgeSupport832_suffix_008, ridgeSupport832_suffix_009, ridgeSupport832_suffix_010, ridgeSupport832_suffix_011, ridgeSupport832_suffix_012, ridgeSupport832_suffix_013, ridgeSupport832_suffix_014, ridgeSupport832_suffix_015, ridgeSupport832_suffix_016, ridgeSupport832_suffix_017, ridgeSupport832_suffix_018, ridgeSupport832_suffix_019, ridgeSupport832_suffix_020, ridgeSupport832_suffix_021, ridgeSupport832_suffix_022, ridgeSupport832_suffix_023, ridgeSupport832_suffix_024, ridgeSupport832_suffix_025, ridgeSupport832_suffix_026, ridgeSupport832_suffix_027, ridgeSupport832_suffix_028, ridgeSupport832_suffix_029, ridgeSupport832_suffix_030, ridgeSupport832_suffix_031, ridgeSupport832_suffix_032, ridgeSupport832_suffix_033, ridgeSupport832_suffix_034, ridgeSupport832_suffix_035, ridgeSupport832_suffix_036, ridgeSupport832_suffix_037, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport832_000_mask, ridgeSupport832_001_mask, ridgeSupport832_002_mask, ridgeSupport832_003_mask, ridgeSupport832_004_mask, ridgeSupport832_005_mask, ridgeSupport832_006_mask, ridgeSupport832_007_mask, ridgeSupport832_008_mask, ridgeSupport832_009_mask, ridgeSupport832_010_mask, ridgeSupport832_011_mask, ridgeSupport832_012_mask, ridgeSupport832_013_mask, ridgeSupport832_014_mask, ridgeSupport832_015_mask, ridgeSupport832_016_mask, ridgeSupport832_017_mask, ridgeSupport832_018_mask, ridgeSupport832_019_mask, ridgeSupport832_020_mask, ridgeSupport832_021_mask, ridgeSupport832_022_mask, ridgeSupport832_023_mask, ridgeSupport832_024_mask, ridgeSupport832_025_mask, ridgeSupport832_026_mask, ridgeSupport832_027_mask, ridgeSupport832_028_mask, ridgeSupport832_029_mask, ridgeSupport832_030_mask, ridgeSupport832_031_mask, ridgeSupport832_032_mask, ridgeSupport832_033_mask, ridgeSupport832_034_mask, ridgeSupport832_035_mask, ridgeSupport832_036_mask]
    decide +kernel
  · rw [show candidateRows 832 = ridgeSupport832_suffix_000 from ridgeSupport832_eq]
    simp only [ridgeSupport832_suffix_000, ridgeSupport832_suffix_001, ridgeSupport832_suffix_002, ridgeSupport832_suffix_003, ridgeSupport832_suffix_004, ridgeSupport832_suffix_005, ridgeSupport832_suffix_006, ridgeSupport832_suffix_007, ridgeSupport832_suffix_008, ridgeSupport832_suffix_009, ridgeSupport832_suffix_010, ridgeSupport832_suffix_011, ridgeSupport832_suffix_012, ridgeSupport832_suffix_013, ridgeSupport832_suffix_014, ridgeSupport832_suffix_015, ridgeSupport832_suffix_016, ridgeSupport832_suffix_017, ridgeSupport832_suffix_018, ridgeSupport832_suffix_019, ridgeSupport832_suffix_020, ridgeSupport832_suffix_021, ridgeSupport832_suffix_022, ridgeSupport832_suffix_023, ridgeSupport832_suffix_024, ridgeSupport832_suffix_025, ridgeSupport832_suffix_026, ridgeSupport832_suffix_027, ridgeSupport832_suffix_028, ridgeSupport832_suffix_029, ridgeSupport832_suffix_030, ridgeSupport832_suffix_031, ridgeSupport832_suffix_032, ridgeSupport832_suffix_033, ridgeSupport832_suffix_034, ridgeSupport832_suffix_035, ridgeSupport832_suffix_036, ridgeSupport832_suffix_037, List.all_append, List.all_nil, ridgeSupport832_000_checked, ridgeSupport832_001_checked, ridgeSupport832_002_checked, ridgeSupport832_003_checked, ridgeSupport832_004_checked, ridgeSupport832_005_checked, ridgeSupport832_006_checked, ridgeSupport832_007_checked, ridgeSupport832_008_checked, ridgeSupport832_009_checked, ridgeSupport832_010_checked, ridgeSupport832_011_checked, ridgeSupport832_012_checked, ridgeSupport832_013_checked, ridgeSupport832_014_checked, ridgeSupport832_015_checked, ridgeSupport832_016_checked, ridgeSupport832_017_checked, ridgeSupport832_018_checked, ridgeSupport832_019_checked, ridgeSupport832_020_checked, ridgeSupport832_021_checked, ridgeSupport832_022_checked, ridgeSupport832_023_checked, ridgeSupport832_024_checked, ridgeSupport832_025_checked, ridgeSupport832_026_checked, ridgeSupport832_027_checked, ridgeSupport832_028_checked, ridgeSupport832_029_checked, ridgeSupport832_030_checked, ridgeSupport832_031_checked, ridgeSupport832_032_checked, ridgeSupport832_033_checked, ridgeSupport832_034_checked, ridgeSupport832_035_checked, ridgeSupport832_036_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase03
