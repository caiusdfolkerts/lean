module
prelude
public meta import LowerSchemas.FiniteRootedSixBase.Part0
public import RootedSixBase03GrowthCacheRidgeSupport448PartGrouped000
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase03
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
cert_ridgeSupport_suffix_decode 448 037 13
cert_ridgeSupport_suffix_decode_2 448 036 13 7 7 037 037 0
cert_ridgeSupport_suffix_decode_2 448 035 13 39 32 037 036 7
cert_ridgeSupport_suffix_decode_2 448 034 13 71 32 037 035 39
cert_ridgeSupport_suffix_decode_2 448 033 13 103 32 037 034 71
cert_ridgeSupport_suffix_decode_2 448 032 13 135 32 037 033 103
cert_ridgeSupport_suffix_decode_2 448 031 13 167 32 037 032 135
cert_ridgeSupport_suffix_decode_2 448 030 13 199 32 037 031 167
cert_ridgeSupport_suffix_decode_2 448 029 13 231 32 037 030 199
cert_ridgeSupport_suffix_decode_2 448 028 13 263 32 037 029 231
cert_ridgeSupport_suffix_decode_2 448 027 13 295 32 037 028 263
cert_ridgeSupport_suffix_decode_2 448 026 13 327 32 037 027 295
cert_ridgeSupport_suffix_decode_2 448 025 13 359 32 037 026 327
cert_ridgeSupport_suffix_decode_2 448 024 13 391 32 037 025 359
cert_ridgeSupport_suffix_decode_2 448 023 13 423 32 037 024 391
cert_ridgeSupport_suffix_decode_2 448 022 13 455 32 037 023 423
cert_ridgeSupport_suffix_decode_2 448 021 13 487 32 037 022 455
cert_ridgeSupport_suffix_decode_2 448 020 13 519 32 037 021 487
cert_ridgeSupport_suffix_decode_2 448 019 13 551 32 037 020 519
cert_ridgeSupport_suffix_decode_2 448 018 13 583 32 037 019 551
cert_ridgeSupport_suffix_decode_2 448 017 13 615 32 037 018 583
cert_ridgeSupport_suffix_decode_2 448 016 13 647 32 037 017 615
cert_ridgeSupport_suffix_decode_2 448 015 13 679 32 037 016 647
cert_ridgeSupport_suffix_decode_2 448 014 13 711 32 037 015 679
cert_ridgeSupport_suffix_decode_2 448 013 13 743 32 037 014 711
cert_ridgeSupport_suffix_decode_2 448 012 13 775 32 037 013 743
cert_ridgeSupport_suffix_decode_2 448 011 13 807 32 037 012 775
cert_ridgeSupport_suffix_decode_2 448 010 13 839 32 037 011 807
cert_ridgeSupport_suffix_decode_2 448 009 13 871 32 037 010 839
cert_ridgeSupport_suffix_decode_2 448 008 13 903 32 037 009 871
cert_ridgeSupport_suffix_decode_2 448 007 13 935 32 037 008 903
cert_ridgeSupport_suffix_decode_2 448 006 13 967 32 037 007 935
cert_ridgeSupport_suffix_decode_2 448 005 13 999 32 037 006 967
cert_ridgeSupport_suffix_decode_2 448 004 13 1031 32 037 005 999
cert_ridgeSupport_suffix_decode_2 448 003 13 1063 32 037 004 1031
cert_ridgeSupport_suffix_decode_2 448 002 13 1095 32 037 003 1063
cert_ridgeSupport_suffix_decode_2 448 001 13 1127 32 037 002 1095
cert_ridgeSupport_suffix_decode_2 448 000 13 1159 32 037 001 1127
cert_ridgeSupport_eq_2 448
theorem ridgeTest_large_448 : ridgeTest 448 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [show candidateRows 448 = ridgeSupport448_suffix_000 from ridgeSupport448_eq]
    simp only [ridgeSupport448_suffix_000, ridgeSupport448_suffix_001, ridgeSupport448_suffix_002, ridgeSupport448_suffix_003, ridgeSupport448_suffix_004, ridgeSupport448_suffix_005, ridgeSupport448_suffix_006, ridgeSupport448_suffix_007, ridgeSupport448_suffix_008, ridgeSupport448_suffix_009, ridgeSupport448_suffix_010, ridgeSupport448_suffix_011, ridgeSupport448_suffix_012, ridgeSupport448_suffix_013, ridgeSupport448_suffix_014, ridgeSupport448_suffix_015, ridgeSupport448_suffix_016, ridgeSupport448_suffix_017, ridgeSupport448_suffix_018, ridgeSupport448_suffix_019, ridgeSupport448_suffix_020, ridgeSupport448_suffix_021, ridgeSupport448_suffix_022, ridgeSupport448_suffix_023, ridgeSupport448_suffix_024, ridgeSupport448_suffix_025, ridgeSupport448_suffix_026, ridgeSupport448_suffix_027, ridgeSupport448_suffix_028, ridgeSupport448_suffix_029, ridgeSupport448_suffix_030, ridgeSupport448_suffix_031, ridgeSupport448_suffix_032, ridgeSupport448_suffix_033, ridgeSupport448_suffix_034, ridgeSupport448_suffix_035, ridgeSupport448_suffix_036, ridgeSupport448_suffix_037, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport448_000_mask, ridgeSupport448_001_mask, ridgeSupport448_002_mask, ridgeSupport448_003_mask, ridgeSupport448_004_mask, ridgeSupport448_005_mask, ridgeSupport448_006_mask, ridgeSupport448_007_mask, ridgeSupport448_008_mask, ridgeSupport448_009_mask, ridgeSupport448_010_mask, ridgeSupport448_011_mask, ridgeSupport448_012_mask, ridgeSupport448_013_mask, ridgeSupport448_014_mask, ridgeSupport448_015_mask, ridgeSupport448_016_mask, ridgeSupport448_017_mask, ridgeSupport448_018_mask, ridgeSupport448_019_mask, ridgeSupport448_020_mask, ridgeSupport448_021_mask, ridgeSupport448_022_mask, ridgeSupport448_023_mask, ridgeSupport448_024_mask, ridgeSupport448_025_mask, ridgeSupport448_026_mask, ridgeSupport448_027_mask, ridgeSupport448_028_mask, ridgeSupport448_029_mask, ridgeSupport448_030_mask, ridgeSupport448_031_mask, ridgeSupport448_032_mask, ridgeSupport448_033_mask, ridgeSupport448_034_mask, ridgeSupport448_035_mask, ridgeSupport448_036_mask]
    decide +kernel
  · rw [show candidateRows 448 = ridgeSupport448_suffix_000 from ridgeSupport448_eq]
    simp only [ridgeSupport448_suffix_000, ridgeSupport448_suffix_001, ridgeSupport448_suffix_002, ridgeSupport448_suffix_003, ridgeSupport448_suffix_004, ridgeSupport448_suffix_005, ridgeSupport448_suffix_006, ridgeSupport448_suffix_007, ridgeSupport448_suffix_008, ridgeSupport448_suffix_009, ridgeSupport448_suffix_010, ridgeSupport448_suffix_011, ridgeSupport448_suffix_012, ridgeSupport448_suffix_013, ridgeSupport448_suffix_014, ridgeSupport448_suffix_015, ridgeSupport448_suffix_016, ridgeSupport448_suffix_017, ridgeSupport448_suffix_018, ridgeSupport448_suffix_019, ridgeSupport448_suffix_020, ridgeSupport448_suffix_021, ridgeSupport448_suffix_022, ridgeSupport448_suffix_023, ridgeSupport448_suffix_024, ridgeSupport448_suffix_025, ridgeSupport448_suffix_026, ridgeSupport448_suffix_027, ridgeSupport448_suffix_028, ridgeSupport448_suffix_029, ridgeSupport448_suffix_030, ridgeSupport448_suffix_031, ridgeSupport448_suffix_032, ridgeSupport448_suffix_033, ridgeSupport448_suffix_034, ridgeSupport448_suffix_035, ridgeSupport448_suffix_036, ridgeSupport448_suffix_037, List.all_append, List.all_nil, ridgeSupport448_000_checked, ridgeSupport448_001_checked, ridgeSupport448_002_checked, ridgeSupport448_003_checked, ridgeSupport448_004_checked, ridgeSupport448_005_checked, ridgeSupport448_006_checked, ridgeSupport448_007_checked, ridgeSupport448_008_checked, ridgeSupport448_009_checked, ridgeSupport448_010_checked, ridgeSupport448_011_checked, ridgeSupport448_012_checked, ridgeSupport448_013_checked, ridgeSupport448_014_checked, ridgeSupport448_015_checked, ridgeSupport448_016_checked, ridgeSupport448_017_checked, ridgeSupport448_018_checked, ridgeSupport448_019_checked, ridgeSupport448_020_checked, ridgeSupport448_021_checked, ridgeSupport448_022_checked, ridgeSupport448_023_checked, ridgeSupport448_024_checked, ridgeSupport448_025_checked, ridgeSupport448_026_checked, ridgeSupport448_027_checked, ridgeSupport448_028_checked, ridgeSupport448_029_checked, ridgeSupport448_030_checked, ridgeSupport448_031_checked, ridgeSupport448_032_checked, ridgeSupport448_033_checked, ridgeSupport448_034_checked, ridgeSupport448_035_checked, ridgeSupport448_036_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase03
