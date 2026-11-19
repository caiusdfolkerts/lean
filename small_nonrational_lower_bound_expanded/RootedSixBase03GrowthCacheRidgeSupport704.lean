module
prelude
public meta import LowerSchemas.FiniteRootedSixBase.Part0
public import RootedSixBase03GrowthCacheRidgeSupport704PartGrouped000
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase03
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
cert_ridgeSupport_suffix_decode 704 037 13
cert_ridgeSupport_suffix_decode_2 704 036 13 7 7 037 037 0
cert_ridgeSupport_suffix_decode_2 704 035 13 39 32 037 036 7
cert_ridgeSupport_suffix_decode_2 704 034 13 71 32 037 035 39
cert_ridgeSupport_suffix_decode_2 704 033 13 103 32 037 034 71
cert_ridgeSupport_suffix_decode_2 704 032 13 135 32 037 033 103
cert_ridgeSupport_suffix_decode_2 704 031 13 167 32 037 032 135
cert_ridgeSupport_suffix_decode_2 704 030 13 199 32 037 031 167
cert_ridgeSupport_suffix_decode_2 704 029 13 231 32 037 030 199
cert_ridgeSupport_suffix_decode_2 704 028 13 263 32 037 029 231
cert_ridgeSupport_suffix_decode_2 704 027 13 295 32 037 028 263
cert_ridgeSupport_suffix_decode_2 704 026 13 327 32 037 027 295
cert_ridgeSupport_suffix_decode_2 704 025 13 359 32 037 026 327
cert_ridgeSupport_suffix_decode_2 704 024 13 391 32 037 025 359
cert_ridgeSupport_suffix_decode_2 704 023 13 423 32 037 024 391
cert_ridgeSupport_suffix_decode_2 704 022 13 455 32 037 023 423
cert_ridgeSupport_suffix_decode_2 704 021 13 487 32 037 022 455
cert_ridgeSupport_suffix_decode_2 704 020 13 519 32 037 021 487
cert_ridgeSupport_suffix_decode_2 704 019 13 551 32 037 020 519
cert_ridgeSupport_suffix_decode_2 704 018 13 583 32 037 019 551
cert_ridgeSupport_suffix_decode_2 704 017 13 615 32 037 018 583
cert_ridgeSupport_suffix_decode_2 704 016 13 647 32 037 017 615
cert_ridgeSupport_suffix_decode_2 704 015 13 679 32 037 016 647
cert_ridgeSupport_suffix_decode_2 704 014 13 711 32 037 015 679
cert_ridgeSupport_suffix_decode_2 704 013 13 743 32 037 014 711
cert_ridgeSupport_suffix_decode_2 704 012 13 775 32 037 013 743
cert_ridgeSupport_suffix_decode_2 704 011 13 807 32 037 012 775
cert_ridgeSupport_suffix_decode_2 704 010 13 839 32 037 011 807
cert_ridgeSupport_suffix_decode_2 704 009 13 871 32 037 010 839
cert_ridgeSupport_suffix_decode_2 704 008 13 903 32 037 009 871
cert_ridgeSupport_suffix_decode_2 704 007 13 935 32 037 008 903
cert_ridgeSupport_suffix_decode_2 704 006 13 967 32 037 007 935
cert_ridgeSupport_suffix_decode_2 704 005 13 999 32 037 006 967
cert_ridgeSupport_suffix_decode_2 704 004 13 1031 32 037 005 999
cert_ridgeSupport_suffix_decode_2 704 003 13 1063 32 037 004 1031
cert_ridgeSupport_suffix_decode_2 704 002 13 1095 32 037 003 1063
cert_ridgeSupport_suffix_decode_2 704 001 13 1127 32 037 002 1095
cert_ridgeSupport_suffix_decode_2 704 000 13 1159 32 037 001 1127
cert_ridgeSupport_eq_2 704
theorem ridgeTest_large_704 : ridgeTest 704 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [show candidateRows 704 = ridgeSupport704_suffix_000 from ridgeSupport704_eq]
    simp only [ridgeSupport704_suffix_000, ridgeSupport704_suffix_001, ridgeSupport704_suffix_002, ridgeSupport704_suffix_003, ridgeSupport704_suffix_004, ridgeSupport704_suffix_005, ridgeSupport704_suffix_006, ridgeSupport704_suffix_007, ridgeSupport704_suffix_008, ridgeSupport704_suffix_009, ridgeSupport704_suffix_010, ridgeSupport704_suffix_011, ridgeSupport704_suffix_012, ridgeSupport704_suffix_013, ridgeSupport704_suffix_014, ridgeSupport704_suffix_015, ridgeSupport704_suffix_016, ridgeSupport704_suffix_017, ridgeSupport704_suffix_018, ridgeSupport704_suffix_019, ridgeSupport704_suffix_020, ridgeSupport704_suffix_021, ridgeSupport704_suffix_022, ridgeSupport704_suffix_023, ridgeSupport704_suffix_024, ridgeSupport704_suffix_025, ridgeSupport704_suffix_026, ridgeSupport704_suffix_027, ridgeSupport704_suffix_028, ridgeSupport704_suffix_029, ridgeSupport704_suffix_030, ridgeSupport704_suffix_031, ridgeSupport704_suffix_032, ridgeSupport704_suffix_033, ridgeSupport704_suffix_034, ridgeSupport704_suffix_035, ridgeSupport704_suffix_036, ridgeSupport704_suffix_037, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport704_000_mask, ridgeSupport704_001_mask, ridgeSupport704_002_mask, ridgeSupport704_003_mask, ridgeSupport704_004_mask, ridgeSupport704_005_mask, ridgeSupport704_006_mask, ridgeSupport704_007_mask, ridgeSupport704_008_mask, ridgeSupport704_009_mask, ridgeSupport704_010_mask, ridgeSupport704_011_mask, ridgeSupport704_012_mask, ridgeSupport704_013_mask, ridgeSupport704_014_mask, ridgeSupport704_015_mask, ridgeSupport704_016_mask, ridgeSupport704_017_mask, ridgeSupport704_018_mask, ridgeSupport704_019_mask, ridgeSupport704_020_mask, ridgeSupport704_021_mask, ridgeSupport704_022_mask, ridgeSupport704_023_mask, ridgeSupport704_024_mask, ridgeSupport704_025_mask, ridgeSupport704_026_mask, ridgeSupport704_027_mask, ridgeSupport704_028_mask, ridgeSupport704_029_mask, ridgeSupport704_030_mask, ridgeSupport704_031_mask, ridgeSupport704_032_mask, ridgeSupport704_033_mask, ridgeSupport704_034_mask, ridgeSupport704_035_mask, ridgeSupport704_036_mask]
    decide +kernel
  · rw [show candidateRows 704 = ridgeSupport704_suffix_000 from ridgeSupport704_eq]
    simp only [ridgeSupport704_suffix_000, ridgeSupport704_suffix_001, ridgeSupport704_suffix_002, ridgeSupport704_suffix_003, ridgeSupport704_suffix_004, ridgeSupport704_suffix_005, ridgeSupport704_suffix_006, ridgeSupport704_suffix_007, ridgeSupport704_suffix_008, ridgeSupport704_suffix_009, ridgeSupport704_suffix_010, ridgeSupport704_suffix_011, ridgeSupport704_suffix_012, ridgeSupport704_suffix_013, ridgeSupport704_suffix_014, ridgeSupport704_suffix_015, ridgeSupport704_suffix_016, ridgeSupport704_suffix_017, ridgeSupport704_suffix_018, ridgeSupport704_suffix_019, ridgeSupport704_suffix_020, ridgeSupport704_suffix_021, ridgeSupport704_suffix_022, ridgeSupport704_suffix_023, ridgeSupport704_suffix_024, ridgeSupport704_suffix_025, ridgeSupport704_suffix_026, ridgeSupport704_suffix_027, ridgeSupport704_suffix_028, ridgeSupport704_suffix_029, ridgeSupport704_suffix_030, ridgeSupport704_suffix_031, ridgeSupport704_suffix_032, ridgeSupport704_suffix_033, ridgeSupport704_suffix_034, ridgeSupport704_suffix_035, ridgeSupport704_suffix_036, ridgeSupport704_suffix_037, List.all_append, List.all_nil, ridgeSupport704_000_checked, ridgeSupport704_001_checked, ridgeSupport704_002_checked, ridgeSupport704_003_checked, ridgeSupport704_004_checked, ridgeSupport704_005_checked, ridgeSupport704_006_checked, ridgeSupport704_007_checked, ridgeSupport704_008_checked, ridgeSupport704_009_checked, ridgeSupport704_010_checked, ridgeSupport704_011_checked, ridgeSupport704_012_checked, ridgeSupport704_013_checked, ridgeSupport704_014_checked, ridgeSupport704_015_checked, ridgeSupport704_016_checked, ridgeSupport704_017_checked, ridgeSupport704_018_checked, ridgeSupport704_019_checked, ridgeSupport704_020_checked, ridgeSupport704_021_checked, ridgeSupport704_022_checked, ridgeSupport704_023_checked, ridgeSupport704_024_checked, ridgeSupport704_025_checked, ridgeSupport704_026_checked, ridgeSupport704_027_checked, ridgeSupport704_028_checked, ridgeSupport704_029_checked, ridgeSupport704_030_checked, ridgeSupport704_031_checked, ridgeSupport704_032_checked, ridgeSupport704_033_checked, ridgeSupport704_034_checked, ridgeSupport704_035_checked, ridgeSupport704_036_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase03
