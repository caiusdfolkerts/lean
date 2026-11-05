module
prelude
public import RootedSixBase03GrowthCacheRidgeSupport704Part000
public import RootedSixBase03GrowthCacheRidgeSupport704Part001
public import RootedSixBase03GrowthCacheRidgeSupport704Part002
public import RootedSixBase03GrowthCacheRidgeSupport704Part003
public import RootedSixBase03GrowthCacheRidgeSupport704Part004
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase03
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport704_suffix_decode_037 : PackedRawNatGrowth.readList 13 0 ridgeSupport704_rest_037 =
    (ridgeSupport704_suffix_037, ridgeSupport704_rest_037) := by rfl
theorem ridgeSupport704_suffix_decode_036 : PackedRawNatGrowth.readList 13 7 ridgeSupport704_rest_036 =
    (ridgeSupport704_suffix_036, ridgeSupport704_rest_037) :=
  PackedRawNatGrowth.readList_append_of_eq 13 7 0
    ridgeSupport704_rest_036 ridgeSupport704_rest_037 ridgeSupport704_rest_037
    ridgeSupport704_036 ridgeSupport704_suffix_037 ridgeSupport704_036_decode ridgeSupport704_suffix_decode_037
theorem ridgeSupport704_suffix_decode_035 : PackedRawNatGrowth.readList 13 39 ridgeSupport704_rest_035 =
    (ridgeSupport704_suffix_035, ridgeSupport704_rest_037) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 7
    ridgeSupport704_rest_035 ridgeSupport704_rest_036 ridgeSupport704_rest_037
    ridgeSupport704_035 ridgeSupport704_suffix_036 ridgeSupport704_035_decode ridgeSupport704_suffix_decode_036
theorem ridgeSupport704_suffix_decode_034 : PackedRawNatGrowth.readList 13 71 ridgeSupport704_rest_034 =
    (ridgeSupport704_suffix_034, ridgeSupport704_rest_037) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 39
    ridgeSupport704_rest_034 ridgeSupport704_rest_035 ridgeSupport704_rest_037
    ridgeSupport704_034 ridgeSupport704_suffix_035 ridgeSupport704_034_decode ridgeSupport704_suffix_decode_035
theorem ridgeSupport704_suffix_decode_033 : PackedRawNatGrowth.readList 13 103 ridgeSupport704_rest_033 =
    (ridgeSupport704_suffix_033, ridgeSupport704_rest_037) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 71
    ridgeSupport704_rest_033 ridgeSupport704_rest_034 ridgeSupport704_rest_037
    ridgeSupport704_033 ridgeSupport704_suffix_034 ridgeSupport704_033_decode ridgeSupport704_suffix_decode_034
theorem ridgeSupport704_suffix_decode_032 : PackedRawNatGrowth.readList 13 135 ridgeSupport704_rest_032 =
    (ridgeSupport704_suffix_032, ridgeSupport704_rest_037) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 103
    ridgeSupport704_rest_032 ridgeSupport704_rest_033 ridgeSupport704_rest_037
    ridgeSupport704_032 ridgeSupport704_suffix_033 ridgeSupport704_032_decode ridgeSupport704_suffix_decode_033
theorem ridgeSupport704_suffix_decode_031 : PackedRawNatGrowth.readList 13 167 ridgeSupport704_rest_031 =
    (ridgeSupport704_suffix_031, ridgeSupport704_rest_037) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 135
    ridgeSupport704_rest_031 ridgeSupport704_rest_032 ridgeSupport704_rest_037
    ridgeSupport704_031 ridgeSupport704_suffix_032 ridgeSupport704_031_decode ridgeSupport704_suffix_decode_032
theorem ridgeSupport704_suffix_decode_030 : PackedRawNatGrowth.readList 13 199 ridgeSupport704_rest_030 =
    (ridgeSupport704_suffix_030, ridgeSupport704_rest_037) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 167
    ridgeSupport704_rest_030 ridgeSupport704_rest_031 ridgeSupport704_rest_037
    ridgeSupport704_030 ridgeSupport704_suffix_031 ridgeSupport704_030_decode ridgeSupport704_suffix_decode_031
theorem ridgeSupport704_suffix_decode_029 : PackedRawNatGrowth.readList 13 231 ridgeSupport704_rest_029 =
    (ridgeSupport704_suffix_029, ridgeSupport704_rest_037) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 199
    ridgeSupport704_rest_029 ridgeSupport704_rest_030 ridgeSupport704_rest_037
    ridgeSupport704_029 ridgeSupport704_suffix_030 ridgeSupport704_029_decode ridgeSupport704_suffix_decode_030
theorem ridgeSupport704_suffix_decode_028 : PackedRawNatGrowth.readList 13 263 ridgeSupport704_rest_028 =
    (ridgeSupport704_suffix_028, ridgeSupport704_rest_037) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 231
    ridgeSupport704_rest_028 ridgeSupport704_rest_029 ridgeSupport704_rest_037
    ridgeSupport704_028 ridgeSupport704_suffix_029 ridgeSupport704_028_decode ridgeSupport704_suffix_decode_029
theorem ridgeSupport704_suffix_decode_027 : PackedRawNatGrowth.readList 13 295 ridgeSupport704_rest_027 =
    (ridgeSupport704_suffix_027, ridgeSupport704_rest_037) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 263
    ridgeSupport704_rest_027 ridgeSupport704_rest_028 ridgeSupport704_rest_037
    ridgeSupport704_027 ridgeSupport704_suffix_028 ridgeSupport704_027_decode ridgeSupport704_suffix_decode_028
theorem ridgeSupport704_suffix_decode_026 : PackedRawNatGrowth.readList 13 327 ridgeSupport704_rest_026 =
    (ridgeSupport704_suffix_026, ridgeSupport704_rest_037) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 295
    ridgeSupport704_rest_026 ridgeSupport704_rest_027 ridgeSupport704_rest_037
    ridgeSupport704_026 ridgeSupport704_suffix_027 ridgeSupport704_026_decode ridgeSupport704_suffix_decode_027
theorem ridgeSupport704_suffix_decode_025 : PackedRawNatGrowth.readList 13 359 ridgeSupport704_rest_025 =
    (ridgeSupport704_suffix_025, ridgeSupport704_rest_037) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 327
    ridgeSupport704_rest_025 ridgeSupport704_rest_026 ridgeSupport704_rest_037
    ridgeSupport704_025 ridgeSupport704_suffix_026 ridgeSupport704_025_decode ridgeSupport704_suffix_decode_026
theorem ridgeSupport704_suffix_decode_024 : PackedRawNatGrowth.readList 13 391 ridgeSupport704_rest_024 =
    (ridgeSupport704_suffix_024, ridgeSupport704_rest_037) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 359
    ridgeSupport704_rest_024 ridgeSupport704_rest_025 ridgeSupport704_rest_037
    ridgeSupport704_024 ridgeSupport704_suffix_025 ridgeSupport704_024_decode ridgeSupport704_suffix_decode_025
theorem ridgeSupport704_suffix_decode_023 : PackedRawNatGrowth.readList 13 423 ridgeSupport704_rest_023 =
    (ridgeSupport704_suffix_023, ridgeSupport704_rest_037) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 391
    ridgeSupport704_rest_023 ridgeSupport704_rest_024 ridgeSupport704_rest_037
    ridgeSupport704_023 ridgeSupport704_suffix_024 ridgeSupport704_023_decode ridgeSupport704_suffix_decode_024
theorem ridgeSupport704_suffix_decode_022 : PackedRawNatGrowth.readList 13 455 ridgeSupport704_rest_022 =
    (ridgeSupport704_suffix_022, ridgeSupport704_rest_037) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 423
    ridgeSupport704_rest_022 ridgeSupport704_rest_023 ridgeSupport704_rest_037
    ridgeSupport704_022 ridgeSupport704_suffix_023 ridgeSupport704_022_decode ridgeSupport704_suffix_decode_023
theorem ridgeSupport704_suffix_decode_021 : PackedRawNatGrowth.readList 13 487 ridgeSupport704_rest_021 =
    (ridgeSupport704_suffix_021, ridgeSupport704_rest_037) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 455
    ridgeSupport704_rest_021 ridgeSupport704_rest_022 ridgeSupport704_rest_037
    ridgeSupport704_021 ridgeSupport704_suffix_022 ridgeSupport704_021_decode ridgeSupport704_suffix_decode_022
theorem ridgeSupport704_suffix_decode_020 : PackedRawNatGrowth.readList 13 519 ridgeSupport704_rest_020 =
    (ridgeSupport704_suffix_020, ridgeSupport704_rest_037) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 487
    ridgeSupport704_rest_020 ridgeSupport704_rest_021 ridgeSupport704_rest_037
    ridgeSupport704_020 ridgeSupport704_suffix_021 ridgeSupport704_020_decode ridgeSupport704_suffix_decode_021
theorem ridgeSupport704_suffix_decode_019 : PackedRawNatGrowth.readList 13 551 ridgeSupport704_rest_019 =
    (ridgeSupport704_suffix_019, ridgeSupport704_rest_037) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 519
    ridgeSupport704_rest_019 ridgeSupport704_rest_020 ridgeSupport704_rest_037
    ridgeSupport704_019 ridgeSupport704_suffix_020 ridgeSupport704_019_decode ridgeSupport704_suffix_decode_020
theorem ridgeSupport704_suffix_decode_018 : PackedRawNatGrowth.readList 13 583 ridgeSupport704_rest_018 =
    (ridgeSupport704_suffix_018, ridgeSupport704_rest_037) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 551
    ridgeSupport704_rest_018 ridgeSupport704_rest_019 ridgeSupport704_rest_037
    ridgeSupport704_018 ridgeSupport704_suffix_019 ridgeSupport704_018_decode ridgeSupport704_suffix_decode_019
theorem ridgeSupport704_suffix_decode_017 : PackedRawNatGrowth.readList 13 615 ridgeSupport704_rest_017 =
    (ridgeSupport704_suffix_017, ridgeSupport704_rest_037) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 583
    ridgeSupport704_rest_017 ridgeSupport704_rest_018 ridgeSupport704_rest_037
    ridgeSupport704_017 ridgeSupport704_suffix_018 ridgeSupport704_017_decode ridgeSupport704_suffix_decode_018
theorem ridgeSupport704_suffix_decode_016 : PackedRawNatGrowth.readList 13 647 ridgeSupport704_rest_016 =
    (ridgeSupport704_suffix_016, ridgeSupport704_rest_037) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 615
    ridgeSupport704_rest_016 ridgeSupport704_rest_017 ridgeSupport704_rest_037
    ridgeSupport704_016 ridgeSupport704_suffix_017 ridgeSupport704_016_decode ridgeSupport704_suffix_decode_017
theorem ridgeSupport704_suffix_decode_015 : PackedRawNatGrowth.readList 13 679 ridgeSupport704_rest_015 =
    (ridgeSupport704_suffix_015, ridgeSupport704_rest_037) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 647
    ridgeSupport704_rest_015 ridgeSupport704_rest_016 ridgeSupport704_rest_037
    ridgeSupport704_015 ridgeSupport704_suffix_016 ridgeSupport704_015_decode ridgeSupport704_suffix_decode_016
theorem ridgeSupport704_suffix_decode_014 : PackedRawNatGrowth.readList 13 711 ridgeSupport704_rest_014 =
    (ridgeSupport704_suffix_014, ridgeSupport704_rest_037) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 679
    ridgeSupport704_rest_014 ridgeSupport704_rest_015 ridgeSupport704_rest_037
    ridgeSupport704_014 ridgeSupport704_suffix_015 ridgeSupport704_014_decode ridgeSupport704_suffix_decode_015
theorem ridgeSupport704_suffix_decode_013 : PackedRawNatGrowth.readList 13 743 ridgeSupport704_rest_013 =
    (ridgeSupport704_suffix_013, ridgeSupport704_rest_037) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 711
    ridgeSupport704_rest_013 ridgeSupport704_rest_014 ridgeSupport704_rest_037
    ridgeSupport704_013 ridgeSupport704_suffix_014 ridgeSupport704_013_decode ridgeSupport704_suffix_decode_014
theorem ridgeSupport704_suffix_decode_012 : PackedRawNatGrowth.readList 13 775 ridgeSupport704_rest_012 =
    (ridgeSupport704_suffix_012, ridgeSupport704_rest_037) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 743
    ridgeSupport704_rest_012 ridgeSupport704_rest_013 ridgeSupport704_rest_037
    ridgeSupport704_012 ridgeSupport704_suffix_013 ridgeSupport704_012_decode ridgeSupport704_suffix_decode_013
theorem ridgeSupport704_suffix_decode_011 : PackedRawNatGrowth.readList 13 807 ridgeSupport704_rest_011 =
    (ridgeSupport704_suffix_011, ridgeSupport704_rest_037) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 775
    ridgeSupport704_rest_011 ridgeSupport704_rest_012 ridgeSupport704_rest_037
    ridgeSupport704_011 ridgeSupport704_suffix_012 ridgeSupport704_011_decode ridgeSupport704_suffix_decode_012
theorem ridgeSupport704_suffix_decode_010 : PackedRawNatGrowth.readList 13 839 ridgeSupport704_rest_010 =
    (ridgeSupport704_suffix_010, ridgeSupport704_rest_037) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 807
    ridgeSupport704_rest_010 ridgeSupport704_rest_011 ridgeSupport704_rest_037
    ridgeSupport704_010 ridgeSupport704_suffix_011 ridgeSupport704_010_decode ridgeSupport704_suffix_decode_011
theorem ridgeSupport704_suffix_decode_009 : PackedRawNatGrowth.readList 13 871 ridgeSupport704_rest_009 =
    (ridgeSupport704_suffix_009, ridgeSupport704_rest_037) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 839
    ridgeSupport704_rest_009 ridgeSupport704_rest_010 ridgeSupport704_rest_037
    ridgeSupport704_009 ridgeSupport704_suffix_010 ridgeSupport704_009_decode ridgeSupport704_suffix_decode_010
theorem ridgeSupport704_suffix_decode_008 : PackedRawNatGrowth.readList 13 903 ridgeSupport704_rest_008 =
    (ridgeSupport704_suffix_008, ridgeSupport704_rest_037) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 871
    ridgeSupport704_rest_008 ridgeSupport704_rest_009 ridgeSupport704_rest_037
    ridgeSupport704_008 ridgeSupport704_suffix_009 ridgeSupport704_008_decode ridgeSupport704_suffix_decode_009
theorem ridgeSupport704_suffix_decode_007 : PackedRawNatGrowth.readList 13 935 ridgeSupport704_rest_007 =
    (ridgeSupport704_suffix_007, ridgeSupport704_rest_037) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 903
    ridgeSupport704_rest_007 ridgeSupport704_rest_008 ridgeSupport704_rest_037
    ridgeSupport704_007 ridgeSupport704_suffix_008 ridgeSupport704_007_decode ridgeSupport704_suffix_decode_008
theorem ridgeSupport704_suffix_decode_006 : PackedRawNatGrowth.readList 13 967 ridgeSupport704_rest_006 =
    (ridgeSupport704_suffix_006, ridgeSupport704_rest_037) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 935
    ridgeSupport704_rest_006 ridgeSupport704_rest_007 ridgeSupport704_rest_037
    ridgeSupport704_006 ridgeSupport704_suffix_007 ridgeSupport704_006_decode ridgeSupport704_suffix_decode_007
theorem ridgeSupport704_suffix_decode_005 : PackedRawNatGrowth.readList 13 999 ridgeSupport704_rest_005 =
    (ridgeSupport704_suffix_005, ridgeSupport704_rest_037) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 967
    ridgeSupport704_rest_005 ridgeSupport704_rest_006 ridgeSupport704_rest_037
    ridgeSupport704_005 ridgeSupport704_suffix_006 ridgeSupport704_005_decode ridgeSupport704_suffix_decode_006
theorem ridgeSupport704_suffix_decode_004 : PackedRawNatGrowth.readList 13 1031 ridgeSupport704_rest_004 =
    (ridgeSupport704_suffix_004, ridgeSupport704_rest_037) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 999
    ridgeSupport704_rest_004 ridgeSupport704_rest_005 ridgeSupport704_rest_037
    ridgeSupport704_004 ridgeSupport704_suffix_005 ridgeSupport704_004_decode ridgeSupport704_suffix_decode_005
theorem ridgeSupport704_suffix_decode_003 : PackedRawNatGrowth.readList 13 1063 ridgeSupport704_rest_003 =
    (ridgeSupport704_suffix_003, ridgeSupport704_rest_037) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 1031
    ridgeSupport704_rest_003 ridgeSupport704_rest_004 ridgeSupport704_rest_037
    ridgeSupport704_003 ridgeSupport704_suffix_004 ridgeSupport704_003_decode ridgeSupport704_suffix_decode_004
theorem ridgeSupport704_suffix_decode_002 : PackedRawNatGrowth.readList 13 1095 ridgeSupport704_rest_002 =
    (ridgeSupport704_suffix_002, ridgeSupport704_rest_037) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 1063
    ridgeSupport704_rest_002 ridgeSupport704_rest_003 ridgeSupport704_rest_037
    ridgeSupport704_002 ridgeSupport704_suffix_003 ridgeSupport704_002_decode ridgeSupport704_suffix_decode_003
theorem ridgeSupport704_suffix_decode_001 : PackedRawNatGrowth.readList 13 1127 ridgeSupport704_rest_001 =
    (ridgeSupport704_suffix_001, ridgeSupport704_rest_037) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 1095
    ridgeSupport704_rest_001 ridgeSupport704_rest_002 ridgeSupport704_rest_037
    ridgeSupport704_001 ridgeSupport704_suffix_002 ridgeSupport704_001_decode ridgeSupport704_suffix_decode_002
theorem ridgeSupport704_suffix_decode_000 : PackedRawNatGrowth.readList 13 1159 ridgeSupport704_rest_000 =
    (ridgeSupport704_suffix_000, ridgeSupport704_rest_037) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 1127
    ridgeSupport704_rest_000 ridgeSupport704_rest_001 ridgeSupport704_rest_037
    ridgeSupport704_000 ridgeSupport704_suffix_001 ridgeSupport704_000_decode ridgeSupport704_suffix_decode_001
theorem ridgeSupport704_eq : candidateSupports 704 = ridgeSupport704_suffix_000 := by
  rw [ridgeSupport704_source]
  exact congrArg Prod.fst ridgeSupport704_suffix_decode_000
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
