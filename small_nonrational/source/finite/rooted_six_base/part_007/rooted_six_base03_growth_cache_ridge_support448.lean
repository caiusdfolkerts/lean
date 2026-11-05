module
prelude
public import RootedSixBase03GrowthCacheRidgeSupport448Part000
public import RootedSixBase03GrowthCacheRidgeSupport448Part001
public import RootedSixBase03GrowthCacheRidgeSupport448Part002
public import RootedSixBase03GrowthCacheRidgeSupport448Part003
public import RootedSixBase03GrowthCacheRidgeSupport448Part004
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase03
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport448_suffix_decode_037 : PackedRawNatGrowth.readList 13 0 ridgeSupport448_rest_037 =
    (ridgeSupport448_suffix_037, ridgeSupport448_rest_037) := by rfl
theorem ridgeSupport448_suffix_decode_036 : PackedRawNatGrowth.readList 13 7 ridgeSupport448_rest_036 =
    (ridgeSupport448_suffix_036, ridgeSupport448_rest_037) :=
  PackedRawNatGrowth.readList_append_of_eq 13 7 0
    ridgeSupport448_rest_036 ridgeSupport448_rest_037 ridgeSupport448_rest_037
    ridgeSupport448_036 ridgeSupport448_suffix_037 ridgeSupport448_036_decode ridgeSupport448_suffix_decode_037
theorem ridgeSupport448_suffix_decode_035 : PackedRawNatGrowth.readList 13 39 ridgeSupport448_rest_035 =
    (ridgeSupport448_suffix_035, ridgeSupport448_rest_037) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 7
    ridgeSupport448_rest_035 ridgeSupport448_rest_036 ridgeSupport448_rest_037
    ridgeSupport448_035 ridgeSupport448_suffix_036 ridgeSupport448_035_decode ridgeSupport448_suffix_decode_036
theorem ridgeSupport448_suffix_decode_034 : PackedRawNatGrowth.readList 13 71 ridgeSupport448_rest_034 =
    (ridgeSupport448_suffix_034, ridgeSupport448_rest_037) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 39
    ridgeSupport448_rest_034 ridgeSupport448_rest_035 ridgeSupport448_rest_037
    ridgeSupport448_034 ridgeSupport448_suffix_035 ridgeSupport448_034_decode ridgeSupport448_suffix_decode_035
theorem ridgeSupport448_suffix_decode_033 : PackedRawNatGrowth.readList 13 103 ridgeSupport448_rest_033 =
    (ridgeSupport448_suffix_033, ridgeSupport448_rest_037) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 71
    ridgeSupport448_rest_033 ridgeSupport448_rest_034 ridgeSupport448_rest_037
    ridgeSupport448_033 ridgeSupport448_suffix_034 ridgeSupport448_033_decode ridgeSupport448_suffix_decode_034
theorem ridgeSupport448_suffix_decode_032 : PackedRawNatGrowth.readList 13 135 ridgeSupport448_rest_032 =
    (ridgeSupport448_suffix_032, ridgeSupport448_rest_037) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 103
    ridgeSupport448_rest_032 ridgeSupport448_rest_033 ridgeSupport448_rest_037
    ridgeSupport448_032 ridgeSupport448_suffix_033 ridgeSupport448_032_decode ridgeSupport448_suffix_decode_033
theorem ridgeSupport448_suffix_decode_031 : PackedRawNatGrowth.readList 13 167 ridgeSupport448_rest_031 =
    (ridgeSupport448_suffix_031, ridgeSupport448_rest_037) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 135
    ridgeSupport448_rest_031 ridgeSupport448_rest_032 ridgeSupport448_rest_037
    ridgeSupport448_031 ridgeSupport448_suffix_032 ridgeSupport448_031_decode ridgeSupport448_suffix_decode_032
theorem ridgeSupport448_suffix_decode_030 : PackedRawNatGrowth.readList 13 199 ridgeSupport448_rest_030 =
    (ridgeSupport448_suffix_030, ridgeSupport448_rest_037) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 167
    ridgeSupport448_rest_030 ridgeSupport448_rest_031 ridgeSupport448_rest_037
    ridgeSupport448_030 ridgeSupport448_suffix_031 ridgeSupport448_030_decode ridgeSupport448_suffix_decode_031
theorem ridgeSupport448_suffix_decode_029 : PackedRawNatGrowth.readList 13 231 ridgeSupport448_rest_029 =
    (ridgeSupport448_suffix_029, ridgeSupport448_rest_037) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 199
    ridgeSupport448_rest_029 ridgeSupport448_rest_030 ridgeSupport448_rest_037
    ridgeSupport448_029 ridgeSupport448_suffix_030 ridgeSupport448_029_decode ridgeSupport448_suffix_decode_030
theorem ridgeSupport448_suffix_decode_028 : PackedRawNatGrowth.readList 13 263 ridgeSupport448_rest_028 =
    (ridgeSupport448_suffix_028, ridgeSupport448_rest_037) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 231
    ridgeSupport448_rest_028 ridgeSupport448_rest_029 ridgeSupport448_rest_037
    ridgeSupport448_028 ridgeSupport448_suffix_029 ridgeSupport448_028_decode ridgeSupport448_suffix_decode_029
theorem ridgeSupport448_suffix_decode_027 : PackedRawNatGrowth.readList 13 295 ridgeSupport448_rest_027 =
    (ridgeSupport448_suffix_027, ridgeSupport448_rest_037) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 263
    ridgeSupport448_rest_027 ridgeSupport448_rest_028 ridgeSupport448_rest_037
    ridgeSupport448_027 ridgeSupport448_suffix_028 ridgeSupport448_027_decode ridgeSupport448_suffix_decode_028
theorem ridgeSupport448_suffix_decode_026 : PackedRawNatGrowth.readList 13 327 ridgeSupport448_rest_026 =
    (ridgeSupport448_suffix_026, ridgeSupport448_rest_037) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 295
    ridgeSupport448_rest_026 ridgeSupport448_rest_027 ridgeSupport448_rest_037
    ridgeSupport448_026 ridgeSupport448_suffix_027 ridgeSupport448_026_decode ridgeSupport448_suffix_decode_027
theorem ridgeSupport448_suffix_decode_025 : PackedRawNatGrowth.readList 13 359 ridgeSupport448_rest_025 =
    (ridgeSupport448_suffix_025, ridgeSupport448_rest_037) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 327
    ridgeSupport448_rest_025 ridgeSupport448_rest_026 ridgeSupport448_rest_037
    ridgeSupport448_025 ridgeSupport448_suffix_026 ridgeSupport448_025_decode ridgeSupport448_suffix_decode_026
theorem ridgeSupport448_suffix_decode_024 : PackedRawNatGrowth.readList 13 391 ridgeSupport448_rest_024 =
    (ridgeSupport448_suffix_024, ridgeSupport448_rest_037) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 359
    ridgeSupport448_rest_024 ridgeSupport448_rest_025 ridgeSupport448_rest_037
    ridgeSupport448_024 ridgeSupport448_suffix_025 ridgeSupport448_024_decode ridgeSupport448_suffix_decode_025
theorem ridgeSupport448_suffix_decode_023 : PackedRawNatGrowth.readList 13 423 ridgeSupport448_rest_023 =
    (ridgeSupport448_suffix_023, ridgeSupport448_rest_037) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 391
    ridgeSupport448_rest_023 ridgeSupport448_rest_024 ridgeSupport448_rest_037
    ridgeSupport448_023 ridgeSupport448_suffix_024 ridgeSupport448_023_decode ridgeSupport448_suffix_decode_024
theorem ridgeSupport448_suffix_decode_022 : PackedRawNatGrowth.readList 13 455 ridgeSupport448_rest_022 =
    (ridgeSupport448_suffix_022, ridgeSupport448_rest_037) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 423
    ridgeSupport448_rest_022 ridgeSupport448_rest_023 ridgeSupport448_rest_037
    ridgeSupport448_022 ridgeSupport448_suffix_023 ridgeSupport448_022_decode ridgeSupport448_suffix_decode_023
theorem ridgeSupport448_suffix_decode_021 : PackedRawNatGrowth.readList 13 487 ridgeSupport448_rest_021 =
    (ridgeSupport448_suffix_021, ridgeSupport448_rest_037) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 455
    ridgeSupport448_rest_021 ridgeSupport448_rest_022 ridgeSupport448_rest_037
    ridgeSupport448_021 ridgeSupport448_suffix_022 ridgeSupport448_021_decode ridgeSupport448_suffix_decode_022
theorem ridgeSupport448_suffix_decode_020 : PackedRawNatGrowth.readList 13 519 ridgeSupport448_rest_020 =
    (ridgeSupport448_suffix_020, ridgeSupport448_rest_037) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 487
    ridgeSupport448_rest_020 ridgeSupport448_rest_021 ridgeSupport448_rest_037
    ridgeSupport448_020 ridgeSupport448_suffix_021 ridgeSupport448_020_decode ridgeSupport448_suffix_decode_021
theorem ridgeSupport448_suffix_decode_019 : PackedRawNatGrowth.readList 13 551 ridgeSupport448_rest_019 =
    (ridgeSupport448_suffix_019, ridgeSupport448_rest_037) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 519
    ridgeSupport448_rest_019 ridgeSupport448_rest_020 ridgeSupport448_rest_037
    ridgeSupport448_019 ridgeSupport448_suffix_020 ridgeSupport448_019_decode ridgeSupport448_suffix_decode_020
theorem ridgeSupport448_suffix_decode_018 : PackedRawNatGrowth.readList 13 583 ridgeSupport448_rest_018 =
    (ridgeSupport448_suffix_018, ridgeSupport448_rest_037) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 551
    ridgeSupport448_rest_018 ridgeSupport448_rest_019 ridgeSupport448_rest_037
    ridgeSupport448_018 ridgeSupport448_suffix_019 ridgeSupport448_018_decode ridgeSupport448_suffix_decode_019
theorem ridgeSupport448_suffix_decode_017 : PackedRawNatGrowth.readList 13 615 ridgeSupport448_rest_017 =
    (ridgeSupport448_suffix_017, ridgeSupport448_rest_037) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 583
    ridgeSupport448_rest_017 ridgeSupport448_rest_018 ridgeSupport448_rest_037
    ridgeSupport448_017 ridgeSupport448_suffix_018 ridgeSupport448_017_decode ridgeSupport448_suffix_decode_018
theorem ridgeSupport448_suffix_decode_016 : PackedRawNatGrowth.readList 13 647 ridgeSupport448_rest_016 =
    (ridgeSupport448_suffix_016, ridgeSupport448_rest_037) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 615
    ridgeSupport448_rest_016 ridgeSupport448_rest_017 ridgeSupport448_rest_037
    ridgeSupport448_016 ridgeSupport448_suffix_017 ridgeSupport448_016_decode ridgeSupport448_suffix_decode_017
theorem ridgeSupport448_suffix_decode_015 : PackedRawNatGrowth.readList 13 679 ridgeSupport448_rest_015 =
    (ridgeSupport448_suffix_015, ridgeSupport448_rest_037) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 647
    ridgeSupport448_rest_015 ridgeSupport448_rest_016 ridgeSupport448_rest_037
    ridgeSupport448_015 ridgeSupport448_suffix_016 ridgeSupport448_015_decode ridgeSupport448_suffix_decode_016
theorem ridgeSupport448_suffix_decode_014 : PackedRawNatGrowth.readList 13 711 ridgeSupport448_rest_014 =
    (ridgeSupport448_suffix_014, ridgeSupport448_rest_037) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 679
    ridgeSupport448_rest_014 ridgeSupport448_rest_015 ridgeSupport448_rest_037
    ridgeSupport448_014 ridgeSupport448_suffix_015 ridgeSupport448_014_decode ridgeSupport448_suffix_decode_015
theorem ridgeSupport448_suffix_decode_013 : PackedRawNatGrowth.readList 13 743 ridgeSupport448_rest_013 =
    (ridgeSupport448_suffix_013, ridgeSupport448_rest_037) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 711
    ridgeSupport448_rest_013 ridgeSupport448_rest_014 ridgeSupport448_rest_037
    ridgeSupport448_013 ridgeSupport448_suffix_014 ridgeSupport448_013_decode ridgeSupport448_suffix_decode_014
theorem ridgeSupport448_suffix_decode_012 : PackedRawNatGrowth.readList 13 775 ridgeSupport448_rest_012 =
    (ridgeSupport448_suffix_012, ridgeSupport448_rest_037) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 743
    ridgeSupport448_rest_012 ridgeSupport448_rest_013 ridgeSupport448_rest_037
    ridgeSupport448_012 ridgeSupport448_suffix_013 ridgeSupport448_012_decode ridgeSupport448_suffix_decode_013
theorem ridgeSupport448_suffix_decode_011 : PackedRawNatGrowth.readList 13 807 ridgeSupport448_rest_011 =
    (ridgeSupport448_suffix_011, ridgeSupport448_rest_037) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 775
    ridgeSupport448_rest_011 ridgeSupport448_rest_012 ridgeSupport448_rest_037
    ridgeSupport448_011 ridgeSupport448_suffix_012 ridgeSupport448_011_decode ridgeSupport448_suffix_decode_012
theorem ridgeSupport448_suffix_decode_010 : PackedRawNatGrowth.readList 13 839 ridgeSupport448_rest_010 =
    (ridgeSupport448_suffix_010, ridgeSupport448_rest_037) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 807
    ridgeSupport448_rest_010 ridgeSupport448_rest_011 ridgeSupport448_rest_037
    ridgeSupport448_010 ridgeSupport448_suffix_011 ridgeSupport448_010_decode ridgeSupport448_suffix_decode_011
theorem ridgeSupport448_suffix_decode_009 : PackedRawNatGrowth.readList 13 871 ridgeSupport448_rest_009 =
    (ridgeSupport448_suffix_009, ridgeSupport448_rest_037) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 839
    ridgeSupport448_rest_009 ridgeSupport448_rest_010 ridgeSupport448_rest_037
    ridgeSupport448_009 ridgeSupport448_suffix_010 ridgeSupport448_009_decode ridgeSupport448_suffix_decode_010
theorem ridgeSupport448_suffix_decode_008 : PackedRawNatGrowth.readList 13 903 ridgeSupport448_rest_008 =
    (ridgeSupport448_suffix_008, ridgeSupport448_rest_037) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 871
    ridgeSupport448_rest_008 ridgeSupport448_rest_009 ridgeSupport448_rest_037
    ridgeSupport448_008 ridgeSupport448_suffix_009 ridgeSupport448_008_decode ridgeSupport448_suffix_decode_009
theorem ridgeSupport448_suffix_decode_007 : PackedRawNatGrowth.readList 13 935 ridgeSupport448_rest_007 =
    (ridgeSupport448_suffix_007, ridgeSupport448_rest_037) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 903
    ridgeSupport448_rest_007 ridgeSupport448_rest_008 ridgeSupport448_rest_037
    ridgeSupport448_007 ridgeSupport448_suffix_008 ridgeSupport448_007_decode ridgeSupport448_suffix_decode_008
theorem ridgeSupport448_suffix_decode_006 : PackedRawNatGrowth.readList 13 967 ridgeSupport448_rest_006 =
    (ridgeSupport448_suffix_006, ridgeSupport448_rest_037) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 935
    ridgeSupport448_rest_006 ridgeSupport448_rest_007 ridgeSupport448_rest_037
    ridgeSupport448_006 ridgeSupport448_suffix_007 ridgeSupport448_006_decode ridgeSupport448_suffix_decode_007
theorem ridgeSupport448_suffix_decode_005 : PackedRawNatGrowth.readList 13 999 ridgeSupport448_rest_005 =
    (ridgeSupport448_suffix_005, ridgeSupport448_rest_037) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 967
    ridgeSupport448_rest_005 ridgeSupport448_rest_006 ridgeSupport448_rest_037
    ridgeSupport448_005 ridgeSupport448_suffix_006 ridgeSupport448_005_decode ridgeSupport448_suffix_decode_006
theorem ridgeSupport448_suffix_decode_004 : PackedRawNatGrowth.readList 13 1031 ridgeSupport448_rest_004 =
    (ridgeSupport448_suffix_004, ridgeSupport448_rest_037) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 999
    ridgeSupport448_rest_004 ridgeSupport448_rest_005 ridgeSupport448_rest_037
    ridgeSupport448_004 ridgeSupport448_suffix_005 ridgeSupport448_004_decode ridgeSupport448_suffix_decode_005
theorem ridgeSupport448_suffix_decode_003 : PackedRawNatGrowth.readList 13 1063 ridgeSupport448_rest_003 =
    (ridgeSupport448_suffix_003, ridgeSupport448_rest_037) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 1031
    ridgeSupport448_rest_003 ridgeSupport448_rest_004 ridgeSupport448_rest_037
    ridgeSupport448_003 ridgeSupport448_suffix_004 ridgeSupport448_003_decode ridgeSupport448_suffix_decode_004
theorem ridgeSupport448_suffix_decode_002 : PackedRawNatGrowth.readList 13 1095 ridgeSupport448_rest_002 =
    (ridgeSupport448_suffix_002, ridgeSupport448_rest_037) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 1063
    ridgeSupport448_rest_002 ridgeSupport448_rest_003 ridgeSupport448_rest_037
    ridgeSupport448_002 ridgeSupport448_suffix_003 ridgeSupport448_002_decode ridgeSupport448_suffix_decode_003
theorem ridgeSupport448_suffix_decode_001 : PackedRawNatGrowth.readList 13 1127 ridgeSupport448_rest_001 =
    (ridgeSupport448_suffix_001, ridgeSupport448_rest_037) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 1095
    ridgeSupport448_rest_001 ridgeSupport448_rest_002 ridgeSupport448_rest_037
    ridgeSupport448_001 ridgeSupport448_suffix_002 ridgeSupport448_001_decode ridgeSupport448_suffix_decode_002
theorem ridgeSupport448_suffix_decode_000 : PackedRawNatGrowth.readList 13 1159 ridgeSupport448_rest_000 =
    (ridgeSupport448_suffix_000, ridgeSupport448_rest_037) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 1127
    ridgeSupport448_rest_000 ridgeSupport448_rest_001 ridgeSupport448_rest_037
    ridgeSupport448_000 ridgeSupport448_suffix_001 ridgeSupport448_000_decode ridgeSupport448_suffix_decode_001
theorem ridgeSupport448_eq : candidateSupports 448 = ridgeSupport448_suffix_000 := by
  rw [ridgeSupport448_source]
  exact congrArg Prod.fst ridgeSupport448_suffix_decode_000
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
