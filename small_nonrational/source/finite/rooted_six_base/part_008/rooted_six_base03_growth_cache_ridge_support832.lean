module
prelude
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
theorem ridgeSupport832_suffix_decode_037 : PackedRawNatGrowth.readList 13 0 ridgeSupport832_rest_037 =
    (ridgeSupport832_suffix_037, ridgeSupport832_rest_037) := by rfl
theorem ridgeSupport832_suffix_decode_036 : PackedRawNatGrowth.readList 13 7 ridgeSupport832_rest_036 =
    (ridgeSupport832_suffix_036, ridgeSupport832_rest_037) :=
  PackedRawNatGrowth.readList_append_of_eq 13 7 0
    ridgeSupport832_rest_036 ridgeSupport832_rest_037 ridgeSupport832_rest_037
    ridgeSupport832_036 ridgeSupport832_suffix_037 ridgeSupport832_036_decode ridgeSupport832_suffix_decode_037
theorem ridgeSupport832_suffix_decode_035 : PackedRawNatGrowth.readList 13 39 ridgeSupport832_rest_035 =
    (ridgeSupport832_suffix_035, ridgeSupport832_rest_037) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 7
    ridgeSupport832_rest_035 ridgeSupport832_rest_036 ridgeSupport832_rest_037
    ridgeSupport832_035 ridgeSupport832_suffix_036 ridgeSupport832_035_decode ridgeSupport832_suffix_decode_036
theorem ridgeSupport832_suffix_decode_034 : PackedRawNatGrowth.readList 13 71 ridgeSupport832_rest_034 =
    (ridgeSupport832_suffix_034, ridgeSupport832_rest_037) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 39
    ridgeSupport832_rest_034 ridgeSupport832_rest_035 ridgeSupport832_rest_037
    ridgeSupport832_034 ridgeSupport832_suffix_035 ridgeSupport832_034_decode ridgeSupport832_suffix_decode_035
theorem ridgeSupport832_suffix_decode_033 : PackedRawNatGrowth.readList 13 103 ridgeSupport832_rest_033 =
    (ridgeSupport832_suffix_033, ridgeSupport832_rest_037) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 71
    ridgeSupport832_rest_033 ridgeSupport832_rest_034 ridgeSupport832_rest_037
    ridgeSupport832_033 ridgeSupport832_suffix_034 ridgeSupport832_033_decode ridgeSupport832_suffix_decode_034
theorem ridgeSupport832_suffix_decode_032 : PackedRawNatGrowth.readList 13 135 ridgeSupport832_rest_032 =
    (ridgeSupport832_suffix_032, ridgeSupport832_rest_037) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 103
    ridgeSupport832_rest_032 ridgeSupport832_rest_033 ridgeSupport832_rest_037
    ridgeSupport832_032 ridgeSupport832_suffix_033 ridgeSupport832_032_decode ridgeSupport832_suffix_decode_033
theorem ridgeSupport832_suffix_decode_031 : PackedRawNatGrowth.readList 13 167 ridgeSupport832_rest_031 =
    (ridgeSupport832_suffix_031, ridgeSupport832_rest_037) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 135
    ridgeSupport832_rest_031 ridgeSupport832_rest_032 ridgeSupport832_rest_037
    ridgeSupport832_031 ridgeSupport832_suffix_032 ridgeSupport832_031_decode ridgeSupport832_suffix_decode_032
theorem ridgeSupport832_suffix_decode_030 : PackedRawNatGrowth.readList 13 199 ridgeSupport832_rest_030 =
    (ridgeSupport832_suffix_030, ridgeSupport832_rest_037) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 167
    ridgeSupport832_rest_030 ridgeSupport832_rest_031 ridgeSupport832_rest_037
    ridgeSupport832_030 ridgeSupport832_suffix_031 ridgeSupport832_030_decode ridgeSupport832_suffix_decode_031
theorem ridgeSupport832_suffix_decode_029 : PackedRawNatGrowth.readList 13 231 ridgeSupport832_rest_029 =
    (ridgeSupport832_suffix_029, ridgeSupport832_rest_037) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 199
    ridgeSupport832_rest_029 ridgeSupport832_rest_030 ridgeSupport832_rest_037
    ridgeSupport832_029 ridgeSupport832_suffix_030 ridgeSupport832_029_decode ridgeSupport832_suffix_decode_030
theorem ridgeSupport832_suffix_decode_028 : PackedRawNatGrowth.readList 13 263 ridgeSupport832_rest_028 =
    (ridgeSupport832_suffix_028, ridgeSupport832_rest_037) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 231
    ridgeSupport832_rest_028 ridgeSupport832_rest_029 ridgeSupport832_rest_037
    ridgeSupport832_028 ridgeSupport832_suffix_029 ridgeSupport832_028_decode ridgeSupport832_suffix_decode_029
theorem ridgeSupport832_suffix_decode_027 : PackedRawNatGrowth.readList 13 295 ridgeSupport832_rest_027 =
    (ridgeSupport832_suffix_027, ridgeSupport832_rest_037) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 263
    ridgeSupport832_rest_027 ridgeSupport832_rest_028 ridgeSupport832_rest_037
    ridgeSupport832_027 ridgeSupport832_suffix_028 ridgeSupport832_027_decode ridgeSupport832_suffix_decode_028
theorem ridgeSupport832_suffix_decode_026 : PackedRawNatGrowth.readList 13 327 ridgeSupport832_rest_026 =
    (ridgeSupport832_suffix_026, ridgeSupport832_rest_037) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 295
    ridgeSupport832_rest_026 ridgeSupport832_rest_027 ridgeSupport832_rest_037
    ridgeSupport832_026 ridgeSupport832_suffix_027 ridgeSupport832_026_decode ridgeSupport832_suffix_decode_027
theorem ridgeSupport832_suffix_decode_025 : PackedRawNatGrowth.readList 13 359 ridgeSupport832_rest_025 =
    (ridgeSupport832_suffix_025, ridgeSupport832_rest_037) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 327
    ridgeSupport832_rest_025 ridgeSupport832_rest_026 ridgeSupport832_rest_037
    ridgeSupport832_025 ridgeSupport832_suffix_026 ridgeSupport832_025_decode ridgeSupport832_suffix_decode_026
theorem ridgeSupport832_suffix_decode_024 : PackedRawNatGrowth.readList 13 391 ridgeSupport832_rest_024 =
    (ridgeSupport832_suffix_024, ridgeSupport832_rest_037) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 359
    ridgeSupport832_rest_024 ridgeSupport832_rest_025 ridgeSupport832_rest_037
    ridgeSupport832_024 ridgeSupport832_suffix_025 ridgeSupport832_024_decode ridgeSupport832_suffix_decode_025
theorem ridgeSupport832_suffix_decode_023 : PackedRawNatGrowth.readList 13 423 ridgeSupport832_rest_023 =
    (ridgeSupport832_suffix_023, ridgeSupport832_rest_037) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 391
    ridgeSupport832_rest_023 ridgeSupport832_rest_024 ridgeSupport832_rest_037
    ridgeSupport832_023 ridgeSupport832_suffix_024 ridgeSupport832_023_decode ridgeSupport832_suffix_decode_024
theorem ridgeSupport832_suffix_decode_022 : PackedRawNatGrowth.readList 13 455 ridgeSupport832_rest_022 =
    (ridgeSupport832_suffix_022, ridgeSupport832_rest_037) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 423
    ridgeSupport832_rest_022 ridgeSupport832_rest_023 ridgeSupport832_rest_037
    ridgeSupport832_022 ridgeSupport832_suffix_023 ridgeSupport832_022_decode ridgeSupport832_suffix_decode_023
theorem ridgeSupport832_suffix_decode_021 : PackedRawNatGrowth.readList 13 487 ridgeSupport832_rest_021 =
    (ridgeSupport832_suffix_021, ridgeSupport832_rest_037) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 455
    ridgeSupport832_rest_021 ridgeSupport832_rest_022 ridgeSupport832_rest_037
    ridgeSupport832_021 ridgeSupport832_suffix_022 ridgeSupport832_021_decode ridgeSupport832_suffix_decode_022
theorem ridgeSupport832_suffix_decode_020 : PackedRawNatGrowth.readList 13 519 ridgeSupport832_rest_020 =
    (ridgeSupport832_suffix_020, ridgeSupport832_rest_037) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 487
    ridgeSupport832_rest_020 ridgeSupport832_rest_021 ridgeSupport832_rest_037
    ridgeSupport832_020 ridgeSupport832_suffix_021 ridgeSupport832_020_decode ridgeSupport832_suffix_decode_021
theorem ridgeSupport832_suffix_decode_019 : PackedRawNatGrowth.readList 13 551 ridgeSupport832_rest_019 =
    (ridgeSupport832_suffix_019, ridgeSupport832_rest_037) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 519
    ridgeSupport832_rest_019 ridgeSupport832_rest_020 ridgeSupport832_rest_037
    ridgeSupport832_019 ridgeSupport832_suffix_020 ridgeSupport832_019_decode ridgeSupport832_suffix_decode_020
theorem ridgeSupport832_suffix_decode_018 : PackedRawNatGrowth.readList 13 583 ridgeSupport832_rest_018 =
    (ridgeSupport832_suffix_018, ridgeSupport832_rest_037) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 551
    ridgeSupport832_rest_018 ridgeSupport832_rest_019 ridgeSupport832_rest_037
    ridgeSupport832_018 ridgeSupport832_suffix_019 ridgeSupport832_018_decode ridgeSupport832_suffix_decode_019
theorem ridgeSupport832_suffix_decode_017 : PackedRawNatGrowth.readList 13 615 ridgeSupport832_rest_017 =
    (ridgeSupport832_suffix_017, ridgeSupport832_rest_037) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 583
    ridgeSupport832_rest_017 ridgeSupport832_rest_018 ridgeSupport832_rest_037
    ridgeSupport832_017 ridgeSupport832_suffix_018 ridgeSupport832_017_decode ridgeSupport832_suffix_decode_018
theorem ridgeSupport832_suffix_decode_016 : PackedRawNatGrowth.readList 13 647 ridgeSupport832_rest_016 =
    (ridgeSupport832_suffix_016, ridgeSupport832_rest_037) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 615
    ridgeSupport832_rest_016 ridgeSupport832_rest_017 ridgeSupport832_rest_037
    ridgeSupport832_016 ridgeSupport832_suffix_017 ridgeSupport832_016_decode ridgeSupport832_suffix_decode_017
theorem ridgeSupport832_suffix_decode_015 : PackedRawNatGrowth.readList 13 679 ridgeSupport832_rest_015 =
    (ridgeSupport832_suffix_015, ridgeSupport832_rest_037) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 647
    ridgeSupport832_rest_015 ridgeSupport832_rest_016 ridgeSupport832_rest_037
    ridgeSupport832_015 ridgeSupport832_suffix_016 ridgeSupport832_015_decode ridgeSupport832_suffix_decode_016
theorem ridgeSupport832_suffix_decode_014 : PackedRawNatGrowth.readList 13 711 ridgeSupport832_rest_014 =
    (ridgeSupport832_suffix_014, ridgeSupport832_rest_037) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 679
    ridgeSupport832_rest_014 ridgeSupport832_rest_015 ridgeSupport832_rest_037
    ridgeSupport832_014 ridgeSupport832_suffix_015 ridgeSupport832_014_decode ridgeSupport832_suffix_decode_015
theorem ridgeSupport832_suffix_decode_013 : PackedRawNatGrowth.readList 13 743 ridgeSupport832_rest_013 =
    (ridgeSupport832_suffix_013, ridgeSupport832_rest_037) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 711
    ridgeSupport832_rest_013 ridgeSupport832_rest_014 ridgeSupport832_rest_037
    ridgeSupport832_013 ridgeSupport832_suffix_014 ridgeSupport832_013_decode ridgeSupport832_suffix_decode_014
theorem ridgeSupport832_suffix_decode_012 : PackedRawNatGrowth.readList 13 775 ridgeSupport832_rest_012 =
    (ridgeSupport832_suffix_012, ridgeSupport832_rest_037) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 743
    ridgeSupport832_rest_012 ridgeSupport832_rest_013 ridgeSupport832_rest_037
    ridgeSupport832_012 ridgeSupport832_suffix_013 ridgeSupport832_012_decode ridgeSupport832_suffix_decode_013
theorem ridgeSupport832_suffix_decode_011 : PackedRawNatGrowth.readList 13 807 ridgeSupport832_rest_011 =
    (ridgeSupport832_suffix_011, ridgeSupport832_rest_037) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 775
    ridgeSupport832_rest_011 ridgeSupport832_rest_012 ridgeSupport832_rest_037
    ridgeSupport832_011 ridgeSupport832_suffix_012 ridgeSupport832_011_decode ridgeSupport832_suffix_decode_012
theorem ridgeSupport832_suffix_decode_010 : PackedRawNatGrowth.readList 13 839 ridgeSupport832_rest_010 =
    (ridgeSupport832_suffix_010, ridgeSupport832_rest_037) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 807
    ridgeSupport832_rest_010 ridgeSupport832_rest_011 ridgeSupport832_rest_037
    ridgeSupport832_010 ridgeSupport832_suffix_011 ridgeSupport832_010_decode ridgeSupport832_suffix_decode_011
theorem ridgeSupport832_suffix_decode_009 : PackedRawNatGrowth.readList 13 871 ridgeSupport832_rest_009 =
    (ridgeSupport832_suffix_009, ridgeSupport832_rest_037) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 839
    ridgeSupport832_rest_009 ridgeSupport832_rest_010 ridgeSupport832_rest_037
    ridgeSupport832_009 ridgeSupport832_suffix_010 ridgeSupport832_009_decode ridgeSupport832_suffix_decode_010
theorem ridgeSupport832_suffix_decode_008 : PackedRawNatGrowth.readList 13 903 ridgeSupport832_rest_008 =
    (ridgeSupport832_suffix_008, ridgeSupport832_rest_037) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 871
    ridgeSupport832_rest_008 ridgeSupport832_rest_009 ridgeSupport832_rest_037
    ridgeSupport832_008 ridgeSupport832_suffix_009 ridgeSupport832_008_decode ridgeSupport832_suffix_decode_009
theorem ridgeSupport832_suffix_decode_007 : PackedRawNatGrowth.readList 13 935 ridgeSupport832_rest_007 =
    (ridgeSupport832_suffix_007, ridgeSupport832_rest_037) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 903
    ridgeSupport832_rest_007 ridgeSupport832_rest_008 ridgeSupport832_rest_037
    ridgeSupport832_007 ridgeSupport832_suffix_008 ridgeSupport832_007_decode ridgeSupport832_suffix_decode_008
theorem ridgeSupport832_suffix_decode_006 : PackedRawNatGrowth.readList 13 967 ridgeSupport832_rest_006 =
    (ridgeSupport832_suffix_006, ridgeSupport832_rest_037) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 935
    ridgeSupport832_rest_006 ridgeSupport832_rest_007 ridgeSupport832_rest_037
    ridgeSupport832_006 ridgeSupport832_suffix_007 ridgeSupport832_006_decode ridgeSupport832_suffix_decode_007
theorem ridgeSupport832_suffix_decode_005 : PackedRawNatGrowth.readList 13 999 ridgeSupport832_rest_005 =
    (ridgeSupport832_suffix_005, ridgeSupport832_rest_037) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 967
    ridgeSupport832_rest_005 ridgeSupport832_rest_006 ridgeSupport832_rest_037
    ridgeSupport832_005 ridgeSupport832_suffix_006 ridgeSupport832_005_decode ridgeSupport832_suffix_decode_006
theorem ridgeSupport832_suffix_decode_004 : PackedRawNatGrowth.readList 13 1031 ridgeSupport832_rest_004 =
    (ridgeSupport832_suffix_004, ridgeSupport832_rest_037) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 999
    ridgeSupport832_rest_004 ridgeSupport832_rest_005 ridgeSupport832_rest_037
    ridgeSupport832_004 ridgeSupport832_suffix_005 ridgeSupport832_004_decode ridgeSupport832_suffix_decode_005
theorem ridgeSupport832_suffix_decode_003 : PackedRawNatGrowth.readList 13 1063 ridgeSupport832_rest_003 =
    (ridgeSupport832_suffix_003, ridgeSupport832_rest_037) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 1031
    ridgeSupport832_rest_003 ridgeSupport832_rest_004 ridgeSupport832_rest_037
    ridgeSupport832_003 ridgeSupport832_suffix_004 ridgeSupport832_003_decode ridgeSupport832_suffix_decode_004
theorem ridgeSupport832_suffix_decode_002 : PackedRawNatGrowth.readList 13 1095 ridgeSupport832_rest_002 =
    (ridgeSupport832_suffix_002, ridgeSupport832_rest_037) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 1063
    ridgeSupport832_rest_002 ridgeSupport832_rest_003 ridgeSupport832_rest_037
    ridgeSupport832_002 ridgeSupport832_suffix_003 ridgeSupport832_002_decode ridgeSupport832_suffix_decode_003
theorem ridgeSupport832_suffix_decode_001 : PackedRawNatGrowth.readList 13 1127 ridgeSupport832_rest_001 =
    (ridgeSupport832_suffix_001, ridgeSupport832_rest_037) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 1095
    ridgeSupport832_rest_001 ridgeSupport832_rest_002 ridgeSupport832_rest_037
    ridgeSupport832_001 ridgeSupport832_suffix_002 ridgeSupport832_001_decode ridgeSupport832_suffix_decode_002
theorem ridgeSupport832_suffix_decode_000 : PackedRawNatGrowth.readList 13 1159 ridgeSupport832_rest_000 =
    (ridgeSupport832_suffix_000, ridgeSupport832_rest_037) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 1127
    ridgeSupport832_rest_000 ridgeSupport832_rest_001 ridgeSupport832_rest_037
    ridgeSupport832_000 ridgeSupport832_suffix_001 ridgeSupport832_000_decode ridgeSupport832_suffix_decode_001
theorem ridgeSupport832_eq : candidateSupports 832 = ridgeSupport832_suffix_000 := by
  rw [ridgeSupport832_source]
  exact congrArg Prod.fst ridgeSupport832_suffix_decode_000
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
