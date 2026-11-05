module
prelude
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
theorem ridgeSupport896_suffix_decode_037 : PackedRawNatGrowth.readList 13 0 ridgeSupport896_rest_037 =
    (ridgeSupport896_suffix_037, ridgeSupport896_rest_037) := by rfl
theorem ridgeSupport896_suffix_decode_036 : PackedRawNatGrowth.readList 13 7 ridgeSupport896_rest_036 =
    (ridgeSupport896_suffix_036, ridgeSupport896_rest_037) :=
  PackedRawNatGrowth.readList_append_of_eq 13 7 0
    ridgeSupport896_rest_036 ridgeSupport896_rest_037 ridgeSupport896_rest_037
    ridgeSupport896_036 ridgeSupport896_suffix_037 ridgeSupport896_036_decode ridgeSupport896_suffix_decode_037
theorem ridgeSupport896_suffix_decode_035 : PackedRawNatGrowth.readList 13 39 ridgeSupport896_rest_035 =
    (ridgeSupport896_suffix_035, ridgeSupport896_rest_037) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 7
    ridgeSupport896_rest_035 ridgeSupport896_rest_036 ridgeSupport896_rest_037
    ridgeSupport896_035 ridgeSupport896_suffix_036 ridgeSupport896_035_decode ridgeSupport896_suffix_decode_036
theorem ridgeSupport896_suffix_decode_034 : PackedRawNatGrowth.readList 13 71 ridgeSupport896_rest_034 =
    (ridgeSupport896_suffix_034, ridgeSupport896_rest_037) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 39
    ridgeSupport896_rest_034 ridgeSupport896_rest_035 ridgeSupport896_rest_037
    ridgeSupport896_034 ridgeSupport896_suffix_035 ridgeSupport896_034_decode ridgeSupport896_suffix_decode_035
theorem ridgeSupport896_suffix_decode_033 : PackedRawNatGrowth.readList 13 103 ridgeSupport896_rest_033 =
    (ridgeSupport896_suffix_033, ridgeSupport896_rest_037) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 71
    ridgeSupport896_rest_033 ridgeSupport896_rest_034 ridgeSupport896_rest_037
    ridgeSupport896_033 ridgeSupport896_suffix_034 ridgeSupport896_033_decode ridgeSupport896_suffix_decode_034
theorem ridgeSupport896_suffix_decode_032 : PackedRawNatGrowth.readList 13 135 ridgeSupport896_rest_032 =
    (ridgeSupport896_suffix_032, ridgeSupport896_rest_037) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 103
    ridgeSupport896_rest_032 ridgeSupport896_rest_033 ridgeSupport896_rest_037
    ridgeSupport896_032 ridgeSupport896_suffix_033 ridgeSupport896_032_decode ridgeSupport896_suffix_decode_033
theorem ridgeSupport896_suffix_decode_031 : PackedRawNatGrowth.readList 13 167 ridgeSupport896_rest_031 =
    (ridgeSupport896_suffix_031, ridgeSupport896_rest_037) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 135
    ridgeSupport896_rest_031 ridgeSupport896_rest_032 ridgeSupport896_rest_037
    ridgeSupport896_031 ridgeSupport896_suffix_032 ridgeSupport896_031_decode ridgeSupport896_suffix_decode_032
theorem ridgeSupport896_suffix_decode_030 : PackedRawNatGrowth.readList 13 199 ridgeSupport896_rest_030 =
    (ridgeSupport896_suffix_030, ridgeSupport896_rest_037) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 167
    ridgeSupport896_rest_030 ridgeSupport896_rest_031 ridgeSupport896_rest_037
    ridgeSupport896_030 ridgeSupport896_suffix_031 ridgeSupport896_030_decode ridgeSupport896_suffix_decode_031
theorem ridgeSupport896_suffix_decode_029 : PackedRawNatGrowth.readList 13 231 ridgeSupport896_rest_029 =
    (ridgeSupport896_suffix_029, ridgeSupport896_rest_037) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 199
    ridgeSupport896_rest_029 ridgeSupport896_rest_030 ridgeSupport896_rest_037
    ridgeSupport896_029 ridgeSupport896_suffix_030 ridgeSupport896_029_decode ridgeSupport896_suffix_decode_030
theorem ridgeSupport896_suffix_decode_028 : PackedRawNatGrowth.readList 13 263 ridgeSupport896_rest_028 =
    (ridgeSupport896_suffix_028, ridgeSupport896_rest_037) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 231
    ridgeSupport896_rest_028 ridgeSupport896_rest_029 ridgeSupport896_rest_037
    ridgeSupport896_028 ridgeSupport896_suffix_029 ridgeSupport896_028_decode ridgeSupport896_suffix_decode_029
theorem ridgeSupport896_suffix_decode_027 : PackedRawNatGrowth.readList 13 295 ridgeSupport896_rest_027 =
    (ridgeSupport896_suffix_027, ridgeSupport896_rest_037) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 263
    ridgeSupport896_rest_027 ridgeSupport896_rest_028 ridgeSupport896_rest_037
    ridgeSupport896_027 ridgeSupport896_suffix_028 ridgeSupport896_027_decode ridgeSupport896_suffix_decode_028
theorem ridgeSupport896_suffix_decode_026 : PackedRawNatGrowth.readList 13 327 ridgeSupport896_rest_026 =
    (ridgeSupport896_suffix_026, ridgeSupport896_rest_037) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 295
    ridgeSupport896_rest_026 ridgeSupport896_rest_027 ridgeSupport896_rest_037
    ridgeSupport896_026 ridgeSupport896_suffix_027 ridgeSupport896_026_decode ridgeSupport896_suffix_decode_027
theorem ridgeSupport896_suffix_decode_025 : PackedRawNatGrowth.readList 13 359 ridgeSupport896_rest_025 =
    (ridgeSupport896_suffix_025, ridgeSupport896_rest_037) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 327
    ridgeSupport896_rest_025 ridgeSupport896_rest_026 ridgeSupport896_rest_037
    ridgeSupport896_025 ridgeSupport896_suffix_026 ridgeSupport896_025_decode ridgeSupport896_suffix_decode_026
theorem ridgeSupport896_suffix_decode_024 : PackedRawNatGrowth.readList 13 391 ridgeSupport896_rest_024 =
    (ridgeSupport896_suffix_024, ridgeSupport896_rest_037) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 359
    ridgeSupport896_rest_024 ridgeSupport896_rest_025 ridgeSupport896_rest_037
    ridgeSupport896_024 ridgeSupport896_suffix_025 ridgeSupport896_024_decode ridgeSupport896_suffix_decode_025
theorem ridgeSupport896_suffix_decode_023 : PackedRawNatGrowth.readList 13 423 ridgeSupport896_rest_023 =
    (ridgeSupport896_suffix_023, ridgeSupport896_rest_037) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 391
    ridgeSupport896_rest_023 ridgeSupport896_rest_024 ridgeSupport896_rest_037
    ridgeSupport896_023 ridgeSupport896_suffix_024 ridgeSupport896_023_decode ridgeSupport896_suffix_decode_024
theorem ridgeSupport896_suffix_decode_022 : PackedRawNatGrowth.readList 13 455 ridgeSupport896_rest_022 =
    (ridgeSupport896_suffix_022, ridgeSupport896_rest_037) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 423
    ridgeSupport896_rest_022 ridgeSupport896_rest_023 ridgeSupport896_rest_037
    ridgeSupport896_022 ridgeSupport896_suffix_023 ridgeSupport896_022_decode ridgeSupport896_suffix_decode_023
theorem ridgeSupport896_suffix_decode_021 : PackedRawNatGrowth.readList 13 487 ridgeSupport896_rest_021 =
    (ridgeSupport896_suffix_021, ridgeSupport896_rest_037) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 455
    ridgeSupport896_rest_021 ridgeSupport896_rest_022 ridgeSupport896_rest_037
    ridgeSupport896_021 ridgeSupport896_suffix_022 ridgeSupport896_021_decode ridgeSupport896_suffix_decode_022
theorem ridgeSupport896_suffix_decode_020 : PackedRawNatGrowth.readList 13 519 ridgeSupport896_rest_020 =
    (ridgeSupport896_suffix_020, ridgeSupport896_rest_037) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 487
    ridgeSupport896_rest_020 ridgeSupport896_rest_021 ridgeSupport896_rest_037
    ridgeSupport896_020 ridgeSupport896_suffix_021 ridgeSupport896_020_decode ridgeSupport896_suffix_decode_021
theorem ridgeSupport896_suffix_decode_019 : PackedRawNatGrowth.readList 13 551 ridgeSupport896_rest_019 =
    (ridgeSupport896_suffix_019, ridgeSupport896_rest_037) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 519
    ridgeSupport896_rest_019 ridgeSupport896_rest_020 ridgeSupport896_rest_037
    ridgeSupport896_019 ridgeSupport896_suffix_020 ridgeSupport896_019_decode ridgeSupport896_suffix_decode_020
theorem ridgeSupport896_suffix_decode_018 : PackedRawNatGrowth.readList 13 583 ridgeSupport896_rest_018 =
    (ridgeSupport896_suffix_018, ridgeSupport896_rest_037) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 551
    ridgeSupport896_rest_018 ridgeSupport896_rest_019 ridgeSupport896_rest_037
    ridgeSupport896_018 ridgeSupport896_suffix_019 ridgeSupport896_018_decode ridgeSupport896_suffix_decode_019
theorem ridgeSupport896_suffix_decode_017 : PackedRawNatGrowth.readList 13 615 ridgeSupport896_rest_017 =
    (ridgeSupport896_suffix_017, ridgeSupport896_rest_037) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 583
    ridgeSupport896_rest_017 ridgeSupport896_rest_018 ridgeSupport896_rest_037
    ridgeSupport896_017 ridgeSupport896_suffix_018 ridgeSupport896_017_decode ridgeSupport896_suffix_decode_018
theorem ridgeSupport896_suffix_decode_016 : PackedRawNatGrowth.readList 13 647 ridgeSupport896_rest_016 =
    (ridgeSupport896_suffix_016, ridgeSupport896_rest_037) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 615
    ridgeSupport896_rest_016 ridgeSupport896_rest_017 ridgeSupport896_rest_037
    ridgeSupport896_016 ridgeSupport896_suffix_017 ridgeSupport896_016_decode ridgeSupport896_suffix_decode_017
theorem ridgeSupport896_suffix_decode_015 : PackedRawNatGrowth.readList 13 679 ridgeSupport896_rest_015 =
    (ridgeSupport896_suffix_015, ridgeSupport896_rest_037) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 647
    ridgeSupport896_rest_015 ridgeSupport896_rest_016 ridgeSupport896_rest_037
    ridgeSupport896_015 ridgeSupport896_suffix_016 ridgeSupport896_015_decode ridgeSupport896_suffix_decode_016
theorem ridgeSupport896_suffix_decode_014 : PackedRawNatGrowth.readList 13 711 ridgeSupport896_rest_014 =
    (ridgeSupport896_suffix_014, ridgeSupport896_rest_037) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 679
    ridgeSupport896_rest_014 ridgeSupport896_rest_015 ridgeSupport896_rest_037
    ridgeSupport896_014 ridgeSupport896_suffix_015 ridgeSupport896_014_decode ridgeSupport896_suffix_decode_015
theorem ridgeSupport896_suffix_decode_013 : PackedRawNatGrowth.readList 13 743 ridgeSupport896_rest_013 =
    (ridgeSupport896_suffix_013, ridgeSupport896_rest_037) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 711
    ridgeSupport896_rest_013 ridgeSupport896_rest_014 ridgeSupport896_rest_037
    ridgeSupport896_013 ridgeSupport896_suffix_014 ridgeSupport896_013_decode ridgeSupport896_suffix_decode_014
theorem ridgeSupport896_suffix_decode_012 : PackedRawNatGrowth.readList 13 775 ridgeSupport896_rest_012 =
    (ridgeSupport896_suffix_012, ridgeSupport896_rest_037) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 743
    ridgeSupport896_rest_012 ridgeSupport896_rest_013 ridgeSupport896_rest_037
    ridgeSupport896_012 ridgeSupport896_suffix_013 ridgeSupport896_012_decode ridgeSupport896_suffix_decode_013
theorem ridgeSupport896_suffix_decode_011 : PackedRawNatGrowth.readList 13 807 ridgeSupport896_rest_011 =
    (ridgeSupport896_suffix_011, ridgeSupport896_rest_037) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 775
    ridgeSupport896_rest_011 ridgeSupport896_rest_012 ridgeSupport896_rest_037
    ridgeSupport896_011 ridgeSupport896_suffix_012 ridgeSupport896_011_decode ridgeSupport896_suffix_decode_012
theorem ridgeSupport896_suffix_decode_010 : PackedRawNatGrowth.readList 13 839 ridgeSupport896_rest_010 =
    (ridgeSupport896_suffix_010, ridgeSupport896_rest_037) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 807
    ridgeSupport896_rest_010 ridgeSupport896_rest_011 ridgeSupport896_rest_037
    ridgeSupport896_010 ridgeSupport896_suffix_011 ridgeSupport896_010_decode ridgeSupport896_suffix_decode_011
theorem ridgeSupport896_suffix_decode_009 : PackedRawNatGrowth.readList 13 871 ridgeSupport896_rest_009 =
    (ridgeSupport896_suffix_009, ridgeSupport896_rest_037) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 839
    ridgeSupport896_rest_009 ridgeSupport896_rest_010 ridgeSupport896_rest_037
    ridgeSupport896_009 ridgeSupport896_suffix_010 ridgeSupport896_009_decode ridgeSupport896_suffix_decode_010
theorem ridgeSupport896_suffix_decode_008 : PackedRawNatGrowth.readList 13 903 ridgeSupport896_rest_008 =
    (ridgeSupport896_suffix_008, ridgeSupport896_rest_037) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 871
    ridgeSupport896_rest_008 ridgeSupport896_rest_009 ridgeSupport896_rest_037
    ridgeSupport896_008 ridgeSupport896_suffix_009 ridgeSupport896_008_decode ridgeSupport896_suffix_decode_009
theorem ridgeSupport896_suffix_decode_007 : PackedRawNatGrowth.readList 13 935 ridgeSupport896_rest_007 =
    (ridgeSupport896_suffix_007, ridgeSupport896_rest_037) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 903
    ridgeSupport896_rest_007 ridgeSupport896_rest_008 ridgeSupport896_rest_037
    ridgeSupport896_007 ridgeSupport896_suffix_008 ridgeSupport896_007_decode ridgeSupport896_suffix_decode_008
theorem ridgeSupport896_suffix_decode_006 : PackedRawNatGrowth.readList 13 967 ridgeSupport896_rest_006 =
    (ridgeSupport896_suffix_006, ridgeSupport896_rest_037) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 935
    ridgeSupport896_rest_006 ridgeSupport896_rest_007 ridgeSupport896_rest_037
    ridgeSupport896_006 ridgeSupport896_suffix_007 ridgeSupport896_006_decode ridgeSupport896_suffix_decode_007
theorem ridgeSupport896_suffix_decode_005 : PackedRawNatGrowth.readList 13 999 ridgeSupport896_rest_005 =
    (ridgeSupport896_suffix_005, ridgeSupport896_rest_037) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 967
    ridgeSupport896_rest_005 ridgeSupport896_rest_006 ridgeSupport896_rest_037
    ridgeSupport896_005 ridgeSupport896_suffix_006 ridgeSupport896_005_decode ridgeSupport896_suffix_decode_006
theorem ridgeSupport896_suffix_decode_004 : PackedRawNatGrowth.readList 13 1031 ridgeSupport896_rest_004 =
    (ridgeSupport896_suffix_004, ridgeSupport896_rest_037) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 999
    ridgeSupport896_rest_004 ridgeSupport896_rest_005 ridgeSupport896_rest_037
    ridgeSupport896_004 ridgeSupport896_suffix_005 ridgeSupport896_004_decode ridgeSupport896_suffix_decode_005
theorem ridgeSupport896_suffix_decode_003 : PackedRawNatGrowth.readList 13 1063 ridgeSupport896_rest_003 =
    (ridgeSupport896_suffix_003, ridgeSupport896_rest_037) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 1031
    ridgeSupport896_rest_003 ridgeSupport896_rest_004 ridgeSupport896_rest_037
    ridgeSupport896_003 ridgeSupport896_suffix_004 ridgeSupport896_003_decode ridgeSupport896_suffix_decode_004
theorem ridgeSupport896_suffix_decode_002 : PackedRawNatGrowth.readList 13 1095 ridgeSupport896_rest_002 =
    (ridgeSupport896_suffix_002, ridgeSupport896_rest_037) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 1063
    ridgeSupport896_rest_002 ridgeSupport896_rest_003 ridgeSupport896_rest_037
    ridgeSupport896_002 ridgeSupport896_suffix_003 ridgeSupport896_002_decode ridgeSupport896_suffix_decode_003
theorem ridgeSupport896_suffix_decode_001 : PackedRawNatGrowth.readList 13 1127 ridgeSupport896_rest_001 =
    (ridgeSupport896_suffix_001, ridgeSupport896_rest_037) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 1095
    ridgeSupport896_rest_001 ridgeSupport896_rest_002 ridgeSupport896_rest_037
    ridgeSupport896_001 ridgeSupport896_suffix_002 ridgeSupport896_001_decode ridgeSupport896_suffix_decode_002
theorem ridgeSupport896_suffix_decode_000 : PackedRawNatGrowth.readList 13 1159 ridgeSupport896_rest_000 =
    (ridgeSupport896_suffix_000, ridgeSupport896_rest_037) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 1127
    ridgeSupport896_rest_000 ridgeSupport896_rest_001 ridgeSupport896_rest_037
    ridgeSupport896_000 ridgeSupport896_suffix_001 ridgeSupport896_000_decode ridgeSupport896_suffix_decode_001
theorem ridgeSupport896_eq : candidateSupports 896 = ridgeSupport896_suffix_000 := by
  rw [ridgeSupport896_source]
  exact congrArg Prod.fst ridgeSupport896_suffix_decode_000
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
