module
prelude
public import RootedSevenTwoSix13GrowthCacheRidgeSupport896Part000
public import RootedSevenTwoSix13GrowthCacheRidgeSupport896Part001
public import RootedSevenTwoSix13GrowthCacheRidgeSupport896Part002
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSevenTwoSix13
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport896_suffix_decode_024 : PackedRawNatGrowth.readList 11 0 ridgeSupport896_rest_024 =
    (ridgeSupport896_suffix_024, ridgeSupport896_rest_024) := by rfl
theorem ridgeSupport896_suffix_decode_023 : PackedRawNatGrowth.readList 11 32 ridgeSupport896_rest_023 =
    (ridgeSupport896_suffix_023, ridgeSupport896_rest_024) :=
  PackedRawNatGrowth.readList_append_of_eq 11 32 0
    ridgeSupport896_rest_023 ridgeSupport896_rest_024 ridgeSupport896_rest_024
    ridgeSupport896_023 ridgeSupport896_suffix_024 ridgeSupport896_023_decode ridgeSupport896_suffix_decode_024
theorem ridgeSupport896_suffix_decode_022 : PackedRawNatGrowth.readList 11 64 ridgeSupport896_rest_022 =
    (ridgeSupport896_suffix_022, ridgeSupport896_rest_024) :=
  PackedRawNatGrowth.readList_append_of_eq 11 32 32
    ridgeSupport896_rest_022 ridgeSupport896_rest_023 ridgeSupport896_rest_024
    ridgeSupport896_022 ridgeSupport896_suffix_023 ridgeSupport896_022_decode ridgeSupport896_suffix_decode_023
theorem ridgeSupport896_suffix_decode_021 : PackedRawNatGrowth.readList 11 96 ridgeSupport896_rest_021 =
    (ridgeSupport896_suffix_021, ridgeSupport896_rest_024) :=
  PackedRawNatGrowth.readList_append_of_eq 11 32 64
    ridgeSupport896_rest_021 ridgeSupport896_rest_022 ridgeSupport896_rest_024
    ridgeSupport896_021 ridgeSupport896_suffix_022 ridgeSupport896_021_decode ridgeSupport896_suffix_decode_022
theorem ridgeSupport896_suffix_decode_020 : PackedRawNatGrowth.readList 11 128 ridgeSupport896_rest_020 =
    (ridgeSupport896_suffix_020, ridgeSupport896_rest_024) :=
  PackedRawNatGrowth.readList_append_of_eq 11 32 96
    ridgeSupport896_rest_020 ridgeSupport896_rest_021 ridgeSupport896_rest_024
    ridgeSupport896_020 ridgeSupport896_suffix_021 ridgeSupport896_020_decode ridgeSupport896_suffix_decode_021
theorem ridgeSupport896_suffix_decode_019 : PackedRawNatGrowth.readList 11 160 ridgeSupport896_rest_019 =
    (ridgeSupport896_suffix_019, ridgeSupport896_rest_024) :=
  PackedRawNatGrowth.readList_append_of_eq 11 32 128
    ridgeSupport896_rest_019 ridgeSupport896_rest_020 ridgeSupport896_rest_024
    ridgeSupport896_019 ridgeSupport896_suffix_020 ridgeSupport896_019_decode ridgeSupport896_suffix_decode_020
theorem ridgeSupport896_suffix_decode_018 : PackedRawNatGrowth.readList 11 192 ridgeSupport896_rest_018 =
    (ridgeSupport896_suffix_018, ridgeSupport896_rest_024) :=
  PackedRawNatGrowth.readList_append_of_eq 11 32 160
    ridgeSupport896_rest_018 ridgeSupport896_rest_019 ridgeSupport896_rest_024
    ridgeSupport896_018 ridgeSupport896_suffix_019 ridgeSupport896_018_decode ridgeSupport896_suffix_decode_019
theorem ridgeSupport896_suffix_decode_017 : PackedRawNatGrowth.readList 11 224 ridgeSupport896_rest_017 =
    (ridgeSupport896_suffix_017, ridgeSupport896_rest_024) :=
  PackedRawNatGrowth.readList_append_of_eq 11 32 192
    ridgeSupport896_rest_017 ridgeSupport896_rest_018 ridgeSupport896_rest_024
    ridgeSupport896_017 ridgeSupport896_suffix_018 ridgeSupport896_017_decode ridgeSupport896_suffix_decode_018
theorem ridgeSupport896_suffix_decode_016 : PackedRawNatGrowth.readList 11 256 ridgeSupport896_rest_016 =
    (ridgeSupport896_suffix_016, ridgeSupport896_rest_024) :=
  PackedRawNatGrowth.readList_append_of_eq 11 32 224
    ridgeSupport896_rest_016 ridgeSupport896_rest_017 ridgeSupport896_rest_024
    ridgeSupport896_016 ridgeSupport896_suffix_017 ridgeSupport896_016_decode ridgeSupport896_suffix_decode_017
theorem ridgeSupport896_suffix_decode_015 : PackedRawNatGrowth.readList 11 288 ridgeSupport896_rest_015 =
    (ridgeSupport896_suffix_015, ridgeSupport896_rest_024) :=
  PackedRawNatGrowth.readList_append_of_eq 11 32 256
    ridgeSupport896_rest_015 ridgeSupport896_rest_016 ridgeSupport896_rest_024
    ridgeSupport896_015 ridgeSupport896_suffix_016 ridgeSupport896_015_decode ridgeSupport896_suffix_decode_016
theorem ridgeSupport896_suffix_decode_014 : PackedRawNatGrowth.readList 11 320 ridgeSupport896_rest_014 =
    (ridgeSupport896_suffix_014, ridgeSupport896_rest_024) :=
  PackedRawNatGrowth.readList_append_of_eq 11 32 288
    ridgeSupport896_rest_014 ridgeSupport896_rest_015 ridgeSupport896_rest_024
    ridgeSupport896_014 ridgeSupport896_suffix_015 ridgeSupport896_014_decode ridgeSupport896_suffix_decode_015
theorem ridgeSupport896_suffix_decode_013 : PackedRawNatGrowth.readList 11 352 ridgeSupport896_rest_013 =
    (ridgeSupport896_suffix_013, ridgeSupport896_rest_024) :=
  PackedRawNatGrowth.readList_append_of_eq 11 32 320
    ridgeSupport896_rest_013 ridgeSupport896_rest_014 ridgeSupport896_rest_024
    ridgeSupport896_013 ridgeSupport896_suffix_014 ridgeSupport896_013_decode ridgeSupport896_suffix_decode_014
theorem ridgeSupport896_suffix_decode_012 : PackedRawNatGrowth.readList 11 384 ridgeSupport896_rest_012 =
    (ridgeSupport896_suffix_012, ridgeSupport896_rest_024) :=
  PackedRawNatGrowth.readList_append_of_eq 11 32 352
    ridgeSupport896_rest_012 ridgeSupport896_rest_013 ridgeSupport896_rest_024
    ridgeSupport896_012 ridgeSupport896_suffix_013 ridgeSupport896_012_decode ridgeSupport896_suffix_decode_013
theorem ridgeSupport896_suffix_decode_011 : PackedRawNatGrowth.readList 11 416 ridgeSupport896_rest_011 =
    (ridgeSupport896_suffix_011, ridgeSupport896_rest_024) :=
  PackedRawNatGrowth.readList_append_of_eq 11 32 384
    ridgeSupport896_rest_011 ridgeSupport896_rest_012 ridgeSupport896_rest_024
    ridgeSupport896_011 ridgeSupport896_suffix_012 ridgeSupport896_011_decode ridgeSupport896_suffix_decode_012
theorem ridgeSupport896_suffix_decode_010 : PackedRawNatGrowth.readList 11 448 ridgeSupport896_rest_010 =
    (ridgeSupport896_suffix_010, ridgeSupport896_rest_024) :=
  PackedRawNatGrowth.readList_append_of_eq 11 32 416
    ridgeSupport896_rest_010 ridgeSupport896_rest_011 ridgeSupport896_rest_024
    ridgeSupport896_010 ridgeSupport896_suffix_011 ridgeSupport896_010_decode ridgeSupport896_suffix_decode_011
theorem ridgeSupport896_suffix_decode_009 : PackedRawNatGrowth.readList 11 480 ridgeSupport896_rest_009 =
    (ridgeSupport896_suffix_009, ridgeSupport896_rest_024) :=
  PackedRawNatGrowth.readList_append_of_eq 11 32 448
    ridgeSupport896_rest_009 ridgeSupport896_rest_010 ridgeSupport896_rest_024
    ridgeSupport896_009 ridgeSupport896_suffix_010 ridgeSupport896_009_decode ridgeSupport896_suffix_decode_010
theorem ridgeSupport896_suffix_decode_008 : PackedRawNatGrowth.readList 11 512 ridgeSupport896_rest_008 =
    (ridgeSupport896_suffix_008, ridgeSupport896_rest_024) :=
  PackedRawNatGrowth.readList_append_of_eq 11 32 480
    ridgeSupport896_rest_008 ridgeSupport896_rest_009 ridgeSupport896_rest_024
    ridgeSupport896_008 ridgeSupport896_suffix_009 ridgeSupport896_008_decode ridgeSupport896_suffix_decode_009
theorem ridgeSupport896_suffix_decode_007 : PackedRawNatGrowth.readList 11 544 ridgeSupport896_rest_007 =
    (ridgeSupport896_suffix_007, ridgeSupport896_rest_024) :=
  PackedRawNatGrowth.readList_append_of_eq 11 32 512
    ridgeSupport896_rest_007 ridgeSupport896_rest_008 ridgeSupport896_rest_024
    ridgeSupport896_007 ridgeSupport896_suffix_008 ridgeSupport896_007_decode ridgeSupport896_suffix_decode_008
theorem ridgeSupport896_suffix_decode_006 : PackedRawNatGrowth.readList 11 576 ridgeSupport896_rest_006 =
    (ridgeSupport896_suffix_006, ridgeSupport896_rest_024) :=
  PackedRawNatGrowth.readList_append_of_eq 11 32 544
    ridgeSupport896_rest_006 ridgeSupport896_rest_007 ridgeSupport896_rest_024
    ridgeSupport896_006 ridgeSupport896_suffix_007 ridgeSupport896_006_decode ridgeSupport896_suffix_decode_007
theorem ridgeSupport896_suffix_decode_005 : PackedRawNatGrowth.readList 11 608 ridgeSupport896_rest_005 =
    (ridgeSupport896_suffix_005, ridgeSupport896_rest_024) :=
  PackedRawNatGrowth.readList_append_of_eq 11 32 576
    ridgeSupport896_rest_005 ridgeSupport896_rest_006 ridgeSupport896_rest_024
    ridgeSupport896_005 ridgeSupport896_suffix_006 ridgeSupport896_005_decode ridgeSupport896_suffix_decode_006
theorem ridgeSupport896_suffix_decode_004 : PackedRawNatGrowth.readList 11 640 ridgeSupport896_rest_004 =
    (ridgeSupport896_suffix_004, ridgeSupport896_rest_024) :=
  PackedRawNatGrowth.readList_append_of_eq 11 32 608
    ridgeSupport896_rest_004 ridgeSupport896_rest_005 ridgeSupport896_rest_024
    ridgeSupport896_004 ridgeSupport896_suffix_005 ridgeSupport896_004_decode ridgeSupport896_suffix_decode_005
theorem ridgeSupport896_suffix_decode_003 : PackedRawNatGrowth.readList 11 672 ridgeSupport896_rest_003 =
    (ridgeSupport896_suffix_003, ridgeSupport896_rest_024) :=
  PackedRawNatGrowth.readList_append_of_eq 11 32 640
    ridgeSupport896_rest_003 ridgeSupport896_rest_004 ridgeSupport896_rest_024
    ridgeSupport896_003 ridgeSupport896_suffix_004 ridgeSupport896_003_decode ridgeSupport896_suffix_decode_004
theorem ridgeSupport896_suffix_decode_002 : PackedRawNatGrowth.readList 11 704 ridgeSupport896_rest_002 =
    (ridgeSupport896_suffix_002, ridgeSupport896_rest_024) :=
  PackedRawNatGrowth.readList_append_of_eq 11 32 672
    ridgeSupport896_rest_002 ridgeSupport896_rest_003 ridgeSupport896_rest_024
    ridgeSupport896_002 ridgeSupport896_suffix_003 ridgeSupport896_002_decode ridgeSupport896_suffix_decode_003
theorem ridgeSupport896_suffix_decode_001 : PackedRawNatGrowth.readList 11 736 ridgeSupport896_rest_001 =
    (ridgeSupport896_suffix_001, ridgeSupport896_rest_024) :=
  PackedRawNatGrowth.readList_append_of_eq 11 32 704
    ridgeSupport896_rest_001 ridgeSupport896_rest_002 ridgeSupport896_rest_024
    ridgeSupport896_001 ridgeSupport896_suffix_002 ridgeSupport896_001_decode ridgeSupport896_suffix_decode_002
theorem ridgeSupport896_suffix_decode_000 : PackedRawNatGrowth.readList 11 768 ridgeSupport896_rest_000 =
    (ridgeSupport896_suffix_000, ridgeSupport896_rest_024) :=
  PackedRawNatGrowth.readList_append_of_eq 11 32 736
    ridgeSupport896_rest_000 ridgeSupport896_rest_001 ridgeSupport896_rest_024
    ridgeSupport896_000 ridgeSupport896_suffix_001 ridgeSupport896_000_decode ridgeSupport896_suffix_decode_001
theorem ridgeSupport896_eq : candidateRows 896 = ridgeSupport896_suffix_000 := by
  rw [ridgeSupport896_source]
  exact congrArg Prod.fst ridgeSupport896_suffix_decode_000
theorem ridgeTest_large_896 : ridgeTest 896 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport896_eq]
    simp only [ridgeSupport896_suffix_000, ridgeSupport896_suffix_001, ridgeSupport896_suffix_002, ridgeSupport896_suffix_003, ridgeSupport896_suffix_004, ridgeSupport896_suffix_005, ridgeSupport896_suffix_006, ridgeSupport896_suffix_007, ridgeSupport896_suffix_008, ridgeSupport896_suffix_009, ridgeSupport896_suffix_010, ridgeSupport896_suffix_011, ridgeSupport896_suffix_012, ridgeSupport896_suffix_013, ridgeSupport896_suffix_014, ridgeSupport896_suffix_015, ridgeSupport896_suffix_016, ridgeSupport896_suffix_017, ridgeSupport896_suffix_018, ridgeSupport896_suffix_019, ridgeSupport896_suffix_020, ridgeSupport896_suffix_021, ridgeSupport896_suffix_022, ridgeSupport896_suffix_023, ridgeSupport896_suffix_024, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport896_000_mask, ridgeSupport896_001_mask, ridgeSupport896_002_mask, ridgeSupport896_003_mask, ridgeSupport896_004_mask, ridgeSupport896_005_mask, ridgeSupport896_006_mask, ridgeSupport896_007_mask, ridgeSupport896_008_mask, ridgeSupport896_009_mask, ridgeSupport896_010_mask, ridgeSupport896_011_mask, ridgeSupport896_012_mask, ridgeSupport896_013_mask, ridgeSupport896_014_mask, ridgeSupport896_015_mask, ridgeSupport896_016_mask, ridgeSupport896_017_mask, ridgeSupport896_018_mask, ridgeSupport896_019_mask, ridgeSupport896_020_mask, ridgeSupport896_021_mask, ridgeSupport896_022_mask, ridgeSupport896_023_mask]
    decide +kernel
  · rw [ridgeSupport896_eq]
    simp only [ridgeSupport896_suffix_000, ridgeSupport896_suffix_001, ridgeSupport896_suffix_002, ridgeSupport896_suffix_003, ridgeSupport896_suffix_004, ridgeSupport896_suffix_005, ridgeSupport896_suffix_006, ridgeSupport896_suffix_007, ridgeSupport896_suffix_008, ridgeSupport896_suffix_009, ridgeSupport896_suffix_010, ridgeSupport896_suffix_011, ridgeSupport896_suffix_012, ridgeSupport896_suffix_013, ridgeSupport896_suffix_014, ridgeSupport896_suffix_015, ridgeSupport896_suffix_016, ridgeSupport896_suffix_017, ridgeSupport896_suffix_018, ridgeSupport896_suffix_019, ridgeSupport896_suffix_020, ridgeSupport896_suffix_021, ridgeSupport896_suffix_022, ridgeSupport896_suffix_023, ridgeSupport896_suffix_024, List.all_append, List.all_nil, ridgeSupport896_000_checked, ridgeSupport896_001_checked, ridgeSupport896_002_checked, ridgeSupport896_003_checked, ridgeSupport896_004_checked, ridgeSupport896_005_checked, ridgeSupport896_006_checked, ridgeSupport896_007_checked, ridgeSupport896_008_checked, ridgeSupport896_009_checked, ridgeSupport896_010_checked, ridgeSupport896_011_checked, ridgeSupport896_012_checked, ridgeSupport896_013_checked, ridgeSupport896_014_checked, ridgeSupport896_015_checked, ridgeSupport896_016_checked, ridgeSupport896_017_checked, ridgeSupport896_018_checked, ridgeSupport896_019_checked, ridgeSupport896_020_checked, ridgeSupport896_021_checked, ridgeSupport896_022_checked, ridgeSupport896_023_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSevenTwoSix13
