module
prelude
public import RootedSixBase01GrowthCacheRidgeSupport608Part000
public import RootedSixBase01GrowthCacheRidgeSupport608Part001
public import RootedSixBase01GrowthCacheRidgeSupport608Part002
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport608_suffix_decode_023 : PackedRawNatGrowth.readList 14 0 ridgeSupport608_rest_023 =
    (ridgeSupport608_suffix_023, ridgeSupport608_rest_023) := by rfl
theorem ridgeSupport608_suffix_decode_022 : PackedRawNatGrowth.readList 14 15 ridgeSupport608_rest_022 =
    (ridgeSupport608_suffix_022, ridgeSupport608_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 15 0
    ridgeSupport608_rest_022 ridgeSupport608_rest_023 ridgeSupport608_rest_023
    ridgeSupport608_022 ridgeSupport608_suffix_023 ridgeSupport608_022_decode ridgeSupport608_suffix_decode_023
theorem ridgeSupport608_suffix_decode_021 : PackedRawNatGrowth.readList 14 47 ridgeSupport608_rest_021 =
    (ridgeSupport608_suffix_021, ridgeSupport608_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 15
    ridgeSupport608_rest_021 ridgeSupport608_rest_022 ridgeSupport608_rest_023
    ridgeSupport608_021 ridgeSupport608_suffix_022 ridgeSupport608_021_decode ridgeSupport608_suffix_decode_022
theorem ridgeSupport608_suffix_decode_020 : PackedRawNatGrowth.readList 14 79 ridgeSupport608_rest_020 =
    (ridgeSupport608_suffix_020, ridgeSupport608_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 47
    ridgeSupport608_rest_020 ridgeSupport608_rest_021 ridgeSupport608_rest_023
    ridgeSupport608_020 ridgeSupport608_suffix_021 ridgeSupport608_020_decode ridgeSupport608_suffix_decode_021
theorem ridgeSupport608_suffix_decode_019 : PackedRawNatGrowth.readList 14 111 ridgeSupport608_rest_019 =
    (ridgeSupport608_suffix_019, ridgeSupport608_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 79
    ridgeSupport608_rest_019 ridgeSupport608_rest_020 ridgeSupport608_rest_023
    ridgeSupport608_019 ridgeSupport608_suffix_020 ridgeSupport608_019_decode ridgeSupport608_suffix_decode_020
theorem ridgeSupport608_suffix_decode_018 : PackedRawNatGrowth.readList 14 143 ridgeSupport608_rest_018 =
    (ridgeSupport608_suffix_018, ridgeSupport608_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 111
    ridgeSupport608_rest_018 ridgeSupport608_rest_019 ridgeSupport608_rest_023
    ridgeSupport608_018 ridgeSupport608_suffix_019 ridgeSupport608_018_decode ridgeSupport608_suffix_decode_019
theorem ridgeSupport608_suffix_decode_017 : PackedRawNatGrowth.readList 14 175 ridgeSupport608_rest_017 =
    (ridgeSupport608_suffix_017, ridgeSupport608_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 143
    ridgeSupport608_rest_017 ridgeSupport608_rest_018 ridgeSupport608_rest_023
    ridgeSupport608_017 ridgeSupport608_suffix_018 ridgeSupport608_017_decode ridgeSupport608_suffix_decode_018
theorem ridgeSupport608_suffix_decode_016 : PackedRawNatGrowth.readList 14 207 ridgeSupport608_rest_016 =
    (ridgeSupport608_suffix_016, ridgeSupport608_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 175
    ridgeSupport608_rest_016 ridgeSupport608_rest_017 ridgeSupport608_rest_023
    ridgeSupport608_016 ridgeSupport608_suffix_017 ridgeSupport608_016_decode ridgeSupport608_suffix_decode_017
theorem ridgeSupport608_suffix_decode_015 : PackedRawNatGrowth.readList 14 239 ridgeSupport608_rest_015 =
    (ridgeSupport608_suffix_015, ridgeSupport608_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 207
    ridgeSupport608_rest_015 ridgeSupport608_rest_016 ridgeSupport608_rest_023
    ridgeSupport608_015 ridgeSupport608_suffix_016 ridgeSupport608_015_decode ridgeSupport608_suffix_decode_016
theorem ridgeSupport608_suffix_decode_014 : PackedRawNatGrowth.readList 14 271 ridgeSupport608_rest_014 =
    (ridgeSupport608_suffix_014, ridgeSupport608_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 239
    ridgeSupport608_rest_014 ridgeSupport608_rest_015 ridgeSupport608_rest_023
    ridgeSupport608_014 ridgeSupport608_suffix_015 ridgeSupport608_014_decode ridgeSupport608_suffix_decode_015
theorem ridgeSupport608_suffix_decode_013 : PackedRawNatGrowth.readList 14 303 ridgeSupport608_rest_013 =
    (ridgeSupport608_suffix_013, ridgeSupport608_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 271
    ridgeSupport608_rest_013 ridgeSupport608_rest_014 ridgeSupport608_rest_023
    ridgeSupport608_013 ridgeSupport608_suffix_014 ridgeSupport608_013_decode ridgeSupport608_suffix_decode_014
theorem ridgeSupport608_suffix_decode_012 : PackedRawNatGrowth.readList 14 335 ridgeSupport608_rest_012 =
    (ridgeSupport608_suffix_012, ridgeSupport608_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 303
    ridgeSupport608_rest_012 ridgeSupport608_rest_013 ridgeSupport608_rest_023
    ridgeSupport608_012 ridgeSupport608_suffix_013 ridgeSupport608_012_decode ridgeSupport608_suffix_decode_013
theorem ridgeSupport608_suffix_decode_011 : PackedRawNatGrowth.readList 14 367 ridgeSupport608_rest_011 =
    (ridgeSupport608_suffix_011, ridgeSupport608_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 335
    ridgeSupport608_rest_011 ridgeSupport608_rest_012 ridgeSupport608_rest_023
    ridgeSupport608_011 ridgeSupport608_suffix_012 ridgeSupport608_011_decode ridgeSupport608_suffix_decode_012
theorem ridgeSupport608_suffix_decode_010 : PackedRawNatGrowth.readList 14 399 ridgeSupport608_rest_010 =
    (ridgeSupport608_suffix_010, ridgeSupport608_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 367
    ridgeSupport608_rest_010 ridgeSupport608_rest_011 ridgeSupport608_rest_023
    ridgeSupport608_010 ridgeSupport608_suffix_011 ridgeSupport608_010_decode ridgeSupport608_suffix_decode_011
theorem ridgeSupport608_suffix_decode_009 : PackedRawNatGrowth.readList 14 431 ridgeSupport608_rest_009 =
    (ridgeSupport608_suffix_009, ridgeSupport608_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 399
    ridgeSupport608_rest_009 ridgeSupport608_rest_010 ridgeSupport608_rest_023
    ridgeSupport608_009 ridgeSupport608_suffix_010 ridgeSupport608_009_decode ridgeSupport608_suffix_decode_010
theorem ridgeSupport608_suffix_decode_008 : PackedRawNatGrowth.readList 14 463 ridgeSupport608_rest_008 =
    (ridgeSupport608_suffix_008, ridgeSupport608_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 431
    ridgeSupport608_rest_008 ridgeSupport608_rest_009 ridgeSupport608_rest_023
    ridgeSupport608_008 ridgeSupport608_suffix_009 ridgeSupport608_008_decode ridgeSupport608_suffix_decode_009
theorem ridgeSupport608_suffix_decode_007 : PackedRawNatGrowth.readList 14 495 ridgeSupport608_rest_007 =
    (ridgeSupport608_suffix_007, ridgeSupport608_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 463
    ridgeSupport608_rest_007 ridgeSupport608_rest_008 ridgeSupport608_rest_023
    ridgeSupport608_007 ridgeSupport608_suffix_008 ridgeSupport608_007_decode ridgeSupport608_suffix_decode_008
theorem ridgeSupport608_suffix_decode_006 : PackedRawNatGrowth.readList 14 527 ridgeSupport608_rest_006 =
    (ridgeSupport608_suffix_006, ridgeSupport608_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 495
    ridgeSupport608_rest_006 ridgeSupport608_rest_007 ridgeSupport608_rest_023
    ridgeSupport608_006 ridgeSupport608_suffix_007 ridgeSupport608_006_decode ridgeSupport608_suffix_decode_007
theorem ridgeSupport608_suffix_decode_005 : PackedRawNatGrowth.readList 14 559 ridgeSupport608_rest_005 =
    (ridgeSupport608_suffix_005, ridgeSupport608_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 527
    ridgeSupport608_rest_005 ridgeSupport608_rest_006 ridgeSupport608_rest_023
    ridgeSupport608_005 ridgeSupport608_suffix_006 ridgeSupport608_005_decode ridgeSupport608_suffix_decode_006
theorem ridgeSupport608_suffix_decode_004 : PackedRawNatGrowth.readList 14 591 ridgeSupport608_rest_004 =
    (ridgeSupport608_suffix_004, ridgeSupport608_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 559
    ridgeSupport608_rest_004 ridgeSupport608_rest_005 ridgeSupport608_rest_023
    ridgeSupport608_004 ridgeSupport608_suffix_005 ridgeSupport608_004_decode ridgeSupport608_suffix_decode_005
theorem ridgeSupport608_suffix_decode_003 : PackedRawNatGrowth.readList 14 623 ridgeSupport608_rest_003 =
    (ridgeSupport608_suffix_003, ridgeSupport608_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 591
    ridgeSupport608_rest_003 ridgeSupport608_rest_004 ridgeSupport608_rest_023
    ridgeSupport608_003 ridgeSupport608_suffix_004 ridgeSupport608_003_decode ridgeSupport608_suffix_decode_004
theorem ridgeSupport608_suffix_decode_002 : PackedRawNatGrowth.readList 14 655 ridgeSupport608_rest_002 =
    (ridgeSupport608_suffix_002, ridgeSupport608_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 623
    ridgeSupport608_rest_002 ridgeSupport608_rest_003 ridgeSupport608_rest_023
    ridgeSupport608_002 ridgeSupport608_suffix_003 ridgeSupport608_002_decode ridgeSupport608_suffix_decode_003
theorem ridgeSupport608_suffix_decode_001 : PackedRawNatGrowth.readList 14 687 ridgeSupport608_rest_001 =
    (ridgeSupport608_suffix_001, ridgeSupport608_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 655
    ridgeSupport608_rest_001 ridgeSupport608_rest_002 ridgeSupport608_rest_023
    ridgeSupport608_001 ridgeSupport608_suffix_002 ridgeSupport608_001_decode ridgeSupport608_suffix_decode_002
theorem ridgeSupport608_suffix_decode_000 : PackedRawNatGrowth.readList 14 719 ridgeSupport608_rest_000 =
    (ridgeSupport608_suffix_000, ridgeSupport608_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 687
    ridgeSupport608_rest_000 ridgeSupport608_rest_001 ridgeSupport608_rest_023
    ridgeSupport608_000 ridgeSupport608_suffix_001 ridgeSupport608_000_decode ridgeSupport608_suffix_decode_001
theorem ridgeSupport608_eq : candidateRows 608 = ridgeSupport608_suffix_000 := by
  rw [ridgeSupport608_source]
  exact congrArg Prod.fst ridgeSupport608_suffix_decode_000
theorem ridgeTest_large_608 : ridgeTest 608 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport608_eq]
    simp only [ridgeSupport608_suffix_000, ridgeSupport608_suffix_001, ridgeSupport608_suffix_002, ridgeSupport608_suffix_003, ridgeSupport608_suffix_004, ridgeSupport608_suffix_005, ridgeSupport608_suffix_006, ridgeSupport608_suffix_007, ridgeSupport608_suffix_008, ridgeSupport608_suffix_009, ridgeSupport608_suffix_010, ridgeSupport608_suffix_011, ridgeSupport608_suffix_012, ridgeSupport608_suffix_013, ridgeSupport608_suffix_014, ridgeSupport608_suffix_015, ridgeSupport608_suffix_016, ridgeSupport608_suffix_017, ridgeSupport608_suffix_018, ridgeSupport608_suffix_019, ridgeSupport608_suffix_020, ridgeSupport608_suffix_021, ridgeSupport608_suffix_022, ridgeSupport608_suffix_023, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport608_000_mask, ridgeSupport608_001_mask, ridgeSupport608_002_mask, ridgeSupport608_003_mask, ridgeSupport608_004_mask, ridgeSupport608_005_mask, ridgeSupport608_006_mask, ridgeSupport608_007_mask, ridgeSupport608_008_mask, ridgeSupport608_009_mask, ridgeSupport608_010_mask, ridgeSupport608_011_mask, ridgeSupport608_012_mask, ridgeSupport608_013_mask, ridgeSupport608_014_mask, ridgeSupport608_015_mask, ridgeSupport608_016_mask, ridgeSupport608_017_mask, ridgeSupport608_018_mask, ridgeSupport608_019_mask, ridgeSupport608_020_mask, ridgeSupport608_021_mask, ridgeSupport608_022_mask]
    decide +kernel
  · rw [ridgeSupport608_eq]
    simp only [ridgeSupport608_suffix_000, ridgeSupport608_suffix_001, ridgeSupport608_suffix_002, ridgeSupport608_suffix_003, ridgeSupport608_suffix_004, ridgeSupport608_suffix_005, ridgeSupport608_suffix_006, ridgeSupport608_suffix_007, ridgeSupport608_suffix_008, ridgeSupport608_suffix_009, ridgeSupport608_suffix_010, ridgeSupport608_suffix_011, ridgeSupport608_suffix_012, ridgeSupport608_suffix_013, ridgeSupport608_suffix_014, ridgeSupport608_suffix_015, ridgeSupport608_suffix_016, ridgeSupport608_suffix_017, ridgeSupport608_suffix_018, ridgeSupport608_suffix_019, ridgeSupport608_suffix_020, ridgeSupport608_suffix_021, ridgeSupport608_suffix_022, ridgeSupport608_suffix_023, List.all_append, List.all_nil, ridgeSupport608_000_checked, ridgeSupport608_001_checked, ridgeSupport608_002_checked, ridgeSupport608_003_checked, ridgeSupport608_004_checked, ridgeSupport608_005_checked, ridgeSupport608_006_checked, ridgeSupport608_007_checked, ridgeSupport608_008_checked, ridgeSupport608_009_checked, ridgeSupport608_010_checked, ridgeSupport608_011_checked, ridgeSupport608_012_checked, ridgeSupport608_013_checked, ridgeSupport608_014_checked, ridgeSupport608_015_checked, ridgeSupport608_016_checked, ridgeSupport608_017_checked, ridgeSupport608_018_checked, ridgeSupport608_019_checked, ridgeSupport608_020_checked, ridgeSupport608_021_checked, ridgeSupport608_022_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase01
