module
prelude
public import RootedSixBase01GrowthCacheRidgeSupport592Part000
public import RootedSixBase01GrowthCacheRidgeSupport592Part001
public import RootedSixBase01GrowthCacheRidgeSupport592Part002
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport592_suffix_decode_023 : PackedRawNatGrowth.readList 14 0 ridgeSupport592_rest_023 =
    (ridgeSupport592_suffix_023, ridgeSupport592_rest_023) := by rfl
theorem ridgeSupport592_suffix_decode_022 : PackedRawNatGrowth.readList 14 15 ridgeSupport592_rest_022 =
    (ridgeSupport592_suffix_022, ridgeSupport592_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 15 0
    ridgeSupport592_rest_022 ridgeSupport592_rest_023 ridgeSupport592_rest_023
    ridgeSupport592_022 ridgeSupport592_suffix_023 ridgeSupport592_022_decode ridgeSupport592_suffix_decode_023
theorem ridgeSupport592_suffix_decode_021 : PackedRawNatGrowth.readList 14 47 ridgeSupport592_rest_021 =
    (ridgeSupport592_suffix_021, ridgeSupport592_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 15
    ridgeSupport592_rest_021 ridgeSupport592_rest_022 ridgeSupport592_rest_023
    ridgeSupport592_021 ridgeSupport592_suffix_022 ridgeSupport592_021_decode ridgeSupport592_suffix_decode_022
theorem ridgeSupport592_suffix_decode_020 : PackedRawNatGrowth.readList 14 79 ridgeSupport592_rest_020 =
    (ridgeSupport592_suffix_020, ridgeSupport592_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 47
    ridgeSupport592_rest_020 ridgeSupport592_rest_021 ridgeSupport592_rest_023
    ridgeSupport592_020 ridgeSupport592_suffix_021 ridgeSupport592_020_decode ridgeSupport592_suffix_decode_021
theorem ridgeSupport592_suffix_decode_019 : PackedRawNatGrowth.readList 14 111 ridgeSupport592_rest_019 =
    (ridgeSupport592_suffix_019, ridgeSupport592_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 79
    ridgeSupport592_rest_019 ridgeSupport592_rest_020 ridgeSupport592_rest_023
    ridgeSupport592_019 ridgeSupport592_suffix_020 ridgeSupport592_019_decode ridgeSupport592_suffix_decode_020
theorem ridgeSupport592_suffix_decode_018 : PackedRawNatGrowth.readList 14 143 ridgeSupport592_rest_018 =
    (ridgeSupport592_suffix_018, ridgeSupport592_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 111
    ridgeSupport592_rest_018 ridgeSupport592_rest_019 ridgeSupport592_rest_023
    ridgeSupport592_018 ridgeSupport592_suffix_019 ridgeSupport592_018_decode ridgeSupport592_suffix_decode_019
theorem ridgeSupport592_suffix_decode_017 : PackedRawNatGrowth.readList 14 175 ridgeSupport592_rest_017 =
    (ridgeSupport592_suffix_017, ridgeSupport592_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 143
    ridgeSupport592_rest_017 ridgeSupport592_rest_018 ridgeSupport592_rest_023
    ridgeSupport592_017 ridgeSupport592_suffix_018 ridgeSupport592_017_decode ridgeSupport592_suffix_decode_018
theorem ridgeSupport592_suffix_decode_016 : PackedRawNatGrowth.readList 14 207 ridgeSupport592_rest_016 =
    (ridgeSupport592_suffix_016, ridgeSupport592_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 175
    ridgeSupport592_rest_016 ridgeSupport592_rest_017 ridgeSupport592_rest_023
    ridgeSupport592_016 ridgeSupport592_suffix_017 ridgeSupport592_016_decode ridgeSupport592_suffix_decode_017
theorem ridgeSupport592_suffix_decode_015 : PackedRawNatGrowth.readList 14 239 ridgeSupport592_rest_015 =
    (ridgeSupport592_suffix_015, ridgeSupport592_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 207
    ridgeSupport592_rest_015 ridgeSupport592_rest_016 ridgeSupport592_rest_023
    ridgeSupport592_015 ridgeSupport592_suffix_016 ridgeSupport592_015_decode ridgeSupport592_suffix_decode_016
theorem ridgeSupport592_suffix_decode_014 : PackedRawNatGrowth.readList 14 271 ridgeSupport592_rest_014 =
    (ridgeSupport592_suffix_014, ridgeSupport592_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 239
    ridgeSupport592_rest_014 ridgeSupport592_rest_015 ridgeSupport592_rest_023
    ridgeSupport592_014 ridgeSupport592_suffix_015 ridgeSupport592_014_decode ridgeSupport592_suffix_decode_015
theorem ridgeSupport592_suffix_decode_013 : PackedRawNatGrowth.readList 14 303 ridgeSupport592_rest_013 =
    (ridgeSupport592_suffix_013, ridgeSupport592_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 271
    ridgeSupport592_rest_013 ridgeSupport592_rest_014 ridgeSupport592_rest_023
    ridgeSupport592_013 ridgeSupport592_suffix_014 ridgeSupport592_013_decode ridgeSupport592_suffix_decode_014
theorem ridgeSupport592_suffix_decode_012 : PackedRawNatGrowth.readList 14 335 ridgeSupport592_rest_012 =
    (ridgeSupport592_suffix_012, ridgeSupport592_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 303
    ridgeSupport592_rest_012 ridgeSupport592_rest_013 ridgeSupport592_rest_023
    ridgeSupport592_012 ridgeSupport592_suffix_013 ridgeSupport592_012_decode ridgeSupport592_suffix_decode_013
theorem ridgeSupport592_suffix_decode_011 : PackedRawNatGrowth.readList 14 367 ridgeSupport592_rest_011 =
    (ridgeSupport592_suffix_011, ridgeSupport592_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 335
    ridgeSupport592_rest_011 ridgeSupport592_rest_012 ridgeSupport592_rest_023
    ridgeSupport592_011 ridgeSupport592_suffix_012 ridgeSupport592_011_decode ridgeSupport592_suffix_decode_012
theorem ridgeSupport592_suffix_decode_010 : PackedRawNatGrowth.readList 14 399 ridgeSupport592_rest_010 =
    (ridgeSupport592_suffix_010, ridgeSupport592_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 367
    ridgeSupport592_rest_010 ridgeSupport592_rest_011 ridgeSupport592_rest_023
    ridgeSupport592_010 ridgeSupport592_suffix_011 ridgeSupport592_010_decode ridgeSupport592_suffix_decode_011
theorem ridgeSupport592_suffix_decode_009 : PackedRawNatGrowth.readList 14 431 ridgeSupport592_rest_009 =
    (ridgeSupport592_suffix_009, ridgeSupport592_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 399
    ridgeSupport592_rest_009 ridgeSupport592_rest_010 ridgeSupport592_rest_023
    ridgeSupport592_009 ridgeSupport592_suffix_010 ridgeSupport592_009_decode ridgeSupport592_suffix_decode_010
theorem ridgeSupport592_suffix_decode_008 : PackedRawNatGrowth.readList 14 463 ridgeSupport592_rest_008 =
    (ridgeSupport592_suffix_008, ridgeSupport592_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 431
    ridgeSupport592_rest_008 ridgeSupport592_rest_009 ridgeSupport592_rest_023
    ridgeSupport592_008 ridgeSupport592_suffix_009 ridgeSupport592_008_decode ridgeSupport592_suffix_decode_009
theorem ridgeSupport592_suffix_decode_007 : PackedRawNatGrowth.readList 14 495 ridgeSupport592_rest_007 =
    (ridgeSupport592_suffix_007, ridgeSupport592_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 463
    ridgeSupport592_rest_007 ridgeSupport592_rest_008 ridgeSupport592_rest_023
    ridgeSupport592_007 ridgeSupport592_suffix_008 ridgeSupport592_007_decode ridgeSupport592_suffix_decode_008
theorem ridgeSupport592_suffix_decode_006 : PackedRawNatGrowth.readList 14 527 ridgeSupport592_rest_006 =
    (ridgeSupport592_suffix_006, ridgeSupport592_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 495
    ridgeSupport592_rest_006 ridgeSupport592_rest_007 ridgeSupport592_rest_023
    ridgeSupport592_006 ridgeSupport592_suffix_007 ridgeSupport592_006_decode ridgeSupport592_suffix_decode_007
theorem ridgeSupport592_suffix_decode_005 : PackedRawNatGrowth.readList 14 559 ridgeSupport592_rest_005 =
    (ridgeSupport592_suffix_005, ridgeSupport592_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 527
    ridgeSupport592_rest_005 ridgeSupport592_rest_006 ridgeSupport592_rest_023
    ridgeSupport592_005 ridgeSupport592_suffix_006 ridgeSupport592_005_decode ridgeSupport592_suffix_decode_006
theorem ridgeSupport592_suffix_decode_004 : PackedRawNatGrowth.readList 14 591 ridgeSupport592_rest_004 =
    (ridgeSupport592_suffix_004, ridgeSupport592_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 559
    ridgeSupport592_rest_004 ridgeSupport592_rest_005 ridgeSupport592_rest_023
    ridgeSupport592_004 ridgeSupport592_suffix_005 ridgeSupport592_004_decode ridgeSupport592_suffix_decode_005
theorem ridgeSupport592_suffix_decode_003 : PackedRawNatGrowth.readList 14 623 ridgeSupport592_rest_003 =
    (ridgeSupport592_suffix_003, ridgeSupport592_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 591
    ridgeSupport592_rest_003 ridgeSupport592_rest_004 ridgeSupport592_rest_023
    ridgeSupport592_003 ridgeSupport592_suffix_004 ridgeSupport592_003_decode ridgeSupport592_suffix_decode_004
theorem ridgeSupport592_suffix_decode_002 : PackedRawNatGrowth.readList 14 655 ridgeSupport592_rest_002 =
    (ridgeSupport592_suffix_002, ridgeSupport592_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 623
    ridgeSupport592_rest_002 ridgeSupport592_rest_003 ridgeSupport592_rest_023
    ridgeSupport592_002 ridgeSupport592_suffix_003 ridgeSupport592_002_decode ridgeSupport592_suffix_decode_003
theorem ridgeSupport592_suffix_decode_001 : PackedRawNatGrowth.readList 14 687 ridgeSupport592_rest_001 =
    (ridgeSupport592_suffix_001, ridgeSupport592_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 655
    ridgeSupport592_rest_001 ridgeSupport592_rest_002 ridgeSupport592_rest_023
    ridgeSupport592_001 ridgeSupport592_suffix_002 ridgeSupport592_001_decode ridgeSupport592_suffix_decode_002
theorem ridgeSupport592_suffix_decode_000 : PackedRawNatGrowth.readList 14 719 ridgeSupport592_rest_000 =
    (ridgeSupport592_suffix_000, ridgeSupport592_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 687
    ridgeSupport592_rest_000 ridgeSupport592_rest_001 ridgeSupport592_rest_023
    ridgeSupport592_000 ridgeSupport592_suffix_001 ridgeSupport592_000_decode ridgeSupport592_suffix_decode_001
theorem ridgeSupport592_eq : candidateRows 592 = ridgeSupport592_suffix_000 := by
  rw [ridgeSupport592_source]
  exact congrArg Prod.fst ridgeSupport592_suffix_decode_000
theorem ridgeTest_large_592 : ridgeTest 592 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport592_eq]
    simp only [ridgeSupport592_suffix_000, ridgeSupport592_suffix_001, ridgeSupport592_suffix_002, ridgeSupport592_suffix_003, ridgeSupport592_suffix_004, ridgeSupport592_suffix_005, ridgeSupport592_suffix_006, ridgeSupport592_suffix_007, ridgeSupport592_suffix_008, ridgeSupport592_suffix_009, ridgeSupport592_suffix_010, ridgeSupport592_suffix_011, ridgeSupport592_suffix_012, ridgeSupport592_suffix_013, ridgeSupport592_suffix_014, ridgeSupport592_suffix_015, ridgeSupport592_suffix_016, ridgeSupport592_suffix_017, ridgeSupport592_suffix_018, ridgeSupport592_suffix_019, ridgeSupport592_suffix_020, ridgeSupport592_suffix_021, ridgeSupport592_suffix_022, ridgeSupport592_suffix_023, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport592_000_mask, ridgeSupport592_001_mask, ridgeSupport592_002_mask, ridgeSupport592_003_mask, ridgeSupport592_004_mask, ridgeSupport592_005_mask, ridgeSupport592_006_mask, ridgeSupport592_007_mask, ridgeSupport592_008_mask, ridgeSupport592_009_mask, ridgeSupport592_010_mask, ridgeSupport592_011_mask, ridgeSupport592_012_mask, ridgeSupport592_013_mask, ridgeSupport592_014_mask, ridgeSupport592_015_mask, ridgeSupport592_016_mask, ridgeSupport592_017_mask, ridgeSupport592_018_mask, ridgeSupport592_019_mask, ridgeSupport592_020_mask, ridgeSupport592_021_mask, ridgeSupport592_022_mask]
    decide +kernel
  · rw [ridgeSupport592_eq]
    simp only [ridgeSupport592_suffix_000, ridgeSupport592_suffix_001, ridgeSupport592_suffix_002, ridgeSupport592_suffix_003, ridgeSupport592_suffix_004, ridgeSupport592_suffix_005, ridgeSupport592_suffix_006, ridgeSupport592_suffix_007, ridgeSupport592_suffix_008, ridgeSupport592_suffix_009, ridgeSupport592_suffix_010, ridgeSupport592_suffix_011, ridgeSupport592_suffix_012, ridgeSupport592_suffix_013, ridgeSupport592_suffix_014, ridgeSupport592_suffix_015, ridgeSupport592_suffix_016, ridgeSupport592_suffix_017, ridgeSupport592_suffix_018, ridgeSupport592_suffix_019, ridgeSupport592_suffix_020, ridgeSupport592_suffix_021, ridgeSupport592_suffix_022, ridgeSupport592_suffix_023, List.all_append, List.all_nil, ridgeSupport592_000_checked, ridgeSupport592_001_checked, ridgeSupport592_002_checked, ridgeSupport592_003_checked, ridgeSupport592_004_checked, ridgeSupport592_005_checked, ridgeSupport592_006_checked, ridgeSupport592_007_checked, ridgeSupport592_008_checked, ridgeSupport592_009_checked, ridgeSupport592_010_checked, ridgeSupport592_011_checked, ridgeSupport592_012_checked, ridgeSupport592_013_checked, ridgeSupport592_014_checked, ridgeSupport592_015_checked, ridgeSupport592_016_checked, ridgeSupport592_017_checked, ridgeSupport592_018_checked, ridgeSupport592_019_checked, ridgeSupport592_020_checked, ridgeSupport592_021_checked, ridgeSupport592_022_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase01
