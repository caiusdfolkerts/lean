module
prelude
public import RootedSixBase01GrowthCacheRidgeSupport208Part000
public import RootedSixBase01GrowthCacheRidgeSupport208Part001
public import RootedSixBase01GrowthCacheRidgeSupport208Part002
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport208_suffix_decode_023 : PackedRawNatGrowth.readList 14 0 ridgeSupport208_rest_023 =
    (ridgeSupport208_suffix_023, ridgeSupport208_rest_023) := by rfl
theorem ridgeSupport208_suffix_decode_022 : PackedRawNatGrowth.readList 14 15 ridgeSupport208_rest_022 =
    (ridgeSupport208_suffix_022, ridgeSupport208_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 15 0
    ridgeSupport208_rest_022 ridgeSupport208_rest_023 ridgeSupport208_rest_023
    ridgeSupport208_022 ridgeSupport208_suffix_023 ridgeSupport208_022_decode ridgeSupport208_suffix_decode_023
theorem ridgeSupport208_suffix_decode_021 : PackedRawNatGrowth.readList 14 47 ridgeSupport208_rest_021 =
    (ridgeSupport208_suffix_021, ridgeSupport208_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 15
    ridgeSupport208_rest_021 ridgeSupport208_rest_022 ridgeSupport208_rest_023
    ridgeSupport208_021 ridgeSupport208_suffix_022 ridgeSupport208_021_decode ridgeSupport208_suffix_decode_022
theorem ridgeSupport208_suffix_decode_020 : PackedRawNatGrowth.readList 14 79 ridgeSupport208_rest_020 =
    (ridgeSupport208_suffix_020, ridgeSupport208_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 47
    ridgeSupport208_rest_020 ridgeSupport208_rest_021 ridgeSupport208_rest_023
    ridgeSupport208_020 ridgeSupport208_suffix_021 ridgeSupport208_020_decode ridgeSupport208_suffix_decode_021
theorem ridgeSupport208_suffix_decode_019 : PackedRawNatGrowth.readList 14 111 ridgeSupport208_rest_019 =
    (ridgeSupport208_suffix_019, ridgeSupport208_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 79
    ridgeSupport208_rest_019 ridgeSupport208_rest_020 ridgeSupport208_rest_023
    ridgeSupport208_019 ridgeSupport208_suffix_020 ridgeSupport208_019_decode ridgeSupport208_suffix_decode_020
theorem ridgeSupport208_suffix_decode_018 : PackedRawNatGrowth.readList 14 143 ridgeSupport208_rest_018 =
    (ridgeSupport208_suffix_018, ridgeSupport208_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 111
    ridgeSupport208_rest_018 ridgeSupport208_rest_019 ridgeSupport208_rest_023
    ridgeSupport208_018 ridgeSupport208_suffix_019 ridgeSupport208_018_decode ridgeSupport208_suffix_decode_019
theorem ridgeSupport208_suffix_decode_017 : PackedRawNatGrowth.readList 14 175 ridgeSupport208_rest_017 =
    (ridgeSupport208_suffix_017, ridgeSupport208_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 143
    ridgeSupport208_rest_017 ridgeSupport208_rest_018 ridgeSupport208_rest_023
    ridgeSupport208_017 ridgeSupport208_suffix_018 ridgeSupport208_017_decode ridgeSupport208_suffix_decode_018
theorem ridgeSupport208_suffix_decode_016 : PackedRawNatGrowth.readList 14 207 ridgeSupport208_rest_016 =
    (ridgeSupport208_suffix_016, ridgeSupport208_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 175
    ridgeSupport208_rest_016 ridgeSupport208_rest_017 ridgeSupport208_rest_023
    ridgeSupport208_016 ridgeSupport208_suffix_017 ridgeSupport208_016_decode ridgeSupport208_suffix_decode_017
theorem ridgeSupport208_suffix_decode_015 : PackedRawNatGrowth.readList 14 239 ridgeSupport208_rest_015 =
    (ridgeSupport208_suffix_015, ridgeSupport208_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 207
    ridgeSupport208_rest_015 ridgeSupport208_rest_016 ridgeSupport208_rest_023
    ridgeSupport208_015 ridgeSupport208_suffix_016 ridgeSupport208_015_decode ridgeSupport208_suffix_decode_016
theorem ridgeSupport208_suffix_decode_014 : PackedRawNatGrowth.readList 14 271 ridgeSupport208_rest_014 =
    (ridgeSupport208_suffix_014, ridgeSupport208_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 239
    ridgeSupport208_rest_014 ridgeSupport208_rest_015 ridgeSupport208_rest_023
    ridgeSupport208_014 ridgeSupport208_suffix_015 ridgeSupport208_014_decode ridgeSupport208_suffix_decode_015
theorem ridgeSupport208_suffix_decode_013 : PackedRawNatGrowth.readList 14 303 ridgeSupport208_rest_013 =
    (ridgeSupport208_suffix_013, ridgeSupport208_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 271
    ridgeSupport208_rest_013 ridgeSupport208_rest_014 ridgeSupport208_rest_023
    ridgeSupport208_013 ridgeSupport208_suffix_014 ridgeSupport208_013_decode ridgeSupport208_suffix_decode_014
theorem ridgeSupport208_suffix_decode_012 : PackedRawNatGrowth.readList 14 335 ridgeSupport208_rest_012 =
    (ridgeSupport208_suffix_012, ridgeSupport208_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 303
    ridgeSupport208_rest_012 ridgeSupport208_rest_013 ridgeSupport208_rest_023
    ridgeSupport208_012 ridgeSupport208_suffix_013 ridgeSupport208_012_decode ridgeSupport208_suffix_decode_013
theorem ridgeSupport208_suffix_decode_011 : PackedRawNatGrowth.readList 14 367 ridgeSupport208_rest_011 =
    (ridgeSupport208_suffix_011, ridgeSupport208_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 335
    ridgeSupport208_rest_011 ridgeSupport208_rest_012 ridgeSupport208_rest_023
    ridgeSupport208_011 ridgeSupport208_suffix_012 ridgeSupport208_011_decode ridgeSupport208_suffix_decode_012
theorem ridgeSupport208_suffix_decode_010 : PackedRawNatGrowth.readList 14 399 ridgeSupport208_rest_010 =
    (ridgeSupport208_suffix_010, ridgeSupport208_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 367
    ridgeSupport208_rest_010 ridgeSupport208_rest_011 ridgeSupport208_rest_023
    ridgeSupport208_010 ridgeSupport208_suffix_011 ridgeSupport208_010_decode ridgeSupport208_suffix_decode_011
theorem ridgeSupport208_suffix_decode_009 : PackedRawNatGrowth.readList 14 431 ridgeSupport208_rest_009 =
    (ridgeSupport208_suffix_009, ridgeSupport208_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 399
    ridgeSupport208_rest_009 ridgeSupport208_rest_010 ridgeSupport208_rest_023
    ridgeSupport208_009 ridgeSupport208_suffix_010 ridgeSupport208_009_decode ridgeSupport208_suffix_decode_010
theorem ridgeSupport208_suffix_decode_008 : PackedRawNatGrowth.readList 14 463 ridgeSupport208_rest_008 =
    (ridgeSupport208_suffix_008, ridgeSupport208_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 431
    ridgeSupport208_rest_008 ridgeSupport208_rest_009 ridgeSupport208_rest_023
    ridgeSupport208_008 ridgeSupport208_suffix_009 ridgeSupport208_008_decode ridgeSupport208_suffix_decode_009
theorem ridgeSupport208_suffix_decode_007 : PackedRawNatGrowth.readList 14 495 ridgeSupport208_rest_007 =
    (ridgeSupport208_suffix_007, ridgeSupport208_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 463
    ridgeSupport208_rest_007 ridgeSupport208_rest_008 ridgeSupport208_rest_023
    ridgeSupport208_007 ridgeSupport208_suffix_008 ridgeSupport208_007_decode ridgeSupport208_suffix_decode_008
theorem ridgeSupport208_suffix_decode_006 : PackedRawNatGrowth.readList 14 527 ridgeSupport208_rest_006 =
    (ridgeSupport208_suffix_006, ridgeSupport208_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 495
    ridgeSupport208_rest_006 ridgeSupport208_rest_007 ridgeSupport208_rest_023
    ridgeSupport208_006 ridgeSupport208_suffix_007 ridgeSupport208_006_decode ridgeSupport208_suffix_decode_007
theorem ridgeSupport208_suffix_decode_005 : PackedRawNatGrowth.readList 14 559 ridgeSupport208_rest_005 =
    (ridgeSupport208_suffix_005, ridgeSupport208_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 527
    ridgeSupport208_rest_005 ridgeSupport208_rest_006 ridgeSupport208_rest_023
    ridgeSupport208_005 ridgeSupport208_suffix_006 ridgeSupport208_005_decode ridgeSupport208_suffix_decode_006
theorem ridgeSupport208_suffix_decode_004 : PackedRawNatGrowth.readList 14 591 ridgeSupport208_rest_004 =
    (ridgeSupport208_suffix_004, ridgeSupport208_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 559
    ridgeSupport208_rest_004 ridgeSupport208_rest_005 ridgeSupport208_rest_023
    ridgeSupport208_004 ridgeSupport208_suffix_005 ridgeSupport208_004_decode ridgeSupport208_suffix_decode_005
theorem ridgeSupport208_suffix_decode_003 : PackedRawNatGrowth.readList 14 623 ridgeSupport208_rest_003 =
    (ridgeSupport208_suffix_003, ridgeSupport208_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 591
    ridgeSupport208_rest_003 ridgeSupport208_rest_004 ridgeSupport208_rest_023
    ridgeSupport208_003 ridgeSupport208_suffix_004 ridgeSupport208_003_decode ridgeSupport208_suffix_decode_004
theorem ridgeSupport208_suffix_decode_002 : PackedRawNatGrowth.readList 14 655 ridgeSupport208_rest_002 =
    (ridgeSupport208_suffix_002, ridgeSupport208_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 623
    ridgeSupport208_rest_002 ridgeSupport208_rest_003 ridgeSupport208_rest_023
    ridgeSupport208_002 ridgeSupport208_suffix_003 ridgeSupport208_002_decode ridgeSupport208_suffix_decode_003
theorem ridgeSupport208_suffix_decode_001 : PackedRawNatGrowth.readList 14 687 ridgeSupport208_rest_001 =
    (ridgeSupport208_suffix_001, ridgeSupport208_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 655
    ridgeSupport208_rest_001 ridgeSupport208_rest_002 ridgeSupport208_rest_023
    ridgeSupport208_001 ridgeSupport208_suffix_002 ridgeSupport208_001_decode ridgeSupport208_suffix_decode_002
theorem ridgeSupport208_suffix_decode_000 : PackedRawNatGrowth.readList 14 719 ridgeSupport208_rest_000 =
    (ridgeSupport208_suffix_000, ridgeSupport208_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 687
    ridgeSupport208_rest_000 ridgeSupport208_rest_001 ridgeSupport208_rest_023
    ridgeSupport208_000 ridgeSupport208_suffix_001 ridgeSupport208_000_decode ridgeSupport208_suffix_decode_001
theorem ridgeSupport208_eq : candidateRows 208 = ridgeSupport208_suffix_000 := by
  rw [ridgeSupport208_source]
  exact congrArg Prod.fst ridgeSupport208_suffix_decode_000
theorem ridgeTest_large_208 : ridgeTest 208 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport208_eq]
    simp only [ridgeSupport208_suffix_000, ridgeSupport208_suffix_001, ridgeSupport208_suffix_002, ridgeSupport208_suffix_003, ridgeSupport208_suffix_004, ridgeSupport208_suffix_005, ridgeSupport208_suffix_006, ridgeSupport208_suffix_007, ridgeSupport208_suffix_008, ridgeSupport208_suffix_009, ridgeSupport208_suffix_010, ridgeSupport208_suffix_011, ridgeSupport208_suffix_012, ridgeSupport208_suffix_013, ridgeSupport208_suffix_014, ridgeSupport208_suffix_015, ridgeSupport208_suffix_016, ridgeSupport208_suffix_017, ridgeSupport208_suffix_018, ridgeSupport208_suffix_019, ridgeSupport208_suffix_020, ridgeSupport208_suffix_021, ridgeSupport208_suffix_022, ridgeSupport208_suffix_023, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport208_000_mask, ridgeSupport208_001_mask, ridgeSupport208_002_mask, ridgeSupport208_003_mask, ridgeSupport208_004_mask, ridgeSupport208_005_mask, ridgeSupport208_006_mask, ridgeSupport208_007_mask, ridgeSupport208_008_mask, ridgeSupport208_009_mask, ridgeSupport208_010_mask, ridgeSupport208_011_mask, ridgeSupport208_012_mask, ridgeSupport208_013_mask, ridgeSupport208_014_mask, ridgeSupport208_015_mask, ridgeSupport208_016_mask, ridgeSupport208_017_mask, ridgeSupport208_018_mask, ridgeSupport208_019_mask, ridgeSupport208_020_mask, ridgeSupport208_021_mask, ridgeSupport208_022_mask]
    decide +kernel
  · rw [ridgeSupport208_eq]
    simp only [ridgeSupport208_suffix_000, ridgeSupport208_suffix_001, ridgeSupport208_suffix_002, ridgeSupport208_suffix_003, ridgeSupport208_suffix_004, ridgeSupport208_suffix_005, ridgeSupport208_suffix_006, ridgeSupport208_suffix_007, ridgeSupport208_suffix_008, ridgeSupport208_suffix_009, ridgeSupport208_suffix_010, ridgeSupport208_suffix_011, ridgeSupport208_suffix_012, ridgeSupport208_suffix_013, ridgeSupport208_suffix_014, ridgeSupport208_suffix_015, ridgeSupport208_suffix_016, ridgeSupport208_suffix_017, ridgeSupport208_suffix_018, ridgeSupport208_suffix_019, ridgeSupport208_suffix_020, ridgeSupport208_suffix_021, ridgeSupport208_suffix_022, ridgeSupport208_suffix_023, List.all_append, List.all_nil, ridgeSupport208_000_checked, ridgeSupport208_001_checked, ridgeSupport208_002_checked, ridgeSupport208_003_checked, ridgeSupport208_004_checked, ridgeSupport208_005_checked, ridgeSupport208_006_checked, ridgeSupport208_007_checked, ridgeSupport208_008_checked, ridgeSupport208_009_checked, ridgeSupport208_010_checked, ridgeSupport208_011_checked, ridgeSupport208_012_checked, ridgeSupport208_013_checked, ridgeSupport208_014_checked, ridgeSupport208_015_checked, ridgeSupport208_016_checked, ridgeSupport208_017_checked, ridgeSupport208_018_checked, ridgeSupport208_019_checked, ridgeSupport208_020_checked, ridgeSupport208_021_checked, ridgeSupport208_022_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase01
