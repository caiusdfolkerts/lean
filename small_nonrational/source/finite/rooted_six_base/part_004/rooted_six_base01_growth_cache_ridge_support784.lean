module
prelude
public import RootedSixBase01GrowthCacheRidgeSupport784Part000
public import RootedSixBase01GrowthCacheRidgeSupport784Part001
public import RootedSixBase01GrowthCacheRidgeSupport784Part002
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport784_suffix_decode_023 : PackedRawNatGrowth.readList 14 0 ridgeSupport784_rest_023 =
    (ridgeSupport784_suffix_023, ridgeSupport784_rest_023) := by rfl
theorem ridgeSupport784_suffix_decode_022 : PackedRawNatGrowth.readList 14 15 ridgeSupport784_rest_022 =
    (ridgeSupport784_suffix_022, ridgeSupport784_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 15 0
    ridgeSupport784_rest_022 ridgeSupport784_rest_023 ridgeSupport784_rest_023
    ridgeSupport784_022 ridgeSupport784_suffix_023 ridgeSupport784_022_decode ridgeSupport784_suffix_decode_023
theorem ridgeSupport784_suffix_decode_021 : PackedRawNatGrowth.readList 14 47 ridgeSupport784_rest_021 =
    (ridgeSupport784_suffix_021, ridgeSupport784_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 15
    ridgeSupport784_rest_021 ridgeSupport784_rest_022 ridgeSupport784_rest_023
    ridgeSupport784_021 ridgeSupport784_suffix_022 ridgeSupport784_021_decode ridgeSupport784_suffix_decode_022
theorem ridgeSupport784_suffix_decode_020 : PackedRawNatGrowth.readList 14 79 ridgeSupport784_rest_020 =
    (ridgeSupport784_suffix_020, ridgeSupport784_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 47
    ridgeSupport784_rest_020 ridgeSupport784_rest_021 ridgeSupport784_rest_023
    ridgeSupport784_020 ridgeSupport784_suffix_021 ridgeSupport784_020_decode ridgeSupport784_suffix_decode_021
theorem ridgeSupport784_suffix_decode_019 : PackedRawNatGrowth.readList 14 111 ridgeSupport784_rest_019 =
    (ridgeSupport784_suffix_019, ridgeSupport784_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 79
    ridgeSupport784_rest_019 ridgeSupport784_rest_020 ridgeSupport784_rest_023
    ridgeSupport784_019 ridgeSupport784_suffix_020 ridgeSupport784_019_decode ridgeSupport784_suffix_decode_020
theorem ridgeSupport784_suffix_decode_018 : PackedRawNatGrowth.readList 14 143 ridgeSupport784_rest_018 =
    (ridgeSupport784_suffix_018, ridgeSupport784_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 111
    ridgeSupport784_rest_018 ridgeSupport784_rest_019 ridgeSupport784_rest_023
    ridgeSupport784_018 ridgeSupport784_suffix_019 ridgeSupport784_018_decode ridgeSupport784_suffix_decode_019
theorem ridgeSupport784_suffix_decode_017 : PackedRawNatGrowth.readList 14 175 ridgeSupport784_rest_017 =
    (ridgeSupport784_suffix_017, ridgeSupport784_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 143
    ridgeSupport784_rest_017 ridgeSupport784_rest_018 ridgeSupport784_rest_023
    ridgeSupport784_017 ridgeSupport784_suffix_018 ridgeSupport784_017_decode ridgeSupport784_suffix_decode_018
theorem ridgeSupport784_suffix_decode_016 : PackedRawNatGrowth.readList 14 207 ridgeSupport784_rest_016 =
    (ridgeSupport784_suffix_016, ridgeSupport784_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 175
    ridgeSupport784_rest_016 ridgeSupport784_rest_017 ridgeSupport784_rest_023
    ridgeSupport784_016 ridgeSupport784_suffix_017 ridgeSupport784_016_decode ridgeSupport784_suffix_decode_017
theorem ridgeSupport784_suffix_decode_015 : PackedRawNatGrowth.readList 14 239 ridgeSupport784_rest_015 =
    (ridgeSupport784_suffix_015, ridgeSupport784_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 207
    ridgeSupport784_rest_015 ridgeSupport784_rest_016 ridgeSupport784_rest_023
    ridgeSupport784_015 ridgeSupport784_suffix_016 ridgeSupport784_015_decode ridgeSupport784_suffix_decode_016
theorem ridgeSupport784_suffix_decode_014 : PackedRawNatGrowth.readList 14 271 ridgeSupport784_rest_014 =
    (ridgeSupport784_suffix_014, ridgeSupport784_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 239
    ridgeSupport784_rest_014 ridgeSupport784_rest_015 ridgeSupport784_rest_023
    ridgeSupport784_014 ridgeSupport784_suffix_015 ridgeSupport784_014_decode ridgeSupport784_suffix_decode_015
theorem ridgeSupport784_suffix_decode_013 : PackedRawNatGrowth.readList 14 303 ridgeSupport784_rest_013 =
    (ridgeSupport784_suffix_013, ridgeSupport784_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 271
    ridgeSupport784_rest_013 ridgeSupport784_rest_014 ridgeSupport784_rest_023
    ridgeSupport784_013 ridgeSupport784_suffix_014 ridgeSupport784_013_decode ridgeSupport784_suffix_decode_014
theorem ridgeSupport784_suffix_decode_012 : PackedRawNatGrowth.readList 14 335 ridgeSupport784_rest_012 =
    (ridgeSupport784_suffix_012, ridgeSupport784_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 303
    ridgeSupport784_rest_012 ridgeSupport784_rest_013 ridgeSupport784_rest_023
    ridgeSupport784_012 ridgeSupport784_suffix_013 ridgeSupport784_012_decode ridgeSupport784_suffix_decode_013
theorem ridgeSupport784_suffix_decode_011 : PackedRawNatGrowth.readList 14 367 ridgeSupport784_rest_011 =
    (ridgeSupport784_suffix_011, ridgeSupport784_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 335
    ridgeSupport784_rest_011 ridgeSupport784_rest_012 ridgeSupport784_rest_023
    ridgeSupport784_011 ridgeSupport784_suffix_012 ridgeSupport784_011_decode ridgeSupport784_suffix_decode_012
theorem ridgeSupport784_suffix_decode_010 : PackedRawNatGrowth.readList 14 399 ridgeSupport784_rest_010 =
    (ridgeSupport784_suffix_010, ridgeSupport784_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 367
    ridgeSupport784_rest_010 ridgeSupport784_rest_011 ridgeSupport784_rest_023
    ridgeSupport784_010 ridgeSupport784_suffix_011 ridgeSupport784_010_decode ridgeSupport784_suffix_decode_011
theorem ridgeSupport784_suffix_decode_009 : PackedRawNatGrowth.readList 14 431 ridgeSupport784_rest_009 =
    (ridgeSupport784_suffix_009, ridgeSupport784_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 399
    ridgeSupport784_rest_009 ridgeSupport784_rest_010 ridgeSupport784_rest_023
    ridgeSupport784_009 ridgeSupport784_suffix_010 ridgeSupport784_009_decode ridgeSupport784_suffix_decode_010
theorem ridgeSupport784_suffix_decode_008 : PackedRawNatGrowth.readList 14 463 ridgeSupport784_rest_008 =
    (ridgeSupport784_suffix_008, ridgeSupport784_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 431
    ridgeSupport784_rest_008 ridgeSupport784_rest_009 ridgeSupport784_rest_023
    ridgeSupport784_008 ridgeSupport784_suffix_009 ridgeSupport784_008_decode ridgeSupport784_suffix_decode_009
theorem ridgeSupport784_suffix_decode_007 : PackedRawNatGrowth.readList 14 495 ridgeSupport784_rest_007 =
    (ridgeSupport784_suffix_007, ridgeSupport784_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 463
    ridgeSupport784_rest_007 ridgeSupport784_rest_008 ridgeSupport784_rest_023
    ridgeSupport784_007 ridgeSupport784_suffix_008 ridgeSupport784_007_decode ridgeSupport784_suffix_decode_008
theorem ridgeSupport784_suffix_decode_006 : PackedRawNatGrowth.readList 14 527 ridgeSupport784_rest_006 =
    (ridgeSupport784_suffix_006, ridgeSupport784_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 495
    ridgeSupport784_rest_006 ridgeSupport784_rest_007 ridgeSupport784_rest_023
    ridgeSupport784_006 ridgeSupport784_suffix_007 ridgeSupport784_006_decode ridgeSupport784_suffix_decode_007
theorem ridgeSupport784_suffix_decode_005 : PackedRawNatGrowth.readList 14 559 ridgeSupport784_rest_005 =
    (ridgeSupport784_suffix_005, ridgeSupport784_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 527
    ridgeSupport784_rest_005 ridgeSupport784_rest_006 ridgeSupport784_rest_023
    ridgeSupport784_005 ridgeSupport784_suffix_006 ridgeSupport784_005_decode ridgeSupport784_suffix_decode_006
theorem ridgeSupport784_suffix_decode_004 : PackedRawNatGrowth.readList 14 591 ridgeSupport784_rest_004 =
    (ridgeSupport784_suffix_004, ridgeSupport784_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 559
    ridgeSupport784_rest_004 ridgeSupport784_rest_005 ridgeSupport784_rest_023
    ridgeSupport784_004 ridgeSupport784_suffix_005 ridgeSupport784_004_decode ridgeSupport784_suffix_decode_005
theorem ridgeSupport784_suffix_decode_003 : PackedRawNatGrowth.readList 14 623 ridgeSupport784_rest_003 =
    (ridgeSupport784_suffix_003, ridgeSupport784_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 591
    ridgeSupport784_rest_003 ridgeSupport784_rest_004 ridgeSupport784_rest_023
    ridgeSupport784_003 ridgeSupport784_suffix_004 ridgeSupport784_003_decode ridgeSupport784_suffix_decode_004
theorem ridgeSupport784_suffix_decode_002 : PackedRawNatGrowth.readList 14 655 ridgeSupport784_rest_002 =
    (ridgeSupport784_suffix_002, ridgeSupport784_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 623
    ridgeSupport784_rest_002 ridgeSupport784_rest_003 ridgeSupport784_rest_023
    ridgeSupport784_002 ridgeSupport784_suffix_003 ridgeSupport784_002_decode ridgeSupport784_suffix_decode_003
theorem ridgeSupport784_suffix_decode_001 : PackedRawNatGrowth.readList 14 687 ridgeSupport784_rest_001 =
    (ridgeSupport784_suffix_001, ridgeSupport784_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 655
    ridgeSupport784_rest_001 ridgeSupport784_rest_002 ridgeSupport784_rest_023
    ridgeSupport784_001 ridgeSupport784_suffix_002 ridgeSupport784_001_decode ridgeSupport784_suffix_decode_002
theorem ridgeSupport784_suffix_decode_000 : PackedRawNatGrowth.readList 14 719 ridgeSupport784_rest_000 =
    (ridgeSupport784_suffix_000, ridgeSupport784_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 687
    ridgeSupport784_rest_000 ridgeSupport784_rest_001 ridgeSupport784_rest_023
    ridgeSupport784_000 ridgeSupport784_suffix_001 ridgeSupport784_000_decode ridgeSupport784_suffix_decode_001
theorem ridgeSupport784_eq : candidateRows 784 = ridgeSupport784_suffix_000 := by
  rw [ridgeSupport784_source]
  exact congrArg Prod.fst ridgeSupport784_suffix_decode_000
theorem ridgeTest_large_784 : ridgeTest 784 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport784_eq]
    simp only [ridgeSupport784_suffix_000, ridgeSupport784_suffix_001, ridgeSupport784_suffix_002, ridgeSupport784_suffix_003, ridgeSupport784_suffix_004, ridgeSupport784_suffix_005, ridgeSupport784_suffix_006, ridgeSupport784_suffix_007, ridgeSupport784_suffix_008, ridgeSupport784_suffix_009, ridgeSupport784_suffix_010, ridgeSupport784_suffix_011, ridgeSupport784_suffix_012, ridgeSupport784_suffix_013, ridgeSupport784_suffix_014, ridgeSupport784_suffix_015, ridgeSupport784_suffix_016, ridgeSupport784_suffix_017, ridgeSupport784_suffix_018, ridgeSupport784_suffix_019, ridgeSupport784_suffix_020, ridgeSupport784_suffix_021, ridgeSupport784_suffix_022, ridgeSupport784_suffix_023, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport784_000_mask, ridgeSupport784_001_mask, ridgeSupport784_002_mask, ridgeSupport784_003_mask, ridgeSupport784_004_mask, ridgeSupport784_005_mask, ridgeSupport784_006_mask, ridgeSupport784_007_mask, ridgeSupport784_008_mask, ridgeSupport784_009_mask, ridgeSupport784_010_mask, ridgeSupport784_011_mask, ridgeSupport784_012_mask, ridgeSupport784_013_mask, ridgeSupport784_014_mask, ridgeSupport784_015_mask, ridgeSupport784_016_mask, ridgeSupport784_017_mask, ridgeSupport784_018_mask, ridgeSupport784_019_mask, ridgeSupport784_020_mask, ridgeSupport784_021_mask, ridgeSupport784_022_mask]
    decide +kernel
  · rw [ridgeSupport784_eq]
    simp only [ridgeSupport784_suffix_000, ridgeSupport784_suffix_001, ridgeSupport784_suffix_002, ridgeSupport784_suffix_003, ridgeSupport784_suffix_004, ridgeSupport784_suffix_005, ridgeSupport784_suffix_006, ridgeSupport784_suffix_007, ridgeSupport784_suffix_008, ridgeSupport784_suffix_009, ridgeSupport784_suffix_010, ridgeSupport784_suffix_011, ridgeSupport784_suffix_012, ridgeSupport784_suffix_013, ridgeSupport784_suffix_014, ridgeSupport784_suffix_015, ridgeSupport784_suffix_016, ridgeSupport784_suffix_017, ridgeSupport784_suffix_018, ridgeSupport784_suffix_019, ridgeSupport784_suffix_020, ridgeSupport784_suffix_021, ridgeSupport784_suffix_022, ridgeSupport784_suffix_023, List.all_append, List.all_nil, ridgeSupport784_000_checked, ridgeSupport784_001_checked, ridgeSupport784_002_checked, ridgeSupport784_003_checked, ridgeSupport784_004_checked, ridgeSupport784_005_checked, ridgeSupport784_006_checked, ridgeSupport784_007_checked, ridgeSupport784_008_checked, ridgeSupport784_009_checked, ridgeSupport784_010_checked, ridgeSupport784_011_checked, ridgeSupport784_012_checked, ridgeSupport784_013_checked, ridgeSupport784_014_checked, ridgeSupport784_015_checked, ridgeSupport784_016_checked, ridgeSupport784_017_checked, ridgeSupport784_018_checked, ridgeSupport784_019_checked, ridgeSupport784_020_checked, ridgeSupport784_021_checked, ridgeSupport784_022_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase01
