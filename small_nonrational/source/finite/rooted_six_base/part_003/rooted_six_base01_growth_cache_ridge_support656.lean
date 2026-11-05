module
prelude
public import RootedSixBase01GrowthCacheRidgeSupport656Part000
public import RootedSixBase01GrowthCacheRidgeSupport656Part001
public import RootedSixBase01GrowthCacheRidgeSupport656Part002
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport656_suffix_decode_023 : PackedRawNatGrowth.readList 14 0 ridgeSupport656_rest_023 =
    (ridgeSupport656_suffix_023, ridgeSupport656_rest_023) := by rfl
theorem ridgeSupport656_suffix_decode_022 : PackedRawNatGrowth.readList 14 15 ridgeSupport656_rest_022 =
    (ridgeSupport656_suffix_022, ridgeSupport656_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 15 0
    ridgeSupport656_rest_022 ridgeSupport656_rest_023 ridgeSupport656_rest_023
    ridgeSupport656_022 ridgeSupport656_suffix_023 ridgeSupport656_022_decode ridgeSupport656_suffix_decode_023
theorem ridgeSupport656_suffix_decode_021 : PackedRawNatGrowth.readList 14 47 ridgeSupport656_rest_021 =
    (ridgeSupport656_suffix_021, ridgeSupport656_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 15
    ridgeSupport656_rest_021 ridgeSupport656_rest_022 ridgeSupport656_rest_023
    ridgeSupport656_021 ridgeSupport656_suffix_022 ridgeSupport656_021_decode ridgeSupport656_suffix_decode_022
theorem ridgeSupport656_suffix_decode_020 : PackedRawNatGrowth.readList 14 79 ridgeSupport656_rest_020 =
    (ridgeSupport656_suffix_020, ridgeSupport656_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 47
    ridgeSupport656_rest_020 ridgeSupport656_rest_021 ridgeSupport656_rest_023
    ridgeSupport656_020 ridgeSupport656_suffix_021 ridgeSupport656_020_decode ridgeSupport656_suffix_decode_021
theorem ridgeSupport656_suffix_decode_019 : PackedRawNatGrowth.readList 14 111 ridgeSupport656_rest_019 =
    (ridgeSupport656_suffix_019, ridgeSupport656_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 79
    ridgeSupport656_rest_019 ridgeSupport656_rest_020 ridgeSupport656_rest_023
    ridgeSupport656_019 ridgeSupport656_suffix_020 ridgeSupport656_019_decode ridgeSupport656_suffix_decode_020
theorem ridgeSupport656_suffix_decode_018 : PackedRawNatGrowth.readList 14 143 ridgeSupport656_rest_018 =
    (ridgeSupport656_suffix_018, ridgeSupport656_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 111
    ridgeSupport656_rest_018 ridgeSupport656_rest_019 ridgeSupport656_rest_023
    ridgeSupport656_018 ridgeSupport656_suffix_019 ridgeSupport656_018_decode ridgeSupport656_suffix_decode_019
theorem ridgeSupport656_suffix_decode_017 : PackedRawNatGrowth.readList 14 175 ridgeSupport656_rest_017 =
    (ridgeSupport656_suffix_017, ridgeSupport656_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 143
    ridgeSupport656_rest_017 ridgeSupport656_rest_018 ridgeSupport656_rest_023
    ridgeSupport656_017 ridgeSupport656_suffix_018 ridgeSupport656_017_decode ridgeSupport656_suffix_decode_018
theorem ridgeSupport656_suffix_decode_016 : PackedRawNatGrowth.readList 14 207 ridgeSupport656_rest_016 =
    (ridgeSupport656_suffix_016, ridgeSupport656_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 175
    ridgeSupport656_rest_016 ridgeSupport656_rest_017 ridgeSupport656_rest_023
    ridgeSupport656_016 ridgeSupport656_suffix_017 ridgeSupport656_016_decode ridgeSupport656_suffix_decode_017
theorem ridgeSupport656_suffix_decode_015 : PackedRawNatGrowth.readList 14 239 ridgeSupport656_rest_015 =
    (ridgeSupport656_suffix_015, ridgeSupport656_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 207
    ridgeSupport656_rest_015 ridgeSupport656_rest_016 ridgeSupport656_rest_023
    ridgeSupport656_015 ridgeSupport656_suffix_016 ridgeSupport656_015_decode ridgeSupport656_suffix_decode_016
theorem ridgeSupport656_suffix_decode_014 : PackedRawNatGrowth.readList 14 271 ridgeSupport656_rest_014 =
    (ridgeSupport656_suffix_014, ridgeSupport656_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 239
    ridgeSupport656_rest_014 ridgeSupport656_rest_015 ridgeSupport656_rest_023
    ridgeSupport656_014 ridgeSupport656_suffix_015 ridgeSupport656_014_decode ridgeSupport656_suffix_decode_015
theorem ridgeSupport656_suffix_decode_013 : PackedRawNatGrowth.readList 14 303 ridgeSupport656_rest_013 =
    (ridgeSupport656_suffix_013, ridgeSupport656_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 271
    ridgeSupport656_rest_013 ridgeSupport656_rest_014 ridgeSupport656_rest_023
    ridgeSupport656_013 ridgeSupport656_suffix_014 ridgeSupport656_013_decode ridgeSupport656_suffix_decode_014
theorem ridgeSupport656_suffix_decode_012 : PackedRawNatGrowth.readList 14 335 ridgeSupport656_rest_012 =
    (ridgeSupport656_suffix_012, ridgeSupport656_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 303
    ridgeSupport656_rest_012 ridgeSupport656_rest_013 ridgeSupport656_rest_023
    ridgeSupport656_012 ridgeSupport656_suffix_013 ridgeSupport656_012_decode ridgeSupport656_suffix_decode_013
theorem ridgeSupport656_suffix_decode_011 : PackedRawNatGrowth.readList 14 367 ridgeSupport656_rest_011 =
    (ridgeSupport656_suffix_011, ridgeSupport656_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 335
    ridgeSupport656_rest_011 ridgeSupport656_rest_012 ridgeSupport656_rest_023
    ridgeSupport656_011 ridgeSupport656_suffix_012 ridgeSupport656_011_decode ridgeSupport656_suffix_decode_012
theorem ridgeSupport656_suffix_decode_010 : PackedRawNatGrowth.readList 14 399 ridgeSupport656_rest_010 =
    (ridgeSupport656_suffix_010, ridgeSupport656_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 367
    ridgeSupport656_rest_010 ridgeSupport656_rest_011 ridgeSupport656_rest_023
    ridgeSupport656_010 ridgeSupport656_suffix_011 ridgeSupport656_010_decode ridgeSupport656_suffix_decode_011
theorem ridgeSupport656_suffix_decode_009 : PackedRawNatGrowth.readList 14 431 ridgeSupport656_rest_009 =
    (ridgeSupport656_suffix_009, ridgeSupport656_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 399
    ridgeSupport656_rest_009 ridgeSupport656_rest_010 ridgeSupport656_rest_023
    ridgeSupport656_009 ridgeSupport656_suffix_010 ridgeSupport656_009_decode ridgeSupport656_suffix_decode_010
theorem ridgeSupport656_suffix_decode_008 : PackedRawNatGrowth.readList 14 463 ridgeSupport656_rest_008 =
    (ridgeSupport656_suffix_008, ridgeSupport656_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 431
    ridgeSupport656_rest_008 ridgeSupport656_rest_009 ridgeSupport656_rest_023
    ridgeSupport656_008 ridgeSupport656_suffix_009 ridgeSupport656_008_decode ridgeSupport656_suffix_decode_009
theorem ridgeSupport656_suffix_decode_007 : PackedRawNatGrowth.readList 14 495 ridgeSupport656_rest_007 =
    (ridgeSupport656_suffix_007, ridgeSupport656_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 463
    ridgeSupport656_rest_007 ridgeSupport656_rest_008 ridgeSupport656_rest_023
    ridgeSupport656_007 ridgeSupport656_suffix_008 ridgeSupport656_007_decode ridgeSupport656_suffix_decode_008
theorem ridgeSupport656_suffix_decode_006 : PackedRawNatGrowth.readList 14 527 ridgeSupport656_rest_006 =
    (ridgeSupport656_suffix_006, ridgeSupport656_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 495
    ridgeSupport656_rest_006 ridgeSupport656_rest_007 ridgeSupport656_rest_023
    ridgeSupport656_006 ridgeSupport656_suffix_007 ridgeSupport656_006_decode ridgeSupport656_suffix_decode_007
theorem ridgeSupport656_suffix_decode_005 : PackedRawNatGrowth.readList 14 559 ridgeSupport656_rest_005 =
    (ridgeSupport656_suffix_005, ridgeSupport656_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 527
    ridgeSupport656_rest_005 ridgeSupport656_rest_006 ridgeSupport656_rest_023
    ridgeSupport656_005 ridgeSupport656_suffix_006 ridgeSupport656_005_decode ridgeSupport656_suffix_decode_006
theorem ridgeSupport656_suffix_decode_004 : PackedRawNatGrowth.readList 14 591 ridgeSupport656_rest_004 =
    (ridgeSupport656_suffix_004, ridgeSupport656_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 559
    ridgeSupport656_rest_004 ridgeSupport656_rest_005 ridgeSupport656_rest_023
    ridgeSupport656_004 ridgeSupport656_suffix_005 ridgeSupport656_004_decode ridgeSupport656_suffix_decode_005
theorem ridgeSupport656_suffix_decode_003 : PackedRawNatGrowth.readList 14 623 ridgeSupport656_rest_003 =
    (ridgeSupport656_suffix_003, ridgeSupport656_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 591
    ridgeSupport656_rest_003 ridgeSupport656_rest_004 ridgeSupport656_rest_023
    ridgeSupport656_003 ridgeSupport656_suffix_004 ridgeSupport656_003_decode ridgeSupport656_suffix_decode_004
theorem ridgeSupport656_suffix_decode_002 : PackedRawNatGrowth.readList 14 655 ridgeSupport656_rest_002 =
    (ridgeSupport656_suffix_002, ridgeSupport656_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 623
    ridgeSupport656_rest_002 ridgeSupport656_rest_003 ridgeSupport656_rest_023
    ridgeSupport656_002 ridgeSupport656_suffix_003 ridgeSupport656_002_decode ridgeSupport656_suffix_decode_003
theorem ridgeSupport656_suffix_decode_001 : PackedRawNatGrowth.readList 14 687 ridgeSupport656_rest_001 =
    (ridgeSupport656_suffix_001, ridgeSupport656_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 655
    ridgeSupport656_rest_001 ridgeSupport656_rest_002 ridgeSupport656_rest_023
    ridgeSupport656_001 ridgeSupport656_suffix_002 ridgeSupport656_001_decode ridgeSupport656_suffix_decode_002
theorem ridgeSupport656_suffix_decode_000 : PackedRawNatGrowth.readList 14 719 ridgeSupport656_rest_000 =
    (ridgeSupport656_suffix_000, ridgeSupport656_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 687
    ridgeSupport656_rest_000 ridgeSupport656_rest_001 ridgeSupport656_rest_023
    ridgeSupport656_000 ridgeSupport656_suffix_001 ridgeSupport656_000_decode ridgeSupport656_suffix_decode_001
theorem ridgeSupport656_eq : candidateRows 656 = ridgeSupport656_suffix_000 := by
  rw [ridgeSupport656_source]
  exact congrArg Prod.fst ridgeSupport656_suffix_decode_000
theorem ridgeTest_large_656 : ridgeTest 656 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport656_eq]
    simp only [ridgeSupport656_suffix_000, ridgeSupport656_suffix_001, ridgeSupport656_suffix_002, ridgeSupport656_suffix_003, ridgeSupport656_suffix_004, ridgeSupport656_suffix_005, ridgeSupport656_suffix_006, ridgeSupport656_suffix_007, ridgeSupport656_suffix_008, ridgeSupport656_suffix_009, ridgeSupport656_suffix_010, ridgeSupport656_suffix_011, ridgeSupport656_suffix_012, ridgeSupport656_suffix_013, ridgeSupport656_suffix_014, ridgeSupport656_suffix_015, ridgeSupport656_suffix_016, ridgeSupport656_suffix_017, ridgeSupport656_suffix_018, ridgeSupport656_suffix_019, ridgeSupport656_suffix_020, ridgeSupport656_suffix_021, ridgeSupport656_suffix_022, ridgeSupport656_suffix_023, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport656_000_mask, ridgeSupport656_001_mask, ridgeSupport656_002_mask, ridgeSupport656_003_mask, ridgeSupport656_004_mask, ridgeSupport656_005_mask, ridgeSupport656_006_mask, ridgeSupport656_007_mask, ridgeSupport656_008_mask, ridgeSupport656_009_mask, ridgeSupport656_010_mask, ridgeSupport656_011_mask, ridgeSupport656_012_mask, ridgeSupport656_013_mask, ridgeSupport656_014_mask, ridgeSupport656_015_mask, ridgeSupport656_016_mask, ridgeSupport656_017_mask, ridgeSupport656_018_mask, ridgeSupport656_019_mask, ridgeSupport656_020_mask, ridgeSupport656_021_mask, ridgeSupport656_022_mask]
    decide +kernel
  · rw [ridgeSupport656_eq]
    simp only [ridgeSupport656_suffix_000, ridgeSupport656_suffix_001, ridgeSupport656_suffix_002, ridgeSupport656_suffix_003, ridgeSupport656_suffix_004, ridgeSupport656_suffix_005, ridgeSupport656_suffix_006, ridgeSupport656_suffix_007, ridgeSupport656_suffix_008, ridgeSupport656_suffix_009, ridgeSupport656_suffix_010, ridgeSupport656_suffix_011, ridgeSupport656_suffix_012, ridgeSupport656_suffix_013, ridgeSupport656_suffix_014, ridgeSupport656_suffix_015, ridgeSupport656_suffix_016, ridgeSupport656_suffix_017, ridgeSupport656_suffix_018, ridgeSupport656_suffix_019, ridgeSupport656_suffix_020, ridgeSupport656_suffix_021, ridgeSupport656_suffix_022, ridgeSupport656_suffix_023, List.all_append, List.all_nil, ridgeSupport656_000_checked, ridgeSupport656_001_checked, ridgeSupport656_002_checked, ridgeSupport656_003_checked, ridgeSupport656_004_checked, ridgeSupport656_005_checked, ridgeSupport656_006_checked, ridgeSupport656_007_checked, ridgeSupport656_008_checked, ridgeSupport656_009_checked, ridgeSupport656_010_checked, ridgeSupport656_011_checked, ridgeSupport656_012_checked, ridgeSupport656_013_checked, ridgeSupport656_014_checked, ridgeSupport656_015_checked, ridgeSupport656_016_checked, ridgeSupport656_017_checked, ridgeSupport656_018_checked, ridgeSupport656_019_checked, ridgeSupport656_020_checked, ridgeSupport656_021_checked, ridgeSupport656_022_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase01
