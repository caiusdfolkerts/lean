module
prelude
public import RootedSixBase01GrowthCacheRidgeSupport224Part000
public import RootedSixBase01GrowthCacheRidgeSupport224Part001
public import RootedSixBase01GrowthCacheRidgeSupport224Part002
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport224_suffix_decode_023 : PackedRawNatGrowth.readList 14 0 ridgeSupport224_rest_023 =
    (ridgeSupport224_suffix_023, ridgeSupport224_rest_023) := by rfl
theorem ridgeSupport224_suffix_decode_022 : PackedRawNatGrowth.readList 14 15 ridgeSupport224_rest_022 =
    (ridgeSupport224_suffix_022, ridgeSupport224_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 15 0
    ridgeSupport224_rest_022 ridgeSupport224_rest_023 ridgeSupport224_rest_023
    ridgeSupport224_022 ridgeSupport224_suffix_023 ridgeSupport224_022_decode ridgeSupport224_suffix_decode_023
theorem ridgeSupport224_suffix_decode_021 : PackedRawNatGrowth.readList 14 47 ridgeSupport224_rest_021 =
    (ridgeSupport224_suffix_021, ridgeSupport224_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 15
    ridgeSupport224_rest_021 ridgeSupport224_rest_022 ridgeSupport224_rest_023
    ridgeSupport224_021 ridgeSupport224_suffix_022 ridgeSupport224_021_decode ridgeSupport224_suffix_decode_022
theorem ridgeSupport224_suffix_decode_020 : PackedRawNatGrowth.readList 14 79 ridgeSupport224_rest_020 =
    (ridgeSupport224_suffix_020, ridgeSupport224_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 47
    ridgeSupport224_rest_020 ridgeSupport224_rest_021 ridgeSupport224_rest_023
    ridgeSupport224_020 ridgeSupport224_suffix_021 ridgeSupport224_020_decode ridgeSupport224_suffix_decode_021
theorem ridgeSupport224_suffix_decode_019 : PackedRawNatGrowth.readList 14 111 ridgeSupport224_rest_019 =
    (ridgeSupport224_suffix_019, ridgeSupport224_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 79
    ridgeSupport224_rest_019 ridgeSupport224_rest_020 ridgeSupport224_rest_023
    ridgeSupport224_019 ridgeSupport224_suffix_020 ridgeSupport224_019_decode ridgeSupport224_suffix_decode_020
theorem ridgeSupport224_suffix_decode_018 : PackedRawNatGrowth.readList 14 143 ridgeSupport224_rest_018 =
    (ridgeSupport224_suffix_018, ridgeSupport224_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 111
    ridgeSupport224_rest_018 ridgeSupport224_rest_019 ridgeSupport224_rest_023
    ridgeSupport224_018 ridgeSupport224_suffix_019 ridgeSupport224_018_decode ridgeSupport224_suffix_decode_019
theorem ridgeSupport224_suffix_decode_017 : PackedRawNatGrowth.readList 14 175 ridgeSupport224_rest_017 =
    (ridgeSupport224_suffix_017, ridgeSupport224_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 143
    ridgeSupport224_rest_017 ridgeSupport224_rest_018 ridgeSupport224_rest_023
    ridgeSupport224_017 ridgeSupport224_suffix_018 ridgeSupport224_017_decode ridgeSupport224_suffix_decode_018
theorem ridgeSupport224_suffix_decode_016 : PackedRawNatGrowth.readList 14 207 ridgeSupport224_rest_016 =
    (ridgeSupport224_suffix_016, ridgeSupport224_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 175
    ridgeSupport224_rest_016 ridgeSupport224_rest_017 ridgeSupport224_rest_023
    ridgeSupport224_016 ridgeSupport224_suffix_017 ridgeSupport224_016_decode ridgeSupport224_suffix_decode_017
theorem ridgeSupport224_suffix_decode_015 : PackedRawNatGrowth.readList 14 239 ridgeSupport224_rest_015 =
    (ridgeSupport224_suffix_015, ridgeSupport224_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 207
    ridgeSupport224_rest_015 ridgeSupport224_rest_016 ridgeSupport224_rest_023
    ridgeSupport224_015 ridgeSupport224_suffix_016 ridgeSupport224_015_decode ridgeSupport224_suffix_decode_016
theorem ridgeSupport224_suffix_decode_014 : PackedRawNatGrowth.readList 14 271 ridgeSupport224_rest_014 =
    (ridgeSupport224_suffix_014, ridgeSupport224_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 239
    ridgeSupport224_rest_014 ridgeSupport224_rest_015 ridgeSupport224_rest_023
    ridgeSupport224_014 ridgeSupport224_suffix_015 ridgeSupport224_014_decode ridgeSupport224_suffix_decode_015
theorem ridgeSupport224_suffix_decode_013 : PackedRawNatGrowth.readList 14 303 ridgeSupport224_rest_013 =
    (ridgeSupport224_suffix_013, ridgeSupport224_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 271
    ridgeSupport224_rest_013 ridgeSupport224_rest_014 ridgeSupport224_rest_023
    ridgeSupport224_013 ridgeSupport224_suffix_014 ridgeSupport224_013_decode ridgeSupport224_suffix_decode_014
theorem ridgeSupport224_suffix_decode_012 : PackedRawNatGrowth.readList 14 335 ridgeSupport224_rest_012 =
    (ridgeSupport224_suffix_012, ridgeSupport224_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 303
    ridgeSupport224_rest_012 ridgeSupport224_rest_013 ridgeSupport224_rest_023
    ridgeSupport224_012 ridgeSupport224_suffix_013 ridgeSupport224_012_decode ridgeSupport224_suffix_decode_013
theorem ridgeSupport224_suffix_decode_011 : PackedRawNatGrowth.readList 14 367 ridgeSupport224_rest_011 =
    (ridgeSupport224_suffix_011, ridgeSupport224_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 335
    ridgeSupport224_rest_011 ridgeSupport224_rest_012 ridgeSupport224_rest_023
    ridgeSupport224_011 ridgeSupport224_suffix_012 ridgeSupport224_011_decode ridgeSupport224_suffix_decode_012
theorem ridgeSupport224_suffix_decode_010 : PackedRawNatGrowth.readList 14 399 ridgeSupport224_rest_010 =
    (ridgeSupport224_suffix_010, ridgeSupport224_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 367
    ridgeSupport224_rest_010 ridgeSupport224_rest_011 ridgeSupport224_rest_023
    ridgeSupport224_010 ridgeSupport224_suffix_011 ridgeSupport224_010_decode ridgeSupport224_suffix_decode_011
theorem ridgeSupport224_suffix_decode_009 : PackedRawNatGrowth.readList 14 431 ridgeSupport224_rest_009 =
    (ridgeSupport224_suffix_009, ridgeSupport224_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 399
    ridgeSupport224_rest_009 ridgeSupport224_rest_010 ridgeSupport224_rest_023
    ridgeSupport224_009 ridgeSupport224_suffix_010 ridgeSupport224_009_decode ridgeSupport224_suffix_decode_010
theorem ridgeSupport224_suffix_decode_008 : PackedRawNatGrowth.readList 14 463 ridgeSupport224_rest_008 =
    (ridgeSupport224_suffix_008, ridgeSupport224_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 431
    ridgeSupport224_rest_008 ridgeSupport224_rest_009 ridgeSupport224_rest_023
    ridgeSupport224_008 ridgeSupport224_suffix_009 ridgeSupport224_008_decode ridgeSupport224_suffix_decode_009
theorem ridgeSupport224_suffix_decode_007 : PackedRawNatGrowth.readList 14 495 ridgeSupport224_rest_007 =
    (ridgeSupport224_suffix_007, ridgeSupport224_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 463
    ridgeSupport224_rest_007 ridgeSupport224_rest_008 ridgeSupport224_rest_023
    ridgeSupport224_007 ridgeSupport224_suffix_008 ridgeSupport224_007_decode ridgeSupport224_suffix_decode_008
theorem ridgeSupport224_suffix_decode_006 : PackedRawNatGrowth.readList 14 527 ridgeSupport224_rest_006 =
    (ridgeSupport224_suffix_006, ridgeSupport224_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 495
    ridgeSupport224_rest_006 ridgeSupport224_rest_007 ridgeSupport224_rest_023
    ridgeSupport224_006 ridgeSupport224_suffix_007 ridgeSupport224_006_decode ridgeSupport224_suffix_decode_007
theorem ridgeSupport224_suffix_decode_005 : PackedRawNatGrowth.readList 14 559 ridgeSupport224_rest_005 =
    (ridgeSupport224_suffix_005, ridgeSupport224_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 527
    ridgeSupport224_rest_005 ridgeSupport224_rest_006 ridgeSupport224_rest_023
    ridgeSupport224_005 ridgeSupport224_suffix_006 ridgeSupport224_005_decode ridgeSupport224_suffix_decode_006
theorem ridgeSupport224_suffix_decode_004 : PackedRawNatGrowth.readList 14 591 ridgeSupport224_rest_004 =
    (ridgeSupport224_suffix_004, ridgeSupport224_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 559
    ridgeSupport224_rest_004 ridgeSupport224_rest_005 ridgeSupport224_rest_023
    ridgeSupport224_004 ridgeSupport224_suffix_005 ridgeSupport224_004_decode ridgeSupport224_suffix_decode_005
theorem ridgeSupport224_suffix_decode_003 : PackedRawNatGrowth.readList 14 623 ridgeSupport224_rest_003 =
    (ridgeSupport224_suffix_003, ridgeSupport224_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 591
    ridgeSupport224_rest_003 ridgeSupport224_rest_004 ridgeSupport224_rest_023
    ridgeSupport224_003 ridgeSupport224_suffix_004 ridgeSupport224_003_decode ridgeSupport224_suffix_decode_004
theorem ridgeSupport224_suffix_decode_002 : PackedRawNatGrowth.readList 14 655 ridgeSupport224_rest_002 =
    (ridgeSupport224_suffix_002, ridgeSupport224_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 623
    ridgeSupport224_rest_002 ridgeSupport224_rest_003 ridgeSupport224_rest_023
    ridgeSupport224_002 ridgeSupport224_suffix_003 ridgeSupport224_002_decode ridgeSupport224_suffix_decode_003
theorem ridgeSupport224_suffix_decode_001 : PackedRawNatGrowth.readList 14 687 ridgeSupport224_rest_001 =
    (ridgeSupport224_suffix_001, ridgeSupport224_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 655
    ridgeSupport224_rest_001 ridgeSupport224_rest_002 ridgeSupport224_rest_023
    ridgeSupport224_001 ridgeSupport224_suffix_002 ridgeSupport224_001_decode ridgeSupport224_suffix_decode_002
theorem ridgeSupport224_suffix_decode_000 : PackedRawNatGrowth.readList 14 719 ridgeSupport224_rest_000 =
    (ridgeSupport224_suffix_000, ridgeSupport224_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 687
    ridgeSupport224_rest_000 ridgeSupport224_rest_001 ridgeSupport224_rest_023
    ridgeSupport224_000 ridgeSupport224_suffix_001 ridgeSupport224_000_decode ridgeSupport224_suffix_decode_001
theorem ridgeSupport224_eq : candidateRows 224 = ridgeSupport224_suffix_000 := by
  rw [ridgeSupport224_source]
  exact congrArg Prod.fst ridgeSupport224_suffix_decode_000
theorem ridgeTest_large_224 : ridgeTest 224 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport224_eq]
    simp only [ridgeSupport224_suffix_000, ridgeSupport224_suffix_001, ridgeSupport224_suffix_002, ridgeSupport224_suffix_003, ridgeSupport224_suffix_004, ridgeSupport224_suffix_005, ridgeSupport224_suffix_006, ridgeSupport224_suffix_007, ridgeSupport224_suffix_008, ridgeSupport224_suffix_009, ridgeSupport224_suffix_010, ridgeSupport224_suffix_011, ridgeSupport224_suffix_012, ridgeSupport224_suffix_013, ridgeSupport224_suffix_014, ridgeSupport224_suffix_015, ridgeSupport224_suffix_016, ridgeSupport224_suffix_017, ridgeSupport224_suffix_018, ridgeSupport224_suffix_019, ridgeSupport224_suffix_020, ridgeSupport224_suffix_021, ridgeSupport224_suffix_022, ridgeSupport224_suffix_023, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport224_000_mask, ridgeSupport224_001_mask, ridgeSupport224_002_mask, ridgeSupport224_003_mask, ridgeSupport224_004_mask, ridgeSupport224_005_mask, ridgeSupport224_006_mask, ridgeSupport224_007_mask, ridgeSupport224_008_mask, ridgeSupport224_009_mask, ridgeSupport224_010_mask, ridgeSupport224_011_mask, ridgeSupport224_012_mask, ridgeSupport224_013_mask, ridgeSupport224_014_mask, ridgeSupport224_015_mask, ridgeSupport224_016_mask, ridgeSupport224_017_mask, ridgeSupport224_018_mask, ridgeSupport224_019_mask, ridgeSupport224_020_mask, ridgeSupport224_021_mask, ridgeSupport224_022_mask]
    decide +kernel
  · rw [ridgeSupport224_eq]
    simp only [ridgeSupport224_suffix_000, ridgeSupport224_suffix_001, ridgeSupport224_suffix_002, ridgeSupport224_suffix_003, ridgeSupport224_suffix_004, ridgeSupport224_suffix_005, ridgeSupport224_suffix_006, ridgeSupport224_suffix_007, ridgeSupport224_suffix_008, ridgeSupport224_suffix_009, ridgeSupport224_suffix_010, ridgeSupport224_suffix_011, ridgeSupport224_suffix_012, ridgeSupport224_suffix_013, ridgeSupport224_suffix_014, ridgeSupport224_suffix_015, ridgeSupport224_suffix_016, ridgeSupport224_suffix_017, ridgeSupport224_suffix_018, ridgeSupport224_suffix_019, ridgeSupport224_suffix_020, ridgeSupport224_suffix_021, ridgeSupport224_suffix_022, ridgeSupport224_suffix_023, List.all_append, List.all_nil, ridgeSupport224_000_checked, ridgeSupport224_001_checked, ridgeSupport224_002_checked, ridgeSupport224_003_checked, ridgeSupport224_004_checked, ridgeSupport224_005_checked, ridgeSupport224_006_checked, ridgeSupport224_007_checked, ridgeSupport224_008_checked, ridgeSupport224_009_checked, ridgeSupport224_010_checked, ridgeSupport224_011_checked, ridgeSupport224_012_checked, ridgeSupport224_013_checked, ridgeSupport224_014_checked, ridgeSupport224_015_checked, ridgeSupport224_016_checked, ridgeSupport224_017_checked, ridgeSupport224_018_checked, ridgeSupport224_019_checked, ridgeSupport224_020_checked, ridgeSupport224_021_checked, ridgeSupport224_022_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase01
