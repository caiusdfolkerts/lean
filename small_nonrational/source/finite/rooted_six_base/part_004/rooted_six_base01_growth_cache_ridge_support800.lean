module
prelude
public import RootedSixBase01GrowthCacheRidgeSupport800Part000
public import RootedSixBase01GrowthCacheRidgeSupport800Part001
public import RootedSixBase01GrowthCacheRidgeSupport800Part002
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport800_suffix_decode_023 : PackedRawNatGrowth.readList 14 0 ridgeSupport800_rest_023 =
    (ridgeSupport800_suffix_023, ridgeSupport800_rest_023) := by rfl
theorem ridgeSupport800_suffix_decode_022 : PackedRawNatGrowth.readList 14 15 ridgeSupport800_rest_022 =
    (ridgeSupport800_suffix_022, ridgeSupport800_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 15 0
    ridgeSupport800_rest_022 ridgeSupport800_rest_023 ridgeSupport800_rest_023
    ridgeSupport800_022 ridgeSupport800_suffix_023 ridgeSupport800_022_decode ridgeSupport800_suffix_decode_023
theorem ridgeSupport800_suffix_decode_021 : PackedRawNatGrowth.readList 14 47 ridgeSupport800_rest_021 =
    (ridgeSupport800_suffix_021, ridgeSupport800_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 15
    ridgeSupport800_rest_021 ridgeSupport800_rest_022 ridgeSupport800_rest_023
    ridgeSupport800_021 ridgeSupport800_suffix_022 ridgeSupport800_021_decode ridgeSupport800_suffix_decode_022
theorem ridgeSupport800_suffix_decode_020 : PackedRawNatGrowth.readList 14 79 ridgeSupport800_rest_020 =
    (ridgeSupport800_suffix_020, ridgeSupport800_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 47
    ridgeSupport800_rest_020 ridgeSupport800_rest_021 ridgeSupport800_rest_023
    ridgeSupport800_020 ridgeSupport800_suffix_021 ridgeSupport800_020_decode ridgeSupport800_suffix_decode_021
theorem ridgeSupport800_suffix_decode_019 : PackedRawNatGrowth.readList 14 111 ridgeSupport800_rest_019 =
    (ridgeSupport800_suffix_019, ridgeSupport800_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 79
    ridgeSupport800_rest_019 ridgeSupport800_rest_020 ridgeSupport800_rest_023
    ridgeSupport800_019 ridgeSupport800_suffix_020 ridgeSupport800_019_decode ridgeSupport800_suffix_decode_020
theorem ridgeSupport800_suffix_decode_018 : PackedRawNatGrowth.readList 14 143 ridgeSupport800_rest_018 =
    (ridgeSupport800_suffix_018, ridgeSupport800_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 111
    ridgeSupport800_rest_018 ridgeSupport800_rest_019 ridgeSupport800_rest_023
    ridgeSupport800_018 ridgeSupport800_suffix_019 ridgeSupport800_018_decode ridgeSupport800_suffix_decode_019
theorem ridgeSupport800_suffix_decode_017 : PackedRawNatGrowth.readList 14 175 ridgeSupport800_rest_017 =
    (ridgeSupport800_suffix_017, ridgeSupport800_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 143
    ridgeSupport800_rest_017 ridgeSupport800_rest_018 ridgeSupport800_rest_023
    ridgeSupport800_017 ridgeSupport800_suffix_018 ridgeSupport800_017_decode ridgeSupport800_suffix_decode_018
theorem ridgeSupport800_suffix_decode_016 : PackedRawNatGrowth.readList 14 207 ridgeSupport800_rest_016 =
    (ridgeSupport800_suffix_016, ridgeSupport800_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 175
    ridgeSupport800_rest_016 ridgeSupport800_rest_017 ridgeSupport800_rest_023
    ridgeSupport800_016 ridgeSupport800_suffix_017 ridgeSupport800_016_decode ridgeSupport800_suffix_decode_017
theorem ridgeSupport800_suffix_decode_015 : PackedRawNatGrowth.readList 14 239 ridgeSupport800_rest_015 =
    (ridgeSupport800_suffix_015, ridgeSupport800_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 207
    ridgeSupport800_rest_015 ridgeSupport800_rest_016 ridgeSupport800_rest_023
    ridgeSupport800_015 ridgeSupport800_suffix_016 ridgeSupport800_015_decode ridgeSupport800_suffix_decode_016
theorem ridgeSupport800_suffix_decode_014 : PackedRawNatGrowth.readList 14 271 ridgeSupport800_rest_014 =
    (ridgeSupport800_suffix_014, ridgeSupport800_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 239
    ridgeSupport800_rest_014 ridgeSupport800_rest_015 ridgeSupport800_rest_023
    ridgeSupport800_014 ridgeSupport800_suffix_015 ridgeSupport800_014_decode ridgeSupport800_suffix_decode_015
theorem ridgeSupport800_suffix_decode_013 : PackedRawNatGrowth.readList 14 303 ridgeSupport800_rest_013 =
    (ridgeSupport800_suffix_013, ridgeSupport800_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 271
    ridgeSupport800_rest_013 ridgeSupport800_rest_014 ridgeSupport800_rest_023
    ridgeSupport800_013 ridgeSupport800_suffix_014 ridgeSupport800_013_decode ridgeSupport800_suffix_decode_014
theorem ridgeSupport800_suffix_decode_012 : PackedRawNatGrowth.readList 14 335 ridgeSupport800_rest_012 =
    (ridgeSupport800_suffix_012, ridgeSupport800_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 303
    ridgeSupport800_rest_012 ridgeSupport800_rest_013 ridgeSupport800_rest_023
    ridgeSupport800_012 ridgeSupport800_suffix_013 ridgeSupport800_012_decode ridgeSupport800_suffix_decode_013
theorem ridgeSupport800_suffix_decode_011 : PackedRawNatGrowth.readList 14 367 ridgeSupport800_rest_011 =
    (ridgeSupport800_suffix_011, ridgeSupport800_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 335
    ridgeSupport800_rest_011 ridgeSupport800_rest_012 ridgeSupport800_rest_023
    ridgeSupport800_011 ridgeSupport800_suffix_012 ridgeSupport800_011_decode ridgeSupport800_suffix_decode_012
theorem ridgeSupport800_suffix_decode_010 : PackedRawNatGrowth.readList 14 399 ridgeSupport800_rest_010 =
    (ridgeSupport800_suffix_010, ridgeSupport800_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 367
    ridgeSupport800_rest_010 ridgeSupport800_rest_011 ridgeSupport800_rest_023
    ridgeSupport800_010 ridgeSupport800_suffix_011 ridgeSupport800_010_decode ridgeSupport800_suffix_decode_011
theorem ridgeSupport800_suffix_decode_009 : PackedRawNatGrowth.readList 14 431 ridgeSupport800_rest_009 =
    (ridgeSupport800_suffix_009, ridgeSupport800_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 399
    ridgeSupport800_rest_009 ridgeSupport800_rest_010 ridgeSupport800_rest_023
    ridgeSupport800_009 ridgeSupport800_suffix_010 ridgeSupport800_009_decode ridgeSupport800_suffix_decode_010
theorem ridgeSupport800_suffix_decode_008 : PackedRawNatGrowth.readList 14 463 ridgeSupport800_rest_008 =
    (ridgeSupport800_suffix_008, ridgeSupport800_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 431
    ridgeSupport800_rest_008 ridgeSupport800_rest_009 ridgeSupport800_rest_023
    ridgeSupport800_008 ridgeSupport800_suffix_009 ridgeSupport800_008_decode ridgeSupport800_suffix_decode_009
theorem ridgeSupport800_suffix_decode_007 : PackedRawNatGrowth.readList 14 495 ridgeSupport800_rest_007 =
    (ridgeSupport800_suffix_007, ridgeSupport800_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 463
    ridgeSupport800_rest_007 ridgeSupport800_rest_008 ridgeSupport800_rest_023
    ridgeSupport800_007 ridgeSupport800_suffix_008 ridgeSupport800_007_decode ridgeSupport800_suffix_decode_008
theorem ridgeSupport800_suffix_decode_006 : PackedRawNatGrowth.readList 14 527 ridgeSupport800_rest_006 =
    (ridgeSupport800_suffix_006, ridgeSupport800_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 495
    ridgeSupport800_rest_006 ridgeSupport800_rest_007 ridgeSupport800_rest_023
    ridgeSupport800_006 ridgeSupport800_suffix_007 ridgeSupport800_006_decode ridgeSupport800_suffix_decode_007
theorem ridgeSupport800_suffix_decode_005 : PackedRawNatGrowth.readList 14 559 ridgeSupport800_rest_005 =
    (ridgeSupport800_suffix_005, ridgeSupport800_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 527
    ridgeSupport800_rest_005 ridgeSupport800_rest_006 ridgeSupport800_rest_023
    ridgeSupport800_005 ridgeSupport800_suffix_006 ridgeSupport800_005_decode ridgeSupport800_suffix_decode_006
theorem ridgeSupport800_suffix_decode_004 : PackedRawNatGrowth.readList 14 591 ridgeSupport800_rest_004 =
    (ridgeSupport800_suffix_004, ridgeSupport800_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 559
    ridgeSupport800_rest_004 ridgeSupport800_rest_005 ridgeSupport800_rest_023
    ridgeSupport800_004 ridgeSupport800_suffix_005 ridgeSupport800_004_decode ridgeSupport800_suffix_decode_005
theorem ridgeSupport800_suffix_decode_003 : PackedRawNatGrowth.readList 14 623 ridgeSupport800_rest_003 =
    (ridgeSupport800_suffix_003, ridgeSupport800_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 591
    ridgeSupport800_rest_003 ridgeSupport800_rest_004 ridgeSupport800_rest_023
    ridgeSupport800_003 ridgeSupport800_suffix_004 ridgeSupport800_003_decode ridgeSupport800_suffix_decode_004
theorem ridgeSupport800_suffix_decode_002 : PackedRawNatGrowth.readList 14 655 ridgeSupport800_rest_002 =
    (ridgeSupport800_suffix_002, ridgeSupport800_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 623
    ridgeSupport800_rest_002 ridgeSupport800_rest_003 ridgeSupport800_rest_023
    ridgeSupport800_002 ridgeSupport800_suffix_003 ridgeSupport800_002_decode ridgeSupport800_suffix_decode_003
theorem ridgeSupport800_suffix_decode_001 : PackedRawNatGrowth.readList 14 687 ridgeSupport800_rest_001 =
    (ridgeSupport800_suffix_001, ridgeSupport800_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 655
    ridgeSupport800_rest_001 ridgeSupport800_rest_002 ridgeSupport800_rest_023
    ridgeSupport800_001 ridgeSupport800_suffix_002 ridgeSupport800_001_decode ridgeSupport800_suffix_decode_002
theorem ridgeSupport800_suffix_decode_000 : PackedRawNatGrowth.readList 14 719 ridgeSupport800_rest_000 =
    (ridgeSupport800_suffix_000, ridgeSupport800_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 687
    ridgeSupport800_rest_000 ridgeSupport800_rest_001 ridgeSupport800_rest_023
    ridgeSupport800_000 ridgeSupport800_suffix_001 ridgeSupport800_000_decode ridgeSupport800_suffix_decode_001
theorem ridgeSupport800_eq : candidateRows 800 = ridgeSupport800_suffix_000 := by
  rw [ridgeSupport800_source]
  exact congrArg Prod.fst ridgeSupport800_suffix_decode_000
theorem ridgeTest_large_800 : ridgeTest 800 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport800_eq]
    simp only [ridgeSupport800_suffix_000, ridgeSupport800_suffix_001, ridgeSupport800_suffix_002, ridgeSupport800_suffix_003, ridgeSupport800_suffix_004, ridgeSupport800_suffix_005, ridgeSupport800_suffix_006, ridgeSupport800_suffix_007, ridgeSupport800_suffix_008, ridgeSupport800_suffix_009, ridgeSupport800_suffix_010, ridgeSupport800_suffix_011, ridgeSupport800_suffix_012, ridgeSupport800_suffix_013, ridgeSupport800_suffix_014, ridgeSupport800_suffix_015, ridgeSupport800_suffix_016, ridgeSupport800_suffix_017, ridgeSupport800_suffix_018, ridgeSupport800_suffix_019, ridgeSupport800_suffix_020, ridgeSupport800_suffix_021, ridgeSupport800_suffix_022, ridgeSupport800_suffix_023, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport800_000_mask, ridgeSupport800_001_mask, ridgeSupport800_002_mask, ridgeSupport800_003_mask, ridgeSupport800_004_mask, ridgeSupport800_005_mask, ridgeSupport800_006_mask, ridgeSupport800_007_mask, ridgeSupport800_008_mask, ridgeSupport800_009_mask, ridgeSupport800_010_mask, ridgeSupport800_011_mask, ridgeSupport800_012_mask, ridgeSupport800_013_mask, ridgeSupport800_014_mask, ridgeSupport800_015_mask, ridgeSupport800_016_mask, ridgeSupport800_017_mask, ridgeSupport800_018_mask, ridgeSupport800_019_mask, ridgeSupport800_020_mask, ridgeSupport800_021_mask, ridgeSupport800_022_mask]
    decide +kernel
  · rw [ridgeSupport800_eq]
    simp only [ridgeSupport800_suffix_000, ridgeSupport800_suffix_001, ridgeSupport800_suffix_002, ridgeSupport800_suffix_003, ridgeSupport800_suffix_004, ridgeSupport800_suffix_005, ridgeSupport800_suffix_006, ridgeSupport800_suffix_007, ridgeSupport800_suffix_008, ridgeSupport800_suffix_009, ridgeSupport800_suffix_010, ridgeSupport800_suffix_011, ridgeSupport800_suffix_012, ridgeSupport800_suffix_013, ridgeSupport800_suffix_014, ridgeSupport800_suffix_015, ridgeSupport800_suffix_016, ridgeSupport800_suffix_017, ridgeSupport800_suffix_018, ridgeSupport800_suffix_019, ridgeSupport800_suffix_020, ridgeSupport800_suffix_021, ridgeSupport800_suffix_022, ridgeSupport800_suffix_023, List.all_append, List.all_nil, ridgeSupport800_000_checked, ridgeSupport800_001_checked, ridgeSupport800_002_checked, ridgeSupport800_003_checked, ridgeSupport800_004_checked, ridgeSupport800_005_checked, ridgeSupport800_006_checked, ridgeSupport800_007_checked, ridgeSupport800_008_checked, ridgeSupport800_009_checked, ridgeSupport800_010_checked, ridgeSupport800_011_checked, ridgeSupport800_012_checked, ridgeSupport800_013_checked, ridgeSupport800_014_checked, ridgeSupport800_015_checked, ridgeSupport800_016_checked, ridgeSupport800_017_checked, ridgeSupport800_018_checked, ridgeSupport800_019_checked, ridgeSupport800_020_checked, ridgeSupport800_021_checked, ridgeSupport800_022_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase01
