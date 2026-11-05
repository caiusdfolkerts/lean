module
prelude
public import RootedSixBase01GrowthCacheRidgeSupport336Part000
public import RootedSixBase01GrowthCacheRidgeSupport336Part001
public import RootedSixBase01GrowthCacheRidgeSupport336Part002
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport336_suffix_decode_023 : PackedRawNatGrowth.readList 14 0 ridgeSupport336_rest_023 =
    (ridgeSupport336_suffix_023, ridgeSupport336_rest_023) := by rfl
theorem ridgeSupport336_suffix_decode_022 : PackedRawNatGrowth.readList 14 15 ridgeSupport336_rest_022 =
    (ridgeSupport336_suffix_022, ridgeSupport336_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 15 0
    ridgeSupport336_rest_022 ridgeSupport336_rest_023 ridgeSupport336_rest_023
    ridgeSupport336_022 ridgeSupport336_suffix_023 ridgeSupport336_022_decode ridgeSupport336_suffix_decode_023
theorem ridgeSupport336_suffix_decode_021 : PackedRawNatGrowth.readList 14 47 ridgeSupport336_rest_021 =
    (ridgeSupport336_suffix_021, ridgeSupport336_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 15
    ridgeSupport336_rest_021 ridgeSupport336_rest_022 ridgeSupport336_rest_023
    ridgeSupport336_021 ridgeSupport336_suffix_022 ridgeSupport336_021_decode ridgeSupport336_suffix_decode_022
theorem ridgeSupport336_suffix_decode_020 : PackedRawNatGrowth.readList 14 79 ridgeSupport336_rest_020 =
    (ridgeSupport336_suffix_020, ridgeSupport336_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 47
    ridgeSupport336_rest_020 ridgeSupport336_rest_021 ridgeSupport336_rest_023
    ridgeSupport336_020 ridgeSupport336_suffix_021 ridgeSupport336_020_decode ridgeSupport336_suffix_decode_021
theorem ridgeSupport336_suffix_decode_019 : PackedRawNatGrowth.readList 14 111 ridgeSupport336_rest_019 =
    (ridgeSupport336_suffix_019, ridgeSupport336_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 79
    ridgeSupport336_rest_019 ridgeSupport336_rest_020 ridgeSupport336_rest_023
    ridgeSupport336_019 ridgeSupport336_suffix_020 ridgeSupport336_019_decode ridgeSupport336_suffix_decode_020
theorem ridgeSupport336_suffix_decode_018 : PackedRawNatGrowth.readList 14 143 ridgeSupport336_rest_018 =
    (ridgeSupport336_suffix_018, ridgeSupport336_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 111
    ridgeSupport336_rest_018 ridgeSupport336_rest_019 ridgeSupport336_rest_023
    ridgeSupport336_018 ridgeSupport336_suffix_019 ridgeSupport336_018_decode ridgeSupport336_suffix_decode_019
theorem ridgeSupport336_suffix_decode_017 : PackedRawNatGrowth.readList 14 175 ridgeSupport336_rest_017 =
    (ridgeSupport336_suffix_017, ridgeSupport336_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 143
    ridgeSupport336_rest_017 ridgeSupport336_rest_018 ridgeSupport336_rest_023
    ridgeSupport336_017 ridgeSupport336_suffix_018 ridgeSupport336_017_decode ridgeSupport336_suffix_decode_018
theorem ridgeSupport336_suffix_decode_016 : PackedRawNatGrowth.readList 14 207 ridgeSupport336_rest_016 =
    (ridgeSupport336_suffix_016, ridgeSupport336_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 175
    ridgeSupport336_rest_016 ridgeSupport336_rest_017 ridgeSupport336_rest_023
    ridgeSupport336_016 ridgeSupport336_suffix_017 ridgeSupport336_016_decode ridgeSupport336_suffix_decode_017
theorem ridgeSupport336_suffix_decode_015 : PackedRawNatGrowth.readList 14 239 ridgeSupport336_rest_015 =
    (ridgeSupport336_suffix_015, ridgeSupport336_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 207
    ridgeSupport336_rest_015 ridgeSupport336_rest_016 ridgeSupport336_rest_023
    ridgeSupport336_015 ridgeSupport336_suffix_016 ridgeSupport336_015_decode ridgeSupport336_suffix_decode_016
theorem ridgeSupport336_suffix_decode_014 : PackedRawNatGrowth.readList 14 271 ridgeSupport336_rest_014 =
    (ridgeSupport336_suffix_014, ridgeSupport336_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 239
    ridgeSupport336_rest_014 ridgeSupport336_rest_015 ridgeSupport336_rest_023
    ridgeSupport336_014 ridgeSupport336_suffix_015 ridgeSupport336_014_decode ridgeSupport336_suffix_decode_015
theorem ridgeSupport336_suffix_decode_013 : PackedRawNatGrowth.readList 14 303 ridgeSupport336_rest_013 =
    (ridgeSupport336_suffix_013, ridgeSupport336_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 271
    ridgeSupport336_rest_013 ridgeSupport336_rest_014 ridgeSupport336_rest_023
    ridgeSupport336_013 ridgeSupport336_suffix_014 ridgeSupport336_013_decode ridgeSupport336_suffix_decode_014
theorem ridgeSupport336_suffix_decode_012 : PackedRawNatGrowth.readList 14 335 ridgeSupport336_rest_012 =
    (ridgeSupport336_suffix_012, ridgeSupport336_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 303
    ridgeSupport336_rest_012 ridgeSupport336_rest_013 ridgeSupport336_rest_023
    ridgeSupport336_012 ridgeSupport336_suffix_013 ridgeSupport336_012_decode ridgeSupport336_suffix_decode_013
theorem ridgeSupport336_suffix_decode_011 : PackedRawNatGrowth.readList 14 367 ridgeSupport336_rest_011 =
    (ridgeSupport336_suffix_011, ridgeSupport336_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 335
    ridgeSupport336_rest_011 ridgeSupport336_rest_012 ridgeSupport336_rest_023
    ridgeSupport336_011 ridgeSupport336_suffix_012 ridgeSupport336_011_decode ridgeSupport336_suffix_decode_012
theorem ridgeSupport336_suffix_decode_010 : PackedRawNatGrowth.readList 14 399 ridgeSupport336_rest_010 =
    (ridgeSupport336_suffix_010, ridgeSupport336_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 367
    ridgeSupport336_rest_010 ridgeSupport336_rest_011 ridgeSupport336_rest_023
    ridgeSupport336_010 ridgeSupport336_suffix_011 ridgeSupport336_010_decode ridgeSupport336_suffix_decode_011
theorem ridgeSupport336_suffix_decode_009 : PackedRawNatGrowth.readList 14 431 ridgeSupport336_rest_009 =
    (ridgeSupport336_suffix_009, ridgeSupport336_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 399
    ridgeSupport336_rest_009 ridgeSupport336_rest_010 ridgeSupport336_rest_023
    ridgeSupport336_009 ridgeSupport336_suffix_010 ridgeSupport336_009_decode ridgeSupport336_suffix_decode_010
theorem ridgeSupport336_suffix_decode_008 : PackedRawNatGrowth.readList 14 463 ridgeSupport336_rest_008 =
    (ridgeSupport336_suffix_008, ridgeSupport336_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 431
    ridgeSupport336_rest_008 ridgeSupport336_rest_009 ridgeSupport336_rest_023
    ridgeSupport336_008 ridgeSupport336_suffix_009 ridgeSupport336_008_decode ridgeSupport336_suffix_decode_009
theorem ridgeSupport336_suffix_decode_007 : PackedRawNatGrowth.readList 14 495 ridgeSupport336_rest_007 =
    (ridgeSupport336_suffix_007, ridgeSupport336_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 463
    ridgeSupport336_rest_007 ridgeSupport336_rest_008 ridgeSupport336_rest_023
    ridgeSupport336_007 ridgeSupport336_suffix_008 ridgeSupport336_007_decode ridgeSupport336_suffix_decode_008
theorem ridgeSupport336_suffix_decode_006 : PackedRawNatGrowth.readList 14 527 ridgeSupport336_rest_006 =
    (ridgeSupport336_suffix_006, ridgeSupport336_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 495
    ridgeSupport336_rest_006 ridgeSupport336_rest_007 ridgeSupport336_rest_023
    ridgeSupport336_006 ridgeSupport336_suffix_007 ridgeSupport336_006_decode ridgeSupport336_suffix_decode_007
theorem ridgeSupport336_suffix_decode_005 : PackedRawNatGrowth.readList 14 559 ridgeSupport336_rest_005 =
    (ridgeSupport336_suffix_005, ridgeSupport336_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 527
    ridgeSupport336_rest_005 ridgeSupport336_rest_006 ridgeSupport336_rest_023
    ridgeSupport336_005 ridgeSupport336_suffix_006 ridgeSupport336_005_decode ridgeSupport336_suffix_decode_006
theorem ridgeSupport336_suffix_decode_004 : PackedRawNatGrowth.readList 14 591 ridgeSupport336_rest_004 =
    (ridgeSupport336_suffix_004, ridgeSupport336_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 559
    ridgeSupport336_rest_004 ridgeSupport336_rest_005 ridgeSupport336_rest_023
    ridgeSupport336_004 ridgeSupport336_suffix_005 ridgeSupport336_004_decode ridgeSupport336_suffix_decode_005
theorem ridgeSupport336_suffix_decode_003 : PackedRawNatGrowth.readList 14 623 ridgeSupport336_rest_003 =
    (ridgeSupport336_suffix_003, ridgeSupport336_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 591
    ridgeSupport336_rest_003 ridgeSupport336_rest_004 ridgeSupport336_rest_023
    ridgeSupport336_003 ridgeSupport336_suffix_004 ridgeSupport336_003_decode ridgeSupport336_suffix_decode_004
theorem ridgeSupport336_suffix_decode_002 : PackedRawNatGrowth.readList 14 655 ridgeSupport336_rest_002 =
    (ridgeSupport336_suffix_002, ridgeSupport336_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 623
    ridgeSupport336_rest_002 ridgeSupport336_rest_003 ridgeSupport336_rest_023
    ridgeSupport336_002 ridgeSupport336_suffix_003 ridgeSupport336_002_decode ridgeSupport336_suffix_decode_003
theorem ridgeSupport336_suffix_decode_001 : PackedRawNatGrowth.readList 14 687 ridgeSupport336_rest_001 =
    (ridgeSupport336_suffix_001, ridgeSupport336_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 655
    ridgeSupport336_rest_001 ridgeSupport336_rest_002 ridgeSupport336_rest_023
    ridgeSupport336_001 ridgeSupport336_suffix_002 ridgeSupport336_001_decode ridgeSupport336_suffix_decode_002
theorem ridgeSupport336_suffix_decode_000 : PackedRawNatGrowth.readList 14 719 ridgeSupport336_rest_000 =
    (ridgeSupport336_suffix_000, ridgeSupport336_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 687
    ridgeSupport336_rest_000 ridgeSupport336_rest_001 ridgeSupport336_rest_023
    ridgeSupport336_000 ridgeSupport336_suffix_001 ridgeSupport336_000_decode ridgeSupport336_suffix_decode_001
theorem ridgeSupport336_eq : candidateRows 336 = ridgeSupport336_suffix_000 := by
  rw [ridgeSupport336_source]
  exact congrArg Prod.fst ridgeSupport336_suffix_decode_000
theorem ridgeTest_large_336 : ridgeTest 336 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport336_eq]
    simp only [ridgeSupport336_suffix_000, ridgeSupport336_suffix_001, ridgeSupport336_suffix_002, ridgeSupport336_suffix_003, ridgeSupport336_suffix_004, ridgeSupport336_suffix_005, ridgeSupport336_suffix_006, ridgeSupport336_suffix_007, ridgeSupport336_suffix_008, ridgeSupport336_suffix_009, ridgeSupport336_suffix_010, ridgeSupport336_suffix_011, ridgeSupport336_suffix_012, ridgeSupport336_suffix_013, ridgeSupport336_suffix_014, ridgeSupport336_suffix_015, ridgeSupport336_suffix_016, ridgeSupport336_suffix_017, ridgeSupport336_suffix_018, ridgeSupport336_suffix_019, ridgeSupport336_suffix_020, ridgeSupport336_suffix_021, ridgeSupport336_suffix_022, ridgeSupport336_suffix_023, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport336_000_mask, ridgeSupport336_001_mask, ridgeSupport336_002_mask, ridgeSupport336_003_mask, ridgeSupport336_004_mask, ridgeSupport336_005_mask, ridgeSupport336_006_mask, ridgeSupport336_007_mask, ridgeSupport336_008_mask, ridgeSupport336_009_mask, ridgeSupport336_010_mask, ridgeSupport336_011_mask, ridgeSupport336_012_mask, ridgeSupport336_013_mask, ridgeSupport336_014_mask, ridgeSupport336_015_mask, ridgeSupport336_016_mask, ridgeSupport336_017_mask, ridgeSupport336_018_mask, ridgeSupport336_019_mask, ridgeSupport336_020_mask, ridgeSupport336_021_mask, ridgeSupport336_022_mask]
    decide +kernel
  · rw [ridgeSupport336_eq]
    simp only [ridgeSupport336_suffix_000, ridgeSupport336_suffix_001, ridgeSupport336_suffix_002, ridgeSupport336_suffix_003, ridgeSupport336_suffix_004, ridgeSupport336_suffix_005, ridgeSupport336_suffix_006, ridgeSupport336_suffix_007, ridgeSupport336_suffix_008, ridgeSupport336_suffix_009, ridgeSupport336_suffix_010, ridgeSupport336_suffix_011, ridgeSupport336_suffix_012, ridgeSupport336_suffix_013, ridgeSupport336_suffix_014, ridgeSupport336_suffix_015, ridgeSupport336_suffix_016, ridgeSupport336_suffix_017, ridgeSupport336_suffix_018, ridgeSupport336_suffix_019, ridgeSupport336_suffix_020, ridgeSupport336_suffix_021, ridgeSupport336_suffix_022, ridgeSupport336_suffix_023, List.all_append, List.all_nil, ridgeSupport336_000_checked, ridgeSupport336_001_checked, ridgeSupport336_002_checked, ridgeSupport336_003_checked, ridgeSupport336_004_checked, ridgeSupport336_005_checked, ridgeSupport336_006_checked, ridgeSupport336_007_checked, ridgeSupport336_008_checked, ridgeSupport336_009_checked, ridgeSupport336_010_checked, ridgeSupport336_011_checked, ridgeSupport336_012_checked, ridgeSupport336_013_checked, ridgeSupport336_014_checked, ridgeSupport336_015_checked, ridgeSupport336_016_checked, ridgeSupport336_017_checked, ridgeSupport336_018_checked, ridgeSupport336_019_checked, ridgeSupport336_020_checked, ridgeSupport336_021_checked, ridgeSupport336_022_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase01
