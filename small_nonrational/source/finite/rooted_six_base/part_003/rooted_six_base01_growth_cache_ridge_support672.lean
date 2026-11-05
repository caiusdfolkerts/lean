module
prelude
public import RootedSixBase01GrowthCacheRidgeSupport672Part000
public import RootedSixBase01GrowthCacheRidgeSupport672Part001
public import RootedSixBase01GrowthCacheRidgeSupport672Part002
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport672_suffix_decode_023 : PackedRawNatGrowth.readList 14 0 ridgeSupport672_rest_023 =
    (ridgeSupport672_suffix_023, ridgeSupport672_rest_023) := by rfl
theorem ridgeSupport672_suffix_decode_022 : PackedRawNatGrowth.readList 14 15 ridgeSupport672_rest_022 =
    (ridgeSupport672_suffix_022, ridgeSupport672_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 15 0
    ridgeSupport672_rest_022 ridgeSupport672_rest_023 ridgeSupport672_rest_023
    ridgeSupport672_022 ridgeSupport672_suffix_023 ridgeSupport672_022_decode ridgeSupport672_suffix_decode_023
theorem ridgeSupport672_suffix_decode_021 : PackedRawNatGrowth.readList 14 47 ridgeSupport672_rest_021 =
    (ridgeSupport672_suffix_021, ridgeSupport672_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 15
    ridgeSupport672_rest_021 ridgeSupport672_rest_022 ridgeSupport672_rest_023
    ridgeSupport672_021 ridgeSupport672_suffix_022 ridgeSupport672_021_decode ridgeSupport672_suffix_decode_022
theorem ridgeSupport672_suffix_decode_020 : PackedRawNatGrowth.readList 14 79 ridgeSupport672_rest_020 =
    (ridgeSupport672_suffix_020, ridgeSupport672_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 47
    ridgeSupport672_rest_020 ridgeSupport672_rest_021 ridgeSupport672_rest_023
    ridgeSupport672_020 ridgeSupport672_suffix_021 ridgeSupport672_020_decode ridgeSupport672_suffix_decode_021
theorem ridgeSupport672_suffix_decode_019 : PackedRawNatGrowth.readList 14 111 ridgeSupport672_rest_019 =
    (ridgeSupport672_suffix_019, ridgeSupport672_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 79
    ridgeSupport672_rest_019 ridgeSupport672_rest_020 ridgeSupport672_rest_023
    ridgeSupport672_019 ridgeSupport672_suffix_020 ridgeSupport672_019_decode ridgeSupport672_suffix_decode_020
theorem ridgeSupport672_suffix_decode_018 : PackedRawNatGrowth.readList 14 143 ridgeSupport672_rest_018 =
    (ridgeSupport672_suffix_018, ridgeSupport672_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 111
    ridgeSupport672_rest_018 ridgeSupport672_rest_019 ridgeSupport672_rest_023
    ridgeSupport672_018 ridgeSupport672_suffix_019 ridgeSupport672_018_decode ridgeSupport672_suffix_decode_019
theorem ridgeSupport672_suffix_decode_017 : PackedRawNatGrowth.readList 14 175 ridgeSupport672_rest_017 =
    (ridgeSupport672_suffix_017, ridgeSupport672_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 143
    ridgeSupport672_rest_017 ridgeSupport672_rest_018 ridgeSupport672_rest_023
    ridgeSupport672_017 ridgeSupport672_suffix_018 ridgeSupport672_017_decode ridgeSupport672_suffix_decode_018
theorem ridgeSupport672_suffix_decode_016 : PackedRawNatGrowth.readList 14 207 ridgeSupport672_rest_016 =
    (ridgeSupport672_suffix_016, ridgeSupport672_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 175
    ridgeSupport672_rest_016 ridgeSupport672_rest_017 ridgeSupport672_rest_023
    ridgeSupport672_016 ridgeSupport672_suffix_017 ridgeSupport672_016_decode ridgeSupport672_suffix_decode_017
theorem ridgeSupport672_suffix_decode_015 : PackedRawNatGrowth.readList 14 239 ridgeSupport672_rest_015 =
    (ridgeSupport672_suffix_015, ridgeSupport672_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 207
    ridgeSupport672_rest_015 ridgeSupport672_rest_016 ridgeSupport672_rest_023
    ridgeSupport672_015 ridgeSupport672_suffix_016 ridgeSupport672_015_decode ridgeSupport672_suffix_decode_016
theorem ridgeSupport672_suffix_decode_014 : PackedRawNatGrowth.readList 14 271 ridgeSupport672_rest_014 =
    (ridgeSupport672_suffix_014, ridgeSupport672_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 239
    ridgeSupport672_rest_014 ridgeSupport672_rest_015 ridgeSupport672_rest_023
    ridgeSupport672_014 ridgeSupport672_suffix_015 ridgeSupport672_014_decode ridgeSupport672_suffix_decode_015
theorem ridgeSupport672_suffix_decode_013 : PackedRawNatGrowth.readList 14 303 ridgeSupport672_rest_013 =
    (ridgeSupport672_suffix_013, ridgeSupport672_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 271
    ridgeSupport672_rest_013 ridgeSupport672_rest_014 ridgeSupport672_rest_023
    ridgeSupport672_013 ridgeSupport672_suffix_014 ridgeSupport672_013_decode ridgeSupport672_suffix_decode_014
theorem ridgeSupport672_suffix_decode_012 : PackedRawNatGrowth.readList 14 335 ridgeSupport672_rest_012 =
    (ridgeSupport672_suffix_012, ridgeSupport672_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 303
    ridgeSupport672_rest_012 ridgeSupport672_rest_013 ridgeSupport672_rest_023
    ridgeSupport672_012 ridgeSupport672_suffix_013 ridgeSupport672_012_decode ridgeSupport672_suffix_decode_013
theorem ridgeSupport672_suffix_decode_011 : PackedRawNatGrowth.readList 14 367 ridgeSupport672_rest_011 =
    (ridgeSupport672_suffix_011, ridgeSupport672_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 335
    ridgeSupport672_rest_011 ridgeSupport672_rest_012 ridgeSupport672_rest_023
    ridgeSupport672_011 ridgeSupport672_suffix_012 ridgeSupport672_011_decode ridgeSupport672_suffix_decode_012
theorem ridgeSupport672_suffix_decode_010 : PackedRawNatGrowth.readList 14 399 ridgeSupport672_rest_010 =
    (ridgeSupport672_suffix_010, ridgeSupport672_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 367
    ridgeSupport672_rest_010 ridgeSupport672_rest_011 ridgeSupport672_rest_023
    ridgeSupport672_010 ridgeSupport672_suffix_011 ridgeSupport672_010_decode ridgeSupport672_suffix_decode_011
theorem ridgeSupport672_suffix_decode_009 : PackedRawNatGrowth.readList 14 431 ridgeSupport672_rest_009 =
    (ridgeSupport672_suffix_009, ridgeSupport672_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 399
    ridgeSupport672_rest_009 ridgeSupport672_rest_010 ridgeSupport672_rest_023
    ridgeSupport672_009 ridgeSupport672_suffix_010 ridgeSupport672_009_decode ridgeSupport672_suffix_decode_010
theorem ridgeSupport672_suffix_decode_008 : PackedRawNatGrowth.readList 14 463 ridgeSupport672_rest_008 =
    (ridgeSupport672_suffix_008, ridgeSupport672_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 431
    ridgeSupport672_rest_008 ridgeSupport672_rest_009 ridgeSupport672_rest_023
    ridgeSupport672_008 ridgeSupport672_suffix_009 ridgeSupport672_008_decode ridgeSupport672_suffix_decode_009
theorem ridgeSupport672_suffix_decode_007 : PackedRawNatGrowth.readList 14 495 ridgeSupport672_rest_007 =
    (ridgeSupport672_suffix_007, ridgeSupport672_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 463
    ridgeSupport672_rest_007 ridgeSupport672_rest_008 ridgeSupport672_rest_023
    ridgeSupport672_007 ridgeSupport672_suffix_008 ridgeSupport672_007_decode ridgeSupport672_suffix_decode_008
theorem ridgeSupport672_suffix_decode_006 : PackedRawNatGrowth.readList 14 527 ridgeSupport672_rest_006 =
    (ridgeSupport672_suffix_006, ridgeSupport672_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 495
    ridgeSupport672_rest_006 ridgeSupport672_rest_007 ridgeSupport672_rest_023
    ridgeSupport672_006 ridgeSupport672_suffix_007 ridgeSupport672_006_decode ridgeSupport672_suffix_decode_007
theorem ridgeSupport672_suffix_decode_005 : PackedRawNatGrowth.readList 14 559 ridgeSupport672_rest_005 =
    (ridgeSupport672_suffix_005, ridgeSupport672_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 527
    ridgeSupport672_rest_005 ridgeSupport672_rest_006 ridgeSupport672_rest_023
    ridgeSupport672_005 ridgeSupport672_suffix_006 ridgeSupport672_005_decode ridgeSupport672_suffix_decode_006
theorem ridgeSupport672_suffix_decode_004 : PackedRawNatGrowth.readList 14 591 ridgeSupport672_rest_004 =
    (ridgeSupport672_suffix_004, ridgeSupport672_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 559
    ridgeSupport672_rest_004 ridgeSupport672_rest_005 ridgeSupport672_rest_023
    ridgeSupport672_004 ridgeSupport672_suffix_005 ridgeSupport672_004_decode ridgeSupport672_suffix_decode_005
theorem ridgeSupport672_suffix_decode_003 : PackedRawNatGrowth.readList 14 623 ridgeSupport672_rest_003 =
    (ridgeSupport672_suffix_003, ridgeSupport672_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 591
    ridgeSupport672_rest_003 ridgeSupport672_rest_004 ridgeSupport672_rest_023
    ridgeSupport672_003 ridgeSupport672_suffix_004 ridgeSupport672_003_decode ridgeSupport672_suffix_decode_004
theorem ridgeSupport672_suffix_decode_002 : PackedRawNatGrowth.readList 14 655 ridgeSupport672_rest_002 =
    (ridgeSupport672_suffix_002, ridgeSupport672_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 623
    ridgeSupport672_rest_002 ridgeSupport672_rest_003 ridgeSupport672_rest_023
    ridgeSupport672_002 ridgeSupport672_suffix_003 ridgeSupport672_002_decode ridgeSupport672_suffix_decode_003
theorem ridgeSupport672_suffix_decode_001 : PackedRawNatGrowth.readList 14 687 ridgeSupport672_rest_001 =
    (ridgeSupport672_suffix_001, ridgeSupport672_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 655
    ridgeSupport672_rest_001 ridgeSupport672_rest_002 ridgeSupport672_rest_023
    ridgeSupport672_001 ridgeSupport672_suffix_002 ridgeSupport672_001_decode ridgeSupport672_suffix_decode_002
theorem ridgeSupport672_suffix_decode_000 : PackedRawNatGrowth.readList 14 719 ridgeSupport672_rest_000 =
    (ridgeSupport672_suffix_000, ridgeSupport672_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 687
    ridgeSupport672_rest_000 ridgeSupport672_rest_001 ridgeSupport672_rest_023
    ridgeSupport672_000 ridgeSupport672_suffix_001 ridgeSupport672_000_decode ridgeSupport672_suffix_decode_001
theorem ridgeSupport672_eq : candidateRows 672 = ridgeSupport672_suffix_000 := by
  rw [ridgeSupport672_source]
  exact congrArg Prod.fst ridgeSupport672_suffix_decode_000
theorem ridgeTest_large_672 : ridgeTest 672 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport672_eq]
    simp only [ridgeSupport672_suffix_000, ridgeSupport672_suffix_001, ridgeSupport672_suffix_002, ridgeSupport672_suffix_003, ridgeSupport672_suffix_004, ridgeSupport672_suffix_005, ridgeSupport672_suffix_006, ridgeSupport672_suffix_007, ridgeSupport672_suffix_008, ridgeSupport672_suffix_009, ridgeSupport672_suffix_010, ridgeSupport672_suffix_011, ridgeSupport672_suffix_012, ridgeSupport672_suffix_013, ridgeSupport672_suffix_014, ridgeSupport672_suffix_015, ridgeSupport672_suffix_016, ridgeSupport672_suffix_017, ridgeSupport672_suffix_018, ridgeSupport672_suffix_019, ridgeSupport672_suffix_020, ridgeSupport672_suffix_021, ridgeSupport672_suffix_022, ridgeSupport672_suffix_023, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport672_000_mask, ridgeSupport672_001_mask, ridgeSupport672_002_mask, ridgeSupport672_003_mask, ridgeSupport672_004_mask, ridgeSupport672_005_mask, ridgeSupport672_006_mask, ridgeSupport672_007_mask, ridgeSupport672_008_mask, ridgeSupport672_009_mask, ridgeSupport672_010_mask, ridgeSupport672_011_mask, ridgeSupport672_012_mask, ridgeSupport672_013_mask, ridgeSupport672_014_mask, ridgeSupport672_015_mask, ridgeSupport672_016_mask, ridgeSupport672_017_mask, ridgeSupport672_018_mask, ridgeSupport672_019_mask, ridgeSupport672_020_mask, ridgeSupport672_021_mask, ridgeSupport672_022_mask]
    decide +kernel
  · rw [ridgeSupport672_eq]
    simp only [ridgeSupport672_suffix_000, ridgeSupport672_suffix_001, ridgeSupport672_suffix_002, ridgeSupport672_suffix_003, ridgeSupport672_suffix_004, ridgeSupport672_suffix_005, ridgeSupport672_suffix_006, ridgeSupport672_suffix_007, ridgeSupport672_suffix_008, ridgeSupport672_suffix_009, ridgeSupport672_suffix_010, ridgeSupport672_suffix_011, ridgeSupport672_suffix_012, ridgeSupport672_suffix_013, ridgeSupport672_suffix_014, ridgeSupport672_suffix_015, ridgeSupport672_suffix_016, ridgeSupport672_suffix_017, ridgeSupport672_suffix_018, ridgeSupport672_suffix_019, ridgeSupport672_suffix_020, ridgeSupport672_suffix_021, ridgeSupport672_suffix_022, ridgeSupport672_suffix_023, List.all_append, List.all_nil, ridgeSupport672_000_checked, ridgeSupport672_001_checked, ridgeSupport672_002_checked, ridgeSupport672_003_checked, ridgeSupport672_004_checked, ridgeSupport672_005_checked, ridgeSupport672_006_checked, ridgeSupport672_007_checked, ridgeSupport672_008_checked, ridgeSupport672_009_checked, ridgeSupport672_010_checked, ridgeSupport672_011_checked, ridgeSupport672_012_checked, ridgeSupport672_013_checked, ridgeSupport672_014_checked, ridgeSupport672_015_checked, ridgeSupport672_016_checked, ridgeSupport672_017_checked, ridgeSupport672_018_checked, ridgeSupport672_019_checked, ridgeSupport672_020_checked, ridgeSupport672_021_checked, ridgeSupport672_022_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase01
