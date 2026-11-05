module
prelude
public import RootedSixBase01GrowthCacheRidgeSupport416Part000
public import RootedSixBase01GrowthCacheRidgeSupport416Part001
public import RootedSixBase01GrowthCacheRidgeSupport416Part002
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport416_suffix_decode_023 : PackedRawNatGrowth.readList 14 0 ridgeSupport416_rest_023 =
    (ridgeSupport416_suffix_023, ridgeSupport416_rest_023) := by rfl
theorem ridgeSupport416_suffix_decode_022 : PackedRawNatGrowth.readList 14 15 ridgeSupport416_rest_022 =
    (ridgeSupport416_suffix_022, ridgeSupport416_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 15 0
    ridgeSupport416_rest_022 ridgeSupport416_rest_023 ridgeSupport416_rest_023
    ridgeSupport416_022 ridgeSupport416_suffix_023 ridgeSupport416_022_decode ridgeSupport416_suffix_decode_023
theorem ridgeSupport416_suffix_decode_021 : PackedRawNatGrowth.readList 14 47 ridgeSupport416_rest_021 =
    (ridgeSupport416_suffix_021, ridgeSupport416_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 15
    ridgeSupport416_rest_021 ridgeSupport416_rest_022 ridgeSupport416_rest_023
    ridgeSupport416_021 ridgeSupport416_suffix_022 ridgeSupport416_021_decode ridgeSupport416_suffix_decode_022
theorem ridgeSupport416_suffix_decode_020 : PackedRawNatGrowth.readList 14 79 ridgeSupport416_rest_020 =
    (ridgeSupport416_suffix_020, ridgeSupport416_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 47
    ridgeSupport416_rest_020 ridgeSupport416_rest_021 ridgeSupport416_rest_023
    ridgeSupport416_020 ridgeSupport416_suffix_021 ridgeSupport416_020_decode ridgeSupport416_suffix_decode_021
theorem ridgeSupport416_suffix_decode_019 : PackedRawNatGrowth.readList 14 111 ridgeSupport416_rest_019 =
    (ridgeSupport416_suffix_019, ridgeSupport416_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 79
    ridgeSupport416_rest_019 ridgeSupport416_rest_020 ridgeSupport416_rest_023
    ridgeSupport416_019 ridgeSupport416_suffix_020 ridgeSupport416_019_decode ridgeSupport416_suffix_decode_020
theorem ridgeSupport416_suffix_decode_018 : PackedRawNatGrowth.readList 14 143 ridgeSupport416_rest_018 =
    (ridgeSupport416_suffix_018, ridgeSupport416_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 111
    ridgeSupport416_rest_018 ridgeSupport416_rest_019 ridgeSupport416_rest_023
    ridgeSupport416_018 ridgeSupport416_suffix_019 ridgeSupport416_018_decode ridgeSupport416_suffix_decode_019
theorem ridgeSupport416_suffix_decode_017 : PackedRawNatGrowth.readList 14 175 ridgeSupport416_rest_017 =
    (ridgeSupport416_suffix_017, ridgeSupport416_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 143
    ridgeSupport416_rest_017 ridgeSupport416_rest_018 ridgeSupport416_rest_023
    ridgeSupport416_017 ridgeSupport416_suffix_018 ridgeSupport416_017_decode ridgeSupport416_suffix_decode_018
theorem ridgeSupport416_suffix_decode_016 : PackedRawNatGrowth.readList 14 207 ridgeSupport416_rest_016 =
    (ridgeSupport416_suffix_016, ridgeSupport416_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 175
    ridgeSupport416_rest_016 ridgeSupport416_rest_017 ridgeSupport416_rest_023
    ridgeSupport416_016 ridgeSupport416_suffix_017 ridgeSupport416_016_decode ridgeSupport416_suffix_decode_017
theorem ridgeSupport416_suffix_decode_015 : PackedRawNatGrowth.readList 14 239 ridgeSupport416_rest_015 =
    (ridgeSupport416_suffix_015, ridgeSupport416_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 207
    ridgeSupport416_rest_015 ridgeSupport416_rest_016 ridgeSupport416_rest_023
    ridgeSupport416_015 ridgeSupport416_suffix_016 ridgeSupport416_015_decode ridgeSupport416_suffix_decode_016
theorem ridgeSupport416_suffix_decode_014 : PackedRawNatGrowth.readList 14 271 ridgeSupport416_rest_014 =
    (ridgeSupport416_suffix_014, ridgeSupport416_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 239
    ridgeSupport416_rest_014 ridgeSupport416_rest_015 ridgeSupport416_rest_023
    ridgeSupport416_014 ridgeSupport416_suffix_015 ridgeSupport416_014_decode ridgeSupport416_suffix_decode_015
theorem ridgeSupport416_suffix_decode_013 : PackedRawNatGrowth.readList 14 303 ridgeSupport416_rest_013 =
    (ridgeSupport416_suffix_013, ridgeSupport416_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 271
    ridgeSupport416_rest_013 ridgeSupport416_rest_014 ridgeSupport416_rest_023
    ridgeSupport416_013 ridgeSupport416_suffix_014 ridgeSupport416_013_decode ridgeSupport416_suffix_decode_014
theorem ridgeSupport416_suffix_decode_012 : PackedRawNatGrowth.readList 14 335 ridgeSupport416_rest_012 =
    (ridgeSupport416_suffix_012, ridgeSupport416_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 303
    ridgeSupport416_rest_012 ridgeSupport416_rest_013 ridgeSupport416_rest_023
    ridgeSupport416_012 ridgeSupport416_suffix_013 ridgeSupport416_012_decode ridgeSupport416_suffix_decode_013
theorem ridgeSupport416_suffix_decode_011 : PackedRawNatGrowth.readList 14 367 ridgeSupport416_rest_011 =
    (ridgeSupport416_suffix_011, ridgeSupport416_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 335
    ridgeSupport416_rest_011 ridgeSupport416_rest_012 ridgeSupport416_rest_023
    ridgeSupport416_011 ridgeSupport416_suffix_012 ridgeSupport416_011_decode ridgeSupport416_suffix_decode_012
theorem ridgeSupport416_suffix_decode_010 : PackedRawNatGrowth.readList 14 399 ridgeSupport416_rest_010 =
    (ridgeSupport416_suffix_010, ridgeSupport416_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 367
    ridgeSupport416_rest_010 ridgeSupport416_rest_011 ridgeSupport416_rest_023
    ridgeSupport416_010 ridgeSupport416_suffix_011 ridgeSupport416_010_decode ridgeSupport416_suffix_decode_011
theorem ridgeSupport416_suffix_decode_009 : PackedRawNatGrowth.readList 14 431 ridgeSupport416_rest_009 =
    (ridgeSupport416_suffix_009, ridgeSupport416_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 399
    ridgeSupport416_rest_009 ridgeSupport416_rest_010 ridgeSupport416_rest_023
    ridgeSupport416_009 ridgeSupport416_suffix_010 ridgeSupport416_009_decode ridgeSupport416_suffix_decode_010
theorem ridgeSupport416_suffix_decode_008 : PackedRawNatGrowth.readList 14 463 ridgeSupport416_rest_008 =
    (ridgeSupport416_suffix_008, ridgeSupport416_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 431
    ridgeSupport416_rest_008 ridgeSupport416_rest_009 ridgeSupport416_rest_023
    ridgeSupport416_008 ridgeSupport416_suffix_009 ridgeSupport416_008_decode ridgeSupport416_suffix_decode_009
theorem ridgeSupport416_suffix_decode_007 : PackedRawNatGrowth.readList 14 495 ridgeSupport416_rest_007 =
    (ridgeSupport416_suffix_007, ridgeSupport416_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 463
    ridgeSupport416_rest_007 ridgeSupport416_rest_008 ridgeSupport416_rest_023
    ridgeSupport416_007 ridgeSupport416_suffix_008 ridgeSupport416_007_decode ridgeSupport416_suffix_decode_008
theorem ridgeSupport416_suffix_decode_006 : PackedRawNatGrowth.readList 14 527 ridgeSupport416_rest_006 =
    (ridgeSupport416_suffix_006, ridgeSupport416_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 495
    ridgeSupport416_rest_006 ridgeSupport416_rest_007 ridgeSupport416_rest_023
    ridgeSupport416_006 ridgeSupport416_suffix_007 ridgeSupport416_006_decode ridgeSupport416_suffix_decode_007
theorem ridgeSupport416_suffix_decode_005 : PackedRawNatGrowth.readList 14 559 ridgeSupport416_rest_005 =
    (ridgeSupport416_suffix_005, ridgeSupport416_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 527
    ridgeSupport416_rest_005 ridgeSupport416_rest_006 ridgeSupport416_rest_023
    ridgeSupport416_005 ridgeSupport416_suffix_006 ridgeSupport416_005_decode ridgeSupport416_suffix_decode_006
theorem ridgeSupport416_suffix_decode_004 : PackedRawNatGrowth.readList 14 591 ridgeSupport416_rest_004 =
    (ridgeSupport416_suffix_004, ridgeSupport416_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 559
    ridgeSupport416_rest_004 ridgeSupport416_rest_005 ridgeSupport416_rest_023
    ridgeSupport416_004 ridgeSupport416_suffix_005 ridgeSupport416_004_decode ridgeSupport416_suffix_decode_005
theorem ridgeSupport416_suffix_decode_003 : PackedRawNatGrowth.readList 14 623 ridgeSupport416_rest_003 =
    (ridgeSupport416_suffix_003, ridgeSupport416_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 591
    ridgeSupport416_rest_003 ridgeSupport416_rest_004 ridgeSupport416_rest_023
    ridgeSupport416_003 ridgeSupport416_suffix_004 ridgeSupport416_003_decode ridgeSupport416_suffix_decode_004
theorem ridgeSupport416_suffix_decode_002 : PackedRawNatGrowth.readList 14 655 ridgeSupport416_rest_002 =
    (ridgeSupport416_suffix_002, ridgeSupport416_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 623
    ridgeSupport416_rest_002 ridgeSupport416_rest_003 ridgeSupport416_rest_023
    ridgeSupport416_002 ridgeSupport416_suffix_003 ridgeSupport416_002_decode ridgeSupport416_suffix_decode_003
theorem ridgeSupport416_suffix_decode_001 : PackedRawNatGrowth.readList 14 687 ridgeSupport416_rest_001 =
    (ridgeSupport416_suffix_001, ridgeSupport416_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 655
    ridgeSupport416_rest_001 ridgeSupport416_rest_002 ridgeSupport416_rest_023
    ridgeSupport416_001 ridgeSupport416_suffix_002 ridgeSupport416_001_decode ridgeSupport416_suffix_decode_002
theorem ridgeSupport416_suffix_decode_000 : PackedRawNatGrowth.readList 14 719 ridgeSupport416_rest_000 =
    (ridgeSupport416_suffix_000, ridgeSupport416_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 687
    ridgeSupport416_rest_000 ridgeSupport416_rest_001 ridgeSupport416_rest_023
    ridgeSupport416_000 ridgeSupport416_suffix_001 ridgeSupport416_000_decode ridgeSupport416_suffix_decode_001
theorem ridgeSupport416_eq : candidateRows 416 = ridgeSupport416_suffix_000 := by
  rw [ridgeSupport416_source]
  exact congrArg Prod.fst ridgeSupport416_suffix_decode_000
theorem ridgeTest_large_416 : ridgeTest 416 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport416_eq]
    simp only [ridgeSupport416_suffix_000, ridgeSupport416_suffix_001, ridgeSupport416_suffix_002, ridgeSupport416_suffix_003, ridgeSupport416_suffix_004, ridgeSupport416_suffix_005, ridgeSupport416_suffix_006, ridgeSupport416_suffix_007, ridgeSupport416_suffix_008, ridgeSupport416_suffix_009, ridgeSupport416_suffix_010, ridgeSupport416_suffix_011, ridgeSupport416_suffix_012, ridgeSupport416_suffix_013, ridgeSupport416_suffix_014, ridgeSupport416_suffix_015, ridgeSupport416_suffix_016, ridgeSupport416_suffix_017, ridgeSupport416_suffix_018, ridgeSupport416_suffix_019, ridgeSupport416_suffix_020, ridgeSupport416_suffix_021, ridgeSupport416_suffix_022, ridgeSupport416_suffix_023, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport416_000_mask, ridgeSupport416_001_mask, ridgeSupport416_002_mask, ridgeSupport416_003_mask, ridgeSupport416_004_mask, ridgeSupport416_005_mask, ridgeSupport416_006_mask, ridgeSupport416_007_mask, ridgeSupport416_008_mask, ridgeSupport416_009_mask, ridgeSupport416_010_mask, ridgeSupport416_011_mask, ridgeSupport416_012_mask, ridgeSupport416_013_mask, ridgeSupport416_014_mask, ridgeSupport416_015_mask, ridgeSupport416_016_mask, ridgeSupport416_017_mask, ridgeSupport416_018_mask, ridgeSupport416_019_mask, ridgeSupport416_020_mask, ridgeSupport416_021_mask, ridgeSupport416_022_mask]
    decide +kernel
  · rw [ridgeSupport416_eq]
    simp only [ridgeSupport416_suffix_000, ridgeSupport416_suffix_001, ridgeSupport416_suffix_002, ridgeSupport416_suffix_003, ridgeSupport416_suffix_004, ridgeSupport416_suffix_005, ridgeSupport416_suffix_006, ridgeSupport416_suffix_007, ridgeSupport416_suffix_008, ridgeSupport416_suffix_009, ridgeSupport416_suffix_010, ridgeSupport416_suffix_011, ridgeSupport416_suffix_012, ridgeSupport416_suffix_013, ridgeSupport416_suffix_014, ridgeSupport416_suffix_015, ridgeSupport416_suffix_016, ridgeSupport416_suffix_017, ridgeSupport416_suffix_018, ridgeSupport416_suffix_019, ridgeSupport416_suffix_020, ridgeSupport416_suffix_021, ridgeSupport416_suffix_022, ridgeSupport416_suffix_023, List.all_append, List.all_nil, ridgeSupport416_000_checked, ridgeSupport416_001_checked, ridgeSupport416_002_checked, ridgeSupport416_003_checked, ridgeSupport416_004_checked, ridgeSupport416_005_checked, ridgeSupport416_006_checked, ridgeSupport416_007_checked, ridgeSupport416_008_checked, ridgeSupport416_009_checked, ridgeSupport416_010_checked, ridgeSupport416_011_checked, ridgeSupport416_012_checked, ridgeSupport416_013_checked, ridgeSupport416_014_checked, ridgeSupport416_015_checked, ridgeSupport416_016_checked, ridgeSupport416_017_checked, ridgeSupport416_018_checked, ridgeSupport416_019_checked, ridgeSupport416_020_checked, ridgeSupport416_021_checked, ridgeSupport416_022_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase01
