module
prelude
public import RootedSixBase01GrowthCacheRidgeSupport352Part000
public import RootedSixBase01GrowthCacheRidgeSupport352Part001
public import RootedSixBase01GrowthCacheRidgeSupport352Part002
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport352_suffix_decode_023 : PackedRawNatGrowth.readList 14 0 ridgeSupport352_rest_023 =
    (ridgeSupport352_suffix_023, ridgeSupport352_rest_023) := by rfl
theorem ridgeSupport352_suffix_decode_022 : PackedRawNatGrowth.readList 14 15 ridgeSupport352_rest_022 =
    (ridgeSupport352_suffix_022, ridgeSupport352_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 15 0
    ridgeSupport352_rest_022 ridgeSupport352_rest_023 ridgeSupport352_rest_023
    ridgeSupport352_022 ridgeSupport352_suffix_023 ridgeSupport352_022_decode ridgeSupport352_suffix_decode_023
theorem ridgeSupport352_suffix_decode_021 : PackedRawNatGrowth.readList 14 47 ridgeSupport352_rest_021 =
    (ridgeSupport352_suffix_021, ridgeSupport352_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 15
    ridgeSupport352_rest_021 ridgeSupport352_rest_022 ridgeSupport352_rest_023
    ridgeSupport352_021 ridgeSupport352_suffix_022 ridgeSupport352_021_decode ridgeSupport352_suffix_decode_022
theorem ridgeSupport352_suffix_decode_020 : PackedRawNatGrowth.readList 14 79 ridgeSupport352_rest_020 =
    (ridgeSupport352_suffix_020, ridgeSupport352_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 47
    ridgeSupport352_rest_020 ridgeSupport352_rest_021 ridgeSupport352_rest_023
    ridgeSupport352_020 ridgeSupport352_suffix_021 ridgeSupport352_020_decode ridgeSupport352_suffix_decode_021
theorem ridgeSupport352_suffix_decode_019 : PackedRawNatGrowth.readList 14 111 ridgeSupport352_rest_019 =
    (ridgeSupport352_suffix_019, ridgeSupport352_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 79
    ridgeSupport352_rest_019 ridgeSupport352_rest_020 ridgeSupport352_rest_023
    ridgeSupport352_019 ridgeSupport352_suffix_020 ridgeSupport352_019_decode ridgeSupport352_suffix_decode_020
theorem ridgeSupport352_suffix_decode_018 : PackedRawNatGrowth.readList 14 143 ridgeSupport352_rest_018 =
    (ridgeSupport352_suffix_018, ridgeSupport352_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 111
    ridgeSupport352_rest_018 ridgeSupport352_rest_019 ridgeSupport352_rest_023
    ridgeSupport352_018 ridgeSupport352_suffix_019 ridgeSupport352_018_decode ridgeSupport352_suffix_decode_019
theorem ridgeSupport352_suffix_decode_017 : PackedRawNatGrowth.readList 14 175 ridgeSupport352_rest_017 =
    (ridgeSupport352_suffix_017, ridgeSupport352_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 143
    ridgeSupport352_rest_017 ridgeSupport352_rest_018 ridgeSupport352_rest_023
    ridgeSupport352_017 ridgeSupport352_suffix_018 ridgeSupport352_017_decode ridgeSupport352_suffix_decode_018
theorem ridgeSupport352_suffix_decode_016 : PackedRawNatGrowth.readList 14 207 ridgeSupport352_rest_016 =
    (ridgeSupport352_suffix_016, ridgeSupport352_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 175
    ridgeSupport352_rest_016 ridgeSupport352_rest_017 ridgeSupport352_rest_023
    ridgeSupport352_016 ridgeSupport352_suffix_017 ridgeSupport352_016_decode ridgeSupport352_suffix_decode_017
theorem ridgeSupport352_suffix_decode_015 : PackedRawNatGrowth.readList 14 239 ridgeSupport352_rest_015 =
    (ridgeSupport352_suffix_015, ridgeSupport352_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 207
    ridgeSupport352_rest_015 ridgeSupport352_rest_016 ridgeSupport352_rest_023
    ridgeSupport352_015 ridgeSupport352_suffix_016 ridgeSupport352_015_decode ridgeSupport352_suffix_decode_016
theorem ridgeSupport352_suffix_decode_014 : PackedRawNatGrowth.readList 14 271 ridgeSupport352_rest_014 =
    (ridgeSupport352_suffix_014, ridgeSupport352_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 239
    ridgeSupport352_rest_014 ridgeSupport352_rest_015 ridgeSupport352_rest_023
    ridgeSupport352_014 ridgeSupport352_suffix_015 ridgeSupport352_014_decode ridgeSupport352_suffix_decode_015
theorem ridgeSupport352_suffix_decode_013 : PackedRawNatGrowth.readList 14 303 ridgeSupport352_rest_013 =
    (ridgeSupport352_suffix_013, ridgeSupport352_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 271
    ridgeSupport352_rest_013 ridgeSupport352_rest_014 ridgeSupport352_rest_023
    ridgeSupport352_013 ridgeSupport352_suffix_014 ridgeSupport352_013_decode ridgeSupport352_suffix_decode_014
theorem ridgeSupport352_suffix_decode_012 : PackedRawNatGrowth.readList 14 335 ridgeSupport352_rest_012 =
    (ridgeSupport352_suffix_012, ridgeSupport352_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 303
    ridgeSupport352_rest_012 ridgeSupport352_rest_013 ridgeSupport352_rest_023
    ridgeSupport352_012 ridgeSupport352_suffix_013 ridgeSupport352_012_decode ridgeSupport352_suffix_decode_013
theorem ridgeSupport352_suffix_decode_011 : PackedRawNatGrowth.readList 14 367 ridgeSupport352_rest_011 =
    (ridgeSupport352_suffix_011, ridgeSupport352_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 335
    ridgeSupport352_rest_011 ridgeSupport352_rest_012 ridgeSupport352_rest_023
    ridgeSupport352_011 ridgeSupport352_suffix_012 ridgeSupport352_011_decode ridgeSupport352_suffix_decode_012
theorem ridgeSupport352_suffix_decode_010 : PackedRawNatGrowth.readList 14 399 ridgeSupport352_rest_010 =
    (ridgeSupport352_suffix_010, ridgeSupport352_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 367
    ridgeSupport352_rest_010 ridgeSupport352_rest_011 ridgeSupport352_rest_023
    ridgeSupport352_010 ridgeSupport352_suffix_011 ridgeSupport352_010_decode ridgeSupport352_suffix_decode_011
theorem ridgeSupport352_suffix_decode_009 : PackedRawNatGrowth.readList 14 431 ridgeSupport352_rest_009 =
    (ridgeSupport352_suffix_009, ridgeSupport352_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 399
    ridgeSupport352_rest_009 ridgeSupport352_rest_010 ridgeSupport352_rest_023
    ridgeSupport352_009 ridgeSupport352_suffix_010 ridgeSupport352_009_decode ridgeSupport352_suffix_decode_010
theorem ridgeSupport352_suffix_decode_008 : PackedRawNatGrowth.readList 14 463 ridgeSupport352_rest_008 =
    (ridgeSupport352_suffix_008, ridgeSupport352_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 431
    ridgeSupport352_rest_008 ridgeSupport352_rest_009 ridgeSupport352_rest_023
    ridgeSupport352_008 ridgeSupport352_suffix_009 ridgeSupport352_008_decode ridgeSupport352_suffix_decode_009
theorem ridgeSupport352_suffix_decode_007 : PackedRawNatGrowth.readList 14 495 ridgeSupport352_rest_007 =
    (ridgeSupport352_suffix_007, ridgeSupport352_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 463
    ridgeSupport352_rest_007 ridgeSupport352_rest_008 ridgeSupport352_rest_023
    ridgeSupport352_007 ridgeSupport352_suffix_008 ridgeSupport352_007_decode ridgeSupport352_suffix_decode_008
theorem ridgeSupport352_suffix_decode_006 : PackedRawNatGrowth.readList 14 527 ridgeSupport352_rest_006 =
    (ridgeSupport352_suffix_006, ridgeSupport352_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 495
    ridgeSupport352_rest_006 ridgeSupport352_rest_007 ridgeSupport352_rest_023
    ridgeSupport352_006 ridgeSupport352_suffix_007 ridgeSupport352_006_decode ridgeSupport352_suffix_decode_007
theorem ridgeSupport352_suffix_decode_005 : PackedRawNatGrowth.readList 14 559 ridgeSupport352_rest_005 =
    (ridgeSupport352_suffix_005, ridgeSupport352_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 527
    ridgeSupport352_rest_005 ridgeSupport352_rest_006 ridgeSupport352_rest_023
    ridgeSupport352_005 ridgeSupport352_suffix_006 ridgeSupport352_005_decode ridgeSupport352_suffix_decode_006
theorem ridgeSupport352_suffix_decode_004 : PackedRawNatGrowth.readList 14 591 ridgeSupport352_rest_004 =
    (ridgeSupport352_suffix_004, ridgeSupport352_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 559
    ridgeSupport352_rest_004 ridgeSupport352_rest_005 ridgeSupport352_rest_023
    ridgeSupport352_004 ridgeSupport352_suffix_005 ridgeSupport352_004_decode ridgeSupport352_suffix_decode_005
theorem ridgeSupport352_suffix_decode_003 : PackedRawNatGrowth.readList 14 623 ridgeSupport352_rest_003 =
    (ridgeSupport352_suffix_003, ridgeSupport352_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 591
    ridgeSupport352_rest_003 ridgeSupport352_rest_004 ridgeSupport352_rest_023
    ridgeSupport352_003 ridgeSupport352_suffix_004 ridgeSupport352_003_decode ridgeSupport352_suffix_decode_004
theorem ridgeSupport352_suffix_decode_002 : PackedRawNatGrowth.readList 14 655 ridgeSupport352_rest_002 =
    (ridgeSupport352_suffix_002, ridgeSupport352_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 623
    ridgeSupport352_rest_002 ridgeSupport352_rest_003 ridgeSupport352_rest_023
    ridgeSupport352_002 ridgeSupport352_suffix_003 ridgeSupport352_002_decode ridgeSupport352_suffix_decode_003
theorem ridgeSupport352_suffix_decode_001 : PackedRawNatGrowth.readList 14 687 ridgeSupport352_rest_001 =
    (ridgeSupport352_suffix_001, ridgeSupport352_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 655
    ridgeSupport352_rest_001 ridgeSupport352_rest_002 ridgeSupport352_rest_023
    ridgeSupport352_001 ridgeSupport352_suffix_002 ridgeSupport352_001_decode ridgeSupport352_suffix_decode_002
theorem ridgeSupport352_suffix_decode_000 : PackedRawNatGrowth.readList 14 719 ridgeSupport352_rest_000 =
    (ridgeSupport352_suffix_000, ridgeSupport352_rest_023) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 687
    ridgeSupport352_rest_000 ridgeSupport352_rest_001 ridgeSupport352_rest_023
    ridgeSupport352_000 ridgeSupport352_suffix_001 ridgeSupport352_000_decode ridgeSupport352_suffix_decode_001
theorem ridgeSupport352_eq : candidateRows 352 = ridgeSupport352_suffix_000 := by
  rw [ridgeSupport352_source]
  exact congrArg Prod.fst ridgeSupport352_suffix_decode_000
theorem ridgeTest_large_352 : ridgeTest 352 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport352_eq]
    simp only [ridgeSupport352_suffix_000, ridgeSupport352_suffix_001, ridgeSupport352_suffix_002, ridgeSupport352_suffix_003, ridgeSupport352_suffix_004, ridgeSupport352_suffix_005, ridgeSupport352_suffix_006, ridgeSupport352_suffix_007, ridgeSupport352_suffix_008, ridgeSupport352_suffix_009, ridgeSupport352_suffix_010, ridgeSupport352_suffix_011, ridgeSupport352_suffix_012, ridgeSupport352_suffix_013, ridgeSupport352_suffix_014, ridgeSupport352_suffix_015, ridgeSupport352_suffix_016, ridgeSupport352_suffix_017, ridgeSupport352_suffix_018, ridgeSupport352_suffix_019, ridgeSupport352_suffix_020, ridgeSupport352_suffix_021, ridgeSupport352_suffix_022, ridgeSupport352_suffix_023, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport352_000_mask, ridgeSupport352_001_mask, ridgeSupport352_002_mask, ridgeSupport352_003_mask, ridgeSupport352_004_mask, ridgeSupport352_005_mask, ridgeSupport352_006_mask, ridgeSupport352_007_mask, ridgeSupport352_008_mask, ridgeSupport352_009_mask, ridgeSupport352_010_mask, ridgeSupport352_011_mask, ridgeSupport352_012_mask, ridgeSupport352_013_mask, ridgeSupport352_014_mask, ridgeSupport352_015_mask, ridgeSupport352_016_mask, ridgeSupport352_017_mask, ridgeSupport352_018_mask, ridgeSupport352_019_mask, ridgeSupport352_020_mask, ridgeSupport352_021_mask, ridgeSupport352_022_mask]
    decide +kernel
  · rw [ridgeSupport352_eq]
    simp only [ridgeSupport352_suffix_000, ridgeSupport352_suffix_001, ridgeSupport352_suffix_002, ridgeSupport352_suffix_003, ridgeSupport352_suffix_004, ridgeSupport352_suffix_005, ridgeSupport352_suffix_006, ridgeSupport352_suffix_007, ridgeSupport352_suffix_008, ridgeSupport352_suffix_009, ridgeSupport352_suffix_010, ridgeSupport352_suffix_011, ridgeSupport352_suffix_012, ridgeSupport352_suffix_013, ridgeSupport352_suffix_014, ridgeSupport352_suffix_015, ridgeSupport352_suffix_016, ridgeSupport352_suffix_017, ridgeSupport352_suffix_018, ridgeSupport352_suffix_019, ridgeSupport352_suffix_020, ridgeSupport352_suffix_021, ridgeSupport352_suffix_022, ridgeSupport352_suffix_023, List.all_append, List.all_nil, ridgeSupport352_000_checked, ridgeSupport352_001_checked, ridgeSupport352_002_checked, ridgeSupport352_003_checked, ridgeSupport352_004_checked, ridgeSupport352_005_checked, ridgeSupport352_006_checked, ridgeSupport352_007_checked, ridgeSupport352_008_checked, ridgeSupport352_009_checked, ridgeSupport352_010_checked, ridgeSupport352_011_checked, ridgeSupport352_012_checked, ridgeSupport352_013_checked, ridgeSupport352_014_checked, ridgeSupport352_015_checked, ridgeSupport352_016_checked, ridgeSupport352_017_checked, ridgeSupport352_018_checked, ridgeSupport352_019_checked, ridgeSupport352_020_checked, ridgeSupport352_021_checked, ridgeSupport352_022_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase01
