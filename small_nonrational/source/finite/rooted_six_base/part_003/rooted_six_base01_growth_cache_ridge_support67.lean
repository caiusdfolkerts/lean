module
prelude
public import RootedSixBase01GrowthCacheRidgeSupport67Part000
public import RootedSixBase01GrowthCacheRidgeSupport67Part001
public import RootedSixBase01GrowthCacheRidgeSupport67Part002
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport67_suffix_decode_021 : PackedRawNatGrowth.readList 14 0 ridgeSupport67_rest_021 =
    (ridgeSupport67_suffix_021, ridgeSupport67_rest_021) := by rfl
theorem ridgeSupport67_suffix_decode_020 : PackedRawNatGrowth.readList 14 13 ridgeSupport67_rest_020 =
    (ridgeSupport67_suffix_020, ridgeSupport67_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 13 0
    ridgeSupport67_rest_020 ridgeSupport67_rest_021 ridgeSupport67_rest_021
    ridgeSupport67_020 ridgeSupport67_suffix_021 ridgeSupport67_020_decode ridgeSupport67_suffix_decode_021
theorem ridgeSupport67_suffix_decode_019 : PackedRawNatGrowth.readList 14 45 ridgeSupport67_rest_019 =
    (ridgeSupport67_suffix_019, ridgeSupport67_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 13
    ridgeSupport67_rest_019 ridgeSupport67_rest_020 ridgeSupport67_rest_021
    ridgeSupport67_019 ridgeSupport67_suffix_020 ridgeSupport67_019_decode ridgeSupport67_suffix_decode_020
theorem ridgeSupport67_suffix_decode_018 : PackedRawNatGrowth.readList 14 77 ridgeSupport67_rest_018 =
    (ridgeSupport67_suffix_018, ridgeSupport67_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 45
    ridgeSupport67_rest_018 ridgeSupport67_rest_019 ridgeSupport67_rest_021
    ridgeSupport67_018 ridgeSupport67_suffix_019 ridgeSupport67_018_decode ridgeSupport67_suffix_decode_019
theorem ridgeSupport67_suffix_decode_017 : PackedRawNatGrowth.readList 14 109 ridgeSupport67_rest_017 =
    (ridgeSupport67_suffix_017, ridgeSupport67_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 77
    ridgeSupport67_rest_017 ridgeSupport67_rest_018 ridgeSupport67_rest_021
    ridgeSupport67_017 ridgeSupport67_suffix_018 ridgeSupport67_017_decode ridgeSupport67_suffix_decode_018
theorem ridgeSupport67_suffix_decode_016 : PackedRawNatGrowth.readList 14 141 ridgeSupport67_rest_016 =
    (ridgeSupport67_suffix_016, ridgeSupport67_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 109
    ridgeSupport67_rest_016 ridgeSupport67_rest_017 ridgeSupport67_rest_021
    ridgeSupport67_016 ridgeSupport67_suffix_017 ridgeSupport67_016_decode ridgeSupport67_suffix_decode_017
theorem ridgeSupport67_suffix_decode_015 : PackedRawNatGrowth.readList 14 173 ridgeSupport67_rest_015 =
    (ridgeSupport67_suffix_015, ridgeSupport67_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 141
    ridgeSupport67_rest_015 ridgeSupport67_rest_016 ridgeSupport67_rest_021
    ridgeSupport67_015 ridgeSupport67_suffix_016 ridgeSupport67_015_decode ridgeSupport67_suffix_decode_016
theorem ridgeSupport67_suffix_decode_014 : PackedRawNatGrowth.readList 14 205 ridgeSupport67_rest_014 =
    (ridgeSupport67_suffix_014, ridgeSupport67_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 173
    ridgeSupport67_rest_014 ridgeSupport67_rest_015 ridgeSupport67_rest_021
    ridgeSupport67_014 ridgeSupport67_suffix_015 ridgeSupport67_014_decode ridgeSupport67_suffix_decode_015
theorem ridgeSupport67_suffix_decode_013 : PackedRawNatGrowth.readList 14 237 ridgeSupport67_rest_013 =
    (ridgeSupport67_suffix_013, ridgeSupport67_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 205
    ridgeSupport67_rest_013 ridgeSupport67_rest_014 ridgeSupport67_rest_021
    ridgeSupport67_013 ridgeSupport67_suffix_014 ridgeSupport67_013_decode ridgeSupport67_suffix_decode_014
theorem ridgeSupport67_suffix_decode_012 : PackedRawNatGrowth.readList 14 269 ridgeSupport67_rest_012 =
    (ridgeSupport67_suffix_012, ridgeSupport67_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 237
    ridgeSupport67_rest_012 ridgeSupport67_rest_013 ridgeSupport67_rest_021
    ridgeSupport67_012 ridgeSupport67_suffix_013 ridgeSupport67_012_decode ridgeSupport67_suffix_decode_013
theorem ridgeSupport67_suffix_decode_011 : PackedRawNatGrowth.readList 14 301 ridgeSupport67_rest_011 =
    (ridgeSupport67_suffix_011, ridgeSupport67_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 269
    ridgeSupport67_rest_011 ridgeSupport67_rest_012 ridgeSupport67_rest_021
    ridgeSupport67_011 ridgeSupport67_suffix_012 ridgeSupport67_011_decode ridgeSupport67_suffix_decode_012
theorem ridgeSupport67_suffix_decode_010 : PackedRawNatGrowth.readList 14 333 ridgeSupport67_rest_010 =
    (ridgeSupport67_suffix_010, ridgeSupport67_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 301
    ridgeSupport67_rest_010 ridgeSupport67_rest_011 ridgeSupport67_rest_021
    ridgeSupport67_010 ridgeSupport67_suffix_011 ridgeSupport67_010_decode ridgeSupport67_suffix_decode_011
theorem ridgeSupport67_suffix_decode_009 : PackedRawNatGrowth.readList 14 365 ridgeSupport67_rest_009 =
    (ridgeSupport67_suffix_009, ridgeSupport67_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 333
    ridgeSupport67_rest_009 ridgeSupport67_rest_010 ridgeSupport67_rest_021
    ridgeSupport67_009 ridgeSupport67_suffix_010 ridgeSupport67_009_decode ridgeSupport67_suffix_decode_010
theorem ridgeSupport67_suffix_decode_008 : PackedRawNatGrowth.readList 14 397 ridgeSupport67_rest_008 =
    (ridgeSupport67_suffix_008, ridgeSupport67_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 365
    ridgeSupport67_rest_008 ridgeSupport67_rest_009 ridgeSupport67_rest_021
    ridgeSupport67_008 ridgeSupport67_suffix_009 ridgeSupport67_008_decode ridgeSupport67_suffix_decode_009
theorem ridgeSupport67_suffix_decode_007 : PackedRawNatGrowth.readList 14 429 ridgeSupport67_rest_007 =
    (ridgeSupport67_suffix_007, ridgeSupport67_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 397
    ridgeSupport67_rest_007 ridgeSupport67_rest_008 ridgeSupport67_rest_021
    ridgeSupport67_007 ridgeSupport67_suffix_008 ridgeSupport67_007_decode ridgeSupport67_suffix_decode_008
theorem ridgeSupport67_suffix_decode_006 : PackedRawNatGrowth.readList 14 461 ridgeSupport67_rest_006 =
    (ridgeSupport67_suffix_006, ridgeSupport67_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 429
    ridgeSupport67_rest_006 ridgeSupport67_rest_007 ridgeSupport67_rest_021
    ridgeSupport67_006 ridgeSupport67_suffix_007 ridgeSupport67_006_decode ridgeSupport67_suffix_decode_007
theorem ridgeSupport67_suffix_decode_005 : PackedRawNatGrowth.readList 14 493 ridgeSupport67_rest_005 =
    (ridgeSupport67_suffix_005, ridgeSupport67_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 461
    ridgeSupport67_rest_005 ridgeSupport67_rest_006 ridgeSupport67_rest_021
    ridgeSupport67_005 ridgeSupport67_suffix_006 ridgeSupport67_005_decode ridgeSupport67_suffix_decode_006
theorem ridgeSupport67_suffix_decode_004 : PackedRawNatGrowth.readList 14 525 ridgeSupport67_rest_004 =
    (ridgeSupport67_suffix_004, ridgeSupport67_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 493
    ridgeSupport67_rest_004 ridgeSupport67_rest_005 ridgeSupport67_rest_021
    ridgeSupport67_004 ridgeSupport67_suffix_005 ridgeSupport67_004_decode ridgeSupport67_suffix_decode_005
theorem ridgeSupport67_suffix_decode_003 : PackedRawNatGrowth.readList 14 557 ridgeSupport67_rest_003 =
    (ridgeSupport67_suffix_003, ridgeSupport67_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 525
    ridgeSupport67_rest_003 ridgeSupport67_rest_004 ridgeSupport67_rest_021
    ridgeSupport67_003 ridgeSupport67_suffix_004 ridgeSupport67_003_decode ridgeSupport67_suffix_decode_004
theorem ridgeSupport67_suffix_decode_002 : PackedRawNatGrowth.readList 14 589 ridgeSupport67_rest_002 =
    (ridgeSupport67_suffix_002, ridgeSupport67_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 557
    ridgeSupport67_rest_002 ridgeSupport67_rest_003 ridgeSupport67_rest_021
    ridgeSupport67_002 ridgeSupport67_suffix_003 ridgeSupport67_002_decode ridgeSupport67_suffix_decode_003
theorem ridgeSupport67_suffix_decode_001 : PackedRawNatGrowth.readList 14 621 ridgeSupport67_rest_001 =
    (ridgeSupport67_suffix_001, ridgeSupport67_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 589
    ridgeSupport67_rest_001 ridgeSupport67_rest_002 ridgeSupport67_rest_021
    ridgeSupport67_001 ridgeSupport67_suffix_002 ridgeSupport67_001_decode ridgeSupport67_suffix_decode_002
theorem ridgeSupport67_suffix_decode_000 : PackedRawNatGrowth.readList 14 653 ridgeSupport67_rest_000 =
    (ridgeSupport67_suffix_000, ridgeSupport67_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 621
    ridgeSupport67_rest_000 ridgeSupport67_rest_001 ridgeSupport67_rest_021
    ridgeSupport67_000 ridgeSupport67_suffix_001 ridgeSupport67_000_decode ridgeSupport67_suffix_decode_001
theorem ridgeSupport67_eq : candidateRows 67 = ridgeSupport67_suffix_000 := by
  rw [ridgeSupport67_source]
  exact congrArg Prod.fst ridgeSupport67_suffix_decode_000
theorem ridgeTest_large_67 : ridgeTest 67 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport67_eq]
    simp only [ridgeSupport67_suffix_000, ridgeSupport67_suffix_001, ridgeSupport67_suffix_002, ridgeSupport67_suffix_003, ridgeSupport67_suffix_004, ridgeSupport67_suffix_005, ridgeSupport67_suffix_006, ridgeSupport67_suffix_007, ridgeSupport67_suffix_008, ridgeSupport67_suffix_009, ridgeSupport67_suffix_010, ridgeSupport67_suffix_011, ridgeSupport67_suffix_012, ridgeSupport67_suffix_013, ridgeSupport67_suffix_014, ridgeSupport67_suffix_015, ridgeSupport67_suffix_016, ridgeSupport67_suffix_017, ridgeSupport67_suffix_018, ridgeSupport67_suffix_019, ridgeSupport67_suffix_020, ridgeSupport67_suffix_021, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport67_000_mask, ridgeSupport67_001_mask, ridgeSupport67_002_mask, ridgeSupport67_003_mask, ridgeSupport67_004_mask, ridgeSupport67_005_mask, ridgeSupport67_006_mask, ridgeSupport67_007_mask, ridgeSupport67_008_mask, ridgeSupport67_009_mask, ridgeSupport67_010_mask, ridgeSupport67_011_mask, ridgeSupport67_012_mask, ridgeSupport67_013_mask, ridgeSupport67_014_mask, ridgeSupport67_015_mask, ridgeSupport67_016_mask, ridgeSupport67_017_mask, ridgeSupport67_018_mask, ridgeSupport67_019_mask, ridgeSupport67_020_mask]
    decide +kernel
  · rw [ridgeSupport67_eq]
    simp only [ridgeSupport67_suffix_000, ridgeSupport67_suffix_001, ridgeSupport67_suffix_002, ridgeSupport67_suffix_003, ridgeSupport67_suffix_004, ridgeSupport67_suffix_005, ridgeSupport67_suffix_006, ridgeSupport67_suffix_007, ridgeSupport67_suffix_008, ridgeSupport67_suffix_009, ridgeSupport67_suffix_010, ridgeSupport67_suffix_011, ridgeSupport67_suffix_012, ridgeSupport67_suffix_013, ridgeSupport67_suffix_014, ridgeSupport67_suffix_015, ridgeSupport67_suffix_016, ridgeSupport67_suffix_017, ridgeSupport67_suffix_018, ridgeSupport67_suffix_019, ridgeSupport67_suffix_020, ridgeSupport67_suffix_021, List.all_append, List.all_nil, ridgeSupport67_000_checked, ridgeSupport67_001_checked, ridgeSupport67_002_checked, ridgeSupport67_003_checked, ridgeSupport67_004_checked, ridgeSupport67_005_checked, ridgeSupport67_006_checked, ridgeSupport67_007_checked, ridgeSupport67_008_checked, ridgeSupport67_009_checked, ridgeSupport67_010_checked, ridgeSupport67_011_checked, ridgeSupport67_012_checked, ridgeSupport67_013_checked, ridgeSupport67_014_checked, ridgeSupport67_015_checked, ridgeSupport67_016_checked, ridgeSupport67_017_checked, ridgeSupport67_018_checked, ridgeSupport67_019_checked, ridgeSupport67_020_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase01
