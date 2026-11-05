module
prelude
public import RootedSixBase01GrowthCacheRidgeSupport532Part000
public import RootedSixBase01GrowthCacheRidgeSupport532Part001
public import RootedSixBase01GrowthCacheRidgeSupport532Part002
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport532_suffix_decode_021 : PackedRawNatGrowth.readList 14 0 ridgeSupport532_rest_021 =
    (ridgeSupport532_suffix_021, ridgeSupport532_rest_021) := by rfl
theorem ridgeSupport532_suffix_decode_020 : PackedRawNatGrowth.readList 14 13 ridgeSupport532_rest_020 =
    (ridgeSupport532_suffix_020, ridgeSupport532_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 13 0
    ridgeSupport532_rest_020 ridgeSupport532_rest_021 ridgeSupport532_rest_021
    ridgeSupport532_020 ridgeSupport532_suffix_021 ridgeSupport532_020_decode ridgeSupport532_suffix_decode_021
theorem ridgeSupport532_suffix_decode_019 : PackedRawNatGrowth.readList 14 45 ridgeSupport532_rest_019 =
    (ridgeSupport532_suffix_019, ridgeSupport532_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 13
    ridgeSupport532_rest_019 ridgeSupport532_rest_020 ridgeSupport532_rest_021
    ridgeSupport532_019 ridgeSupport532_suffix_020 ridgeSupport532_019_decode ridgeSupport532_suffix_decode_020
theorem ridgeSupport532_suffix_decode_018 : PackedRawNatGrowth.readList 14 77 ridgeSupport532_rest_018 =
    (ridgeSupport532_suffix_018, ridgeSupport532_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 45
    ridgeSupport532_rest_018 ridgeSupport532_rest_019 ridgeSupport532_rest_021
    ridgeSupport532_018 ridgeSupport532_suffix_019 ridgeSupport532_018_decode ridgeSupport532_suffix_decode_019
theorem ridgeSupport532_suffix_decode_017 : PackedRawNatGrowth.readList 14 109 ridgeSupport532_rest_017 =
    (ridgeSupport532_suffix_017, ridgeSupport532_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 77
    ridgeSupport532_rest_017 ridgeSupport532_rest_018 ridgeSupport532_rest_021
    ridgeSupport532_017 ridgeSupport532_suffix_018 ridgeSupport532_017_decode ridgeSupport532_suffix_decode_018
theorem ridgeSupport532_suffix_decode_016 : PackedRawNatGrowth.readList 14 141 ridgeSupport532_rest_016 =
    (ridgeSupport532_suffix_016, ridgeSupport532_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 109
    ridgeSupport532_rest_016 ridgeSupport532_rest_017 ridgeSupport532_rest_021
    ridgeSupport532_016 ridgeSupport532_suffix_017 ridgeSupport532_016_decode ridgeSupport532_suffix_decode_017
theorem ridgeSupport532_suffix_decode_015 : PackedRawNatGrowth.readList 14 173 ridgeSupport532_rest_015 =
    (ridgeSupport532_suffix_015, ridgeSupport532_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 141
    ridgeSupport532_rest_015 ridgeSupport532_rest_016 ridgeSupport532_rest_021
    ridgeSupport532_015 ridgeSupport532_suffix_016 ridgeSupport532_015_decode ridgeSupport532_suffix_decode_016
theorem ridgeSupport532_suffix_decode_014 : PackedRawNatGrowth.readList 14 205 ridgeSupport532_rest_014 =
    (ridgeSupport532_suffix_014, ridgeSupport532_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 173
    ridgeSupport532_rest_014 ridgeSupport532_rest_015 ridgeSupport532_rest_021
    ridgeSupport532_014 ridgeSupport532_suffix_015 ridgeSupport532_014_decode ridgeSupport532_suffix_decode_015
theorem ridgeSupport532_suffix_decode_013 : PackedRawNatGrowth.readList 14 237 ridgeSupport532_rest_013 =
    (ridgeSupport532_suffix_013, ridgeSupport532_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 205
    ridgeSupport532_rest_013 ridgeSupport532_rest_014 ridgeSupport532_rest_021
    ridgeSupport532_013 ridgeSupport532_suffix_014 ridgeSupport532_013_decode ridgeSupport532_suffix_decode_014
theorem ridgeSupport532_suffix_decode_012 : PackedRawNatGrowth.readList 14 269 ridgeSupport532_rest_012 =
    (ridgeSupport532_suffix_012, ridgeSupport532_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 237
    ridgeSupport532_rest_012 ridgeSupport532_rest_013 ridgeSupport532_rest_021
    ridgeSupport532_012 ridgeSupport532_suffix_013 ridgeSupport532_012_decode ridgeSupport532_suffix_decode_013
theorem ridgeSupport532_suffix_decode_011 : PackedRawNatGrowth.readList 14 301 ridgeSupport532_rest_011 =
    (ridgeSupport532_suffix_011, ridgeSupport532_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 269
    ridgeSupport532_rest_011 ridgeSupport532_rest_012 ridgeSupport532_rest_021
    ridgeSupport532_011 ridgeSupport532_suffix_012 ridgeSupport532_011_decode ridgeSupport532_suffix_decode_012
theorem ridgeSupport532_suffix_decode_010 : PackedRawNatGrowth.readList 14 333 ridgeSupport532_rest_010 =
    (ridgeSupport532_suffix_010, ridgeSupport532_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 301
    ridgeSupport532_rest_010 ridgeSupport532_rest_011 ridgeSupport532_rest_021
    ridgeSupport532_010 ridgeSupport532_suffix_011 ridgeSupport532_010_decode ridgeSupport532_suffix_decode_011
theorem ridgeSupport532_suffix_decode_009 : PackedRawNatGrowth.readList 14 365 ridgeSupport532_rest_009 =
    (ridgeSupport532_suffix_009, ridgeSupport532_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 333
    ridgeSupport532_rest_009 ridgeSupport532_rest_010 ridgeSupport532_rest_021
    ridgeSupport532_009 ridgeSupport532_suffix_010 ridgeSupport532_009_decode ridgeSupport532_suffix_decode_010
theorem ridgeSupport532_suffix_decode_008 : PackedRawNatGrowth.readList 14 397 ridgeSupport532_rest_008 =
    (ridgeSupport532_suffix_008, ridgeSupport532_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 365
    ridgeSupport532_rest_008 ridgeSupport532_rest_009 ridgeSupport532_rest_021
    ridgeSupport532_008 ridgeSupport532_suffix_009 ridgeSupport532_008_decode ridgeSupport532_suffix_decode_009
theorem ridgeSupport532_suffix_decode_007 : PackedRawNatGrowth.readList 14 429 ridgeSupport532_rest_007 =
    (ridgeSupport532_suffix_007, ridgeSupport532_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 397
    ridgeSupport532_rest_007 ridgeSupport532_rest_008 ridgeSupport532_rest_021
    ridgeSupport532_007 ridgeSupport532_suffix_008 ridgeSupport532_007_decode ridgeSupport532_suffix_decode_008
theorem ridgeSupport532_suffix_decode_006 : PackedRawNatGrowth.readList 14 461 ridgeSupport532_rest_006 =
    (ridgeSupport532_suffix_006, ridgeSupport532_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 429
    ridgeSupport532_rest_006 ridgeSupport532_rest_007 ridgeSupport532_rest_021
    ridgeSupport532_006 ridgeSupport532_suffix_007 ridgeSupport532_006_decode ridgeSupport532_suffix_decode_007
theorem ridgeSupport532_suffix_decode_005 : PackedRawNatGrowth.readList 14 493 ridgeSupport532_rest_005 =
    (ridgeSupport532_suffix_005, ridgeSupport532_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 461
    ridgeSupport532_rest_005 ridgeSupport532_rest_006 ridgeSupport532_rest_021
    ridgeSupport532_005 ridgeSupport532_suffix_006 ridgeSupport532_005_decode ridgeSupport532_suffix_decode_006
theorem ridgeSupport532_suffix_decode_004 : PackedRawNatGrowth.readList 14 525 ridgeSupport532_rest_004 =
    (ridgeSupport532_suffix_004, ridgeSupport532_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 493
    ridgeSupport532_rest_004 ridgeSupport532_rest_005 ridgeSupport532_rest_021
    ridgeSupport532_004 ridgeSupport532_suffix_005 ridgeSupport532_004_decode ridgeSupport532_suffix_decode_005
theorem ridgeSupport532_suffix_decode_003 : PackedRawNatGrowth.readList 14 557 ridgeSupport532_rest_003 =
    (ridgeSupport532_suffix_003, ridgeSupport532_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 525
    ridgeSupport532_rest_003 ridgeSupport532_rest_004 ridgeSupport532_rest_021
    ridgeSupport532_003 ridgeSupport532_suffix_004 ridgeSupport532_003_decode ridgeSupport532_suffix_decode_004
theorem ridgeSupport532_suffix_decode_002 : PackedRawNatGrowth.readList 14 589 ridgeSupport532_rest_002 =
    (ridgeSupport532_suffix_002, ridgeSupport532_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 557
    ridgeSupport532_rest_002 ridgeSupport532_rest_003 ridgeSupport532_rest_021
    ridgeSupport532_002 ridgeSupport532_suffix_003 ridgeSupport532_002_decode ridgeSupport532_suffix_decode_003
theorem ridgeSupport532_suffix_decode_001 : PackedRawNatGrowth.readList 14 621 ridgeSupport532_rest_001 =
    (ridgeSupport532_suffix_001, ridgeSupport532_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 589
    ridgeSupport532_rest_001 ridgeSupport532_rest_002 ridgeSupport532_rest_021
    ridgeSupport532_001 ridgeSupport532_suffix_002 ridgeSupport532_001_decode ridgeSupport532_suffix_decode_002
theorem ridgeSupport532_suffix_decode_000 : PackedRawNatGrowth.readList 14 653 ridgeSupport532_rest_000 =
    (ridgeSupport532_suffix_000, ridgeSupport532_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 621
    ridgeSupport532_rest_000 ridgeSupport532_rest_001 ridgeSupport532_rest_021
    ridgeSupport532_000 ridgeSupport532_suffix_001 ridgeSupport532_000_decode ridgeSupport532_suffix_decode_001
theorem ridgeSupport532_eq : candidateRows 532 = ridgeSupport532_suffix_000 := by
  rw [ridgeSupport532_source]
  exact congrArg Prod.fst ridgeSupport532_suffix_decode_000
theorem ridgeTest_large_532 : ridgeTest 532 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport532_eq]
    simp only [ridgeSupport532_suffix_000, ridgeSupport532_suffix_001, ridgeSupport532_suffix_002, ridgeSupport532_suffix_003, ridgeSupport532_suffix_004, ridgeSupport532_suffix_005, ridgeSupport532_suffix_006, ridgeSupport532_suffix_007, ridgeSupport532_suffix_008, ridgeSupport532_suffix_009, ridgeSupport532_suffix_010, ridgeSupport532_suffix_011, ridgeSupport532_suffix_012, ridgeSupport532_suffix_013, ridgeSupport532_suffix_014, ridgeSupport532_suffix_015, ridgeSupport532_suffix_016, ridgeSupport532_suffix_017, ridgeSupport532_suffix_018, ridgeSupport532_suffix_019, ridgeSupport532_suffix_020, ridgeSupport532_suffix_021, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport532_000_mask, ridgeSupport532_001_mask, ridgeSupport532_002_mask, ridgeSupport532_003_mask, ridgeSupport532_004_mask, ridgeSupport532_005_mask, ridgeSupport532_006_mask, ridgeSupport532_007_mask, ridgeSupport532_008_mask, ridgeSupport532_009_mask, ridgeSupport532_010_mask, ridgeSupport532_011_mask, ridgeSupport532_012_mask, ridgeSupport532_013_mask, ridgeSupport532_014_mask, ridgeSupport532_015_mask, ridgeSupport532_016_mask, ridgeSupport532_017_mask, ridgeSupport532_018_mask, ridgeSupport532_019_mask, ridgeSupport532_020_mask]
    decide +kernel
  · rw [ridgeSupport532_eq]
    simp only [ridgeSupport532_suffix_000, ridgeSupport532_suffix_001, ridgeSupport532_suffix_002, ridgeSupport532_suffix_003, ridgeSupport532_suffix_004, ridgeSupport532_suffix_005, ridgeSupport532_suffix_006, ridgeSupport532_suffix_007, ridgeSupport532_suffix_008, ridgeSupport532_suffix_009, ridgeSupport532_suffix_010, ridgeSupport532_suffix_011, ridgeSupport532_suffix_012, ridgeSupport532_suffix_013, ridgeSupport532_suffix_014, ridgeSupport532_suffix_015, ridgeSupport532_suffix_016, ridgeSupport532_suffix_017, ridgeSupport532_suffix_018, ridgeSupport532_suffix_019, ridgeSupport532_suffix_020, ridgeSupport532_suffix_021, List.all_append, List.all_nil, ridgeSupport532_000_checked, ridgeSupport532_001_checked, ridgeSupport532_002_checked, ridgeSupport532_003_checked, ridgeSupport532_004_checked, ridgeSupport532_005_checked, ridgeSupport532_006_checked, ridgeSupport532_007_checked, ridgeSupport532_008_checked, ridgeSupport532_009_checked, ridgeSupport532_010_checked, ridgeSupport532_011_checked, ridgeSupport532_012_checked, ridgeSupport532_013_checked, ridgeSupport532_014_checked, ridgeSupport532_015_checked, ridgeSupport532_016_checked, ridgeSupport532_017_checked, ridgeSupport532_018_checked, ridgeSupport532_019_checked, ridgeSupport532_020_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase01
