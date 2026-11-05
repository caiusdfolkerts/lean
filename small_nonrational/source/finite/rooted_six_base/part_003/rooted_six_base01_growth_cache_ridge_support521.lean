module
prelude
public import RootedSixBase01GrowthCacheRidgeSupport521Part000
public import RootedSixBase01GrowthCacheRidgeSupport521Part001
public import RootedSixBase01GrowthCacheRidgeSupport521Part002
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport521_suffix_decode_021 : PackedRawNatGrowth.readList 14 0 ridgeSupport521_rest_021 =
    (ridgeSupport521_suffix_021, ridgeSupport521_rest_021) := by rfl
theorem ridgeSupport521_suffix_decode_020 : PackedRawNatGrowth.readList 14 13 ridgeSupport521_rest_020 =
    (ridgeSupport521_suffix_020, ridgeSupport521_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 13 0
    ridgeSupport521_rest_020 ridgeSupport521_rest_021 ridgeSupport521_rest_021
    ridgeSupport521_020 ridgeSupport521_suffix_021 ridgeSupport521_020_decode ridgeSupport521_suffix_decode_021
theorem ridgeSupport521_suffix_decode_019 : PackedRawNatGrowth.readList 14 45 ridgeSupport521_rest_019 =
    (ridgeSupport521_suffix_019, ridgeSupport521_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 13
    ridgeSupport521_rest_019 ridgeSupport521_rest_020 ridgeSupport521_rest_021
    ridgeSupport521_019 ridgeSupport521_suffix_020 ridgeSupport521_019_decode ridgeSupport521_suffix_decode_020
theorem ridgeSupport521_suffix_decode_018 : PackedRawNatGrowth.readList 14 77 ridgeSupport521_rest_018 =
    (ridgeSupport521_suffix_018, ridgeSupport521_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 45
    ridgeSupport521_rest_018 ridgeSupport521_rest_019 ridgeSupport521_rest_021
    ridgeSupport521_018 ridgeSupport521_suffix_019 ridgeSupport521_018_decode ridgeSupport521_suffix_decode_019
theorem ridgeSupport521_suffix_decode_017 : PackedRawNatGrowth.readList 14 109 ridgeSupport521_rest_017 =
    (ridgeSupport521_suffix_017, ridgeSupport521_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 77
    ridgeSupport521_rest_017 ridgeSupport521_rest_018 ridgeSupport521_rest_021
    ridgeSupport521_017 ridgeSupport521_suffix_018 ridgeSupport521_017_decode ridgeSupport521_suffix_decode_018
theorem ridgeSupport521_suffix_decode_016 : PackedRawNatGrowth.readList 14 141 ridgeSupport521_rest_016 =
    (ridgeSupport521_suffix_016, ridgeSupport521_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 109
    ridgeSupport521_rest_016 ridgeSupport521_rest_017 ridgeSupport521_rest_021
    ridgeSupport521_016 ridgeSupport521_suffix_017 ridgeSupport521_016_decode ridgeSupport521_suffix_decode_017
theorem ridgeSupport521_suffix_decode_015 : PackedRawNatGrowth.readList 14 173 ridgeSupport521_rest_015 =
    (ridgeSupport521_suffix_015, ridgeSupport521_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 141
    ridgeSupport521_rest_015 ridgeSupport521_rest_016 ridgeSupport521_rest_021
    ridgeSupport521_015 ridgeSupport521_suffix_016 ridgeSupport521_015_decode ridgeSupport521_suffix_decode_016
theorem ridgeSupport521_suffix_decode_014 : PackedRawNatGrowth.readList 14 205 ridgeSupport521_rest_014 =
    (ridgeSupport521_suffix_014, ridgeSupport521_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 173
    ridgeSupport521_rest_014 ridgeSupport521_rest_015 ridgeSupport521_rest_021
    ridgeSupport521_014 ridgeSupport521_suffix_015 ridgeSupport521_014_decode ridgeSupport521_suffix_decode_015
theorem ridgeSupport521_suffix_decode_013 : PackedRawNatGrowth.readList 14 237 ridgeSupport521_rest_013 =
    (ridgeSupport521_suffix_013, ridgeSupport521_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 205
    ridgeSupport521_rest_013 ridgeSupport521_rest_014 ridgeSupport521_rest_021
    ridgeSupport521_013 ridgeSupport521_suffix_014 ridgeSupport521_013_decode ridgeSupport521_suffix_decode_014
theorem ridgeSupport521_suffix_decode_012 : PackedRawNatGrowth.readList 14 269 ridgeSupport521_rest_012 =
    (ridgeSupport521_suffix_012, ridgeSupport521_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 237
    ridgeSupport521_rest_012 ridgeSupport521_rest_013 ridgeSupport521_rest_021
    ridgeSupport521_012 ridgeSupport521_suffix_013 ridgeSupport521_012_decode ridgeSupport521_suffix_decode_013
theorem ridgeSupport521_suffix_decode_011 : PackedRawNatGrowth.readList 14 301 ridgeSupport521_rest_011 =
    (ridgeSupport521_suffix_011, ridgeSupport521_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 269
    ridgeSupport521_rest_011 ridgeSupport521_rest_012 ridgeSupport521_rest_021
    ridgeSupport521_011 ridgeSupport521_suffix_012 ridgeSupport521_011_decode ridgeSupport521_suffix_decode_012
theorem ridgeSupport521_suffix_decode_010 : PackedRawNatGrowth.readList 14 333 ridgeSupport521_rest_010 =
    (ridgeSupport521_suffix_010, ridgeSupport521_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 301
    ridgeSupport521_rest_010 ridgeSupport521_rest_011 ridgeSupport521_rest_021
    ridgeSupport521_010 ridgeSupport521_suffix_011 ridgeSupport521_010_decode ridgeSupport521_suffix_decode_011
theorem ridgeSupport521_suffix_decode_009 : PackedRawNatGrowth.readList 14 365 ridgeSupport521_rest_009 =
    (ridgeSupport521_suffix_009, ridgeSupport521_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 333
    ridgeSupport521_rest_009 ridgeSupport521_rest_010 ridgeSupport521_rest_021
    ridgeSupport521_009 ridgeSupport521_suffix_010 ridgeSupport521_009_decode ridgeSupport521_suffix_decode_010
theorem ridgeSupport521_suffix_decode_008 : PackedRawNatGrowth.readList 14 397 ridgeSupport521_rest_008 =
    (ridgeSupport521_suffix_008, ridgeSupport521_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 365
    ridgeSupport521_rest_008 ridgeSupport521_rest_009 ridgeSupport521_rest_021
    ridgeSupport521_008 ridgeSupport521_suffix_009 ridgeSupport521_008_decode ridgeSupport521_suffix_decode_009
theorem ridgeSupport521_suffix_decode_007 : PackedRawNatGrowth.readList 14 429 ridgeSupport521_rest_007 =
    (ridgeSupport521_suffix_007, ridgeSupport521_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 397
    ridgeSupport521_rest_007 ridgeSupport521_rest_008 ridgeSupport521_rest_021
    ridgeSupport521_007 ridgeSupport521_suffix_008 ridgeSupport521_007_decode ridgeSupport521_suffix_decode_008
theorem ridgeSupport521_suffix_decode_006 : PackedRawNatGrowth.readList 14 461 ridgeSupport521_rest_006 =
    (ridgeSupport521_suffix_006, ridgeSupport521_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 429
    ridgeSupport521_rest_006 ridgeSupport521_rest_007 ridgeSupport521_rest_021
    ridgeSupport521_006 ridgeSupport521_suffix_007 ridgeSupport521_006_decode ridgeSupport521_suffix_decode_007
theorem ridgeSupport521_suffix_decode_005 : PackedRawNatGrowth.readList 14 493 ridgeSupport521_rest_005 =
    (ridgeSupport521_suffix_005, ridgeSupport521_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 461
    ridgeSupport521_rest_005 ridgeSupport521_rest_006 ridgeSupport521_rest_021
    ridgeSupport521_005 ridgeSupport521_suffix_006 ridgeSupport521_005_decode ridgeSupport521_suffix_decode_006
theorem ridgeSupport521_suffix_decode_004 : PackedRawNatGrowth.readList 14 525 ridgeSupport521_rest_004 =
    (ridgeSupport521_suffix_004, ridgeSupport521_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 493
    ridgeSupport521_rest_004 ridgeSupport521_rest_005 ridgeSupport521_rest_021
    ridgeSupport521_004 ridgeSupport521_suffix_005 ridgeSupport521_004_decode ridgeSupport521_suffix_decode_005
theorem ridgeSupport521_suffix_decode_003 : PackedRawNatGrowth.readList 14 557 ridgeSupport521_rest_003 =
    (ridgeSupport521_suffix_003, ridgeSupport521_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 525
    ridgeSupport521_rest_003 ridgeSupport521_rest_004 ridgeSupport521_rest_021
    ridgeSupport521_003 ridgeSupport521_suffix_004 ridgeSupport521_003_decode ridgeSupport521_suffix_decode_004
theorem ridgeSupport521_suffix_decode_002 : PackedRawNatGrowth.readList 14 589 ridgeSupport521_rest_002 =
    (ridgeSupport521_suffix_002, ridgeSupport521_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 557
    ridgeSupport521_rest_002 ridgeSupport521_rest_003 ridgeSupport521_rest_021
    ridgeSupport521_002 ridgeSupport521_suffix_003 ridgeSupport521_002_decode ridgeSupport521_suffix_decode_003
theorem ridgeSupport521_suffix_decode_001 : PackedRawNatGrowth.readList 14 621 ridgeSupport521_rest_001 =
    (ridgeSupport521_suffix_001, ridgeSupport521_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 589
    ridgeSupport521_rest_001 ridgeSupport521_rest_002 ridgeSupport521_rest_021
    ridgeSupport521_001 ridgeSupport521_suffix_002 ridgeSupport521_001_decode ridgeSupport521_suffix_decode_002
theorem ridgeSupport521_suffix_decode_000 : PackedRawNatGrowth.readList 14 653 ridgeSupport521_rest_000 =
    (ridgeSupport521_suffix_000, ridgeSupport521_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 621
    ridgeSupport521_rest_000 ridgeSupport521_rest_001 ridgeSupport521_rest_021
    ridgeSupport521_000 ridgeSupport521_suffix_001 ridgeSupport521_000_decode ridgeSupport521_suffix_decode_001
theorem ridgeSupport521_eq : candidateRows 521 = ridgeSupport521_suffix_000 := by
  rw [ridgeSupport521_source]
  exact congrArg Prod.fst ridgeSupport521_suffix_decode_000
theorem ridgeTest_large_521 : ridgeTest 521 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport521_eq]
    simp only [ridgeSupport521_suffix_000, ridgeSupport521_suffix_001, ridgeSupport521_suffix_002, ridgeSupport521_suffix_003, ridgeSupport521_suffix_004, ridgeSupport521_suffix_005, ridgeSupport521_suffix_006, ridgeSupport521_suffix_007, ridgeSupport521_suffix_008, ridgeSupport521_suffix_009, ridgeSupport521_suffix_010, ridgeSupport521_suffix_011, ridgeSupport521_suffix_012, ridgeSupport521_suffix_013, ridgeSupport521_suffix_014, ridgeSupport521_suffix_015, ridgeSupport521_suffix_016, ridgeSupport521_suffix_017, ridgeSupport521_suffix_018, ridgeSupport521_suffix_019, ridgeSupport521_suffix_020, ridgeSupport521_suffix_021, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport521_000_mask, ridgeSupport521_001_mask, ridgeSupport521_002_mask, ridgeSupport521_003_mask, ridgeSupport521_004_mask, ridgeSupport521_005_mask, ridgeSupport521_006_mask, ridgeSupport521_007_mask, ridgeSupport521_008_mask, ridgeSupport521_009_mask, ridgeSupport521_010_mask, ridgeSupport521_011_mask, ridgeSupport521_012_mask, ridgeSupport521_013_mask, ridgeSupport521_014_mask, ridgeSupport521_015_mask, ridgeSupport521_016_mask, ridgeSupport521_017_mask, ridgeSupport521_018_mask, ridgeSupport521_019_mask, ridgeSupport521_020_mask]
    decide +kernel
  · rw [ridgeSupport521_eq]
    simp only [ridgeSupport521_suffix_000, ridgeSupport521_suffix_001, ridgeSupport521_suffix_002, ridgeSupport521_suffix_003, ridgeSupport521_suffix_004, ridgeSupport521_suffix_005, ridgeSupport521_suffix_006, ridgeSupport521_suffix_007, ridgeSupport521_suffix_008, ridgeSupport521_suffix_009, ridgeSupport521_suffix_010, ridgeSupport521_suffix_011, ridgeSupport521_suffix_012, ridgeSupport521_suffix_013, ridgeSupport521_suffix_014, ridgeSupport521_suffix_015, ridgeSupport521_suffix_016, ridgeSupport521_suffix_017, ridgeSupport521_suffix_018, ridgeSupport521_suffix_019, ridgeSupport521_suffix_020, ridgeSupport521_suffix_021, List.all_append, List.all_nil, ridgeSupport521_000_checked, ridgeSupport521_001_checked, ridgeSupport521_002_checked, ridgeSupport521_003_checked, ridgeSupport521_004_checked, ridgeSupport521_005_checked, ridgeSupport521_006_checked, ridgeSupport521_007_checked, ridgeSupport521_008_checked, ridgeSupport521_009_checked, ridgeSupport521_010_checked, ridgeSupport521_011_checked, ridgeSupport521_012_checked, ridgeSupport521_013_checked, ridgeSupport521_014_checked, ridgeSupport521_015_checked, ridgeSupport521_016_checked, ridgeSupport521_017_checked, ridgeSupport521_018_checked, ridgeSupport521_019_checked, ridgeSupport521_020_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase01
