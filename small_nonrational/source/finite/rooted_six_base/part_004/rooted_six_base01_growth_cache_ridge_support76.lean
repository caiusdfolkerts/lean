module
prelude
public import RootedSixBase01GrowthCacheRidgeSupport76Part000
public import RootedSixBase01GrowthCacheRidgeSupport76Part001
public import RootedSixBase01GrowthCacheRidgeSupport76Part002
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport76_suffix_decode_021 : PackedRawNatGrowth.readList 14 0 ridgeSupport76_rest_021 =
    (ridgeSupport76_suffix_021, ridgeSupport76_rest_021) := by rfl
theorem ridgeSupport76_suffix_decode_020 : PackedRawNatGrowth.readList 14 13 ridgeSupport76_rest_020 =
    (ridgeSupport76_suffix_020, ridgeSupport76_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 13 0
    ridgeSupport76_rest_020 ridgeSupport76_rest_021 ridgeSupport76_rest_021
    ridgeSupport76_020 ridgeSupport76_suffix_021 ridgeSupport76_020_decode ridgeSupport76_suffix_decode_021
theorem ridgeSupport76_suffix_decode_019 : PackedRawNatGrowth.readList 14 45 ridgeSupport76_rest_019 =
    (ridgeSupport76_suffix_019, ridgeSupport76_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 13
    ridgeSupport76_rest_019 ridgeSupport76_rest_020 ridgeSupport76_rest_021
    ridgeSupport76_019 ridgeSupport76_suffix_020 ridgeSupport76_019_decode ridgeSupport76_suffix_decode_020
theorem ridgeSupport76_suffix_decode_018 : PackedRawNatGrowth.readList 14 77 ridgeSupport76_rest_018 =
    (ridgeSupport76_suffix_018, ridgeSupport76_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 45
    ridgeSupport76_rest_018 ridgeSupport76_rest_019 ridgeSupport76_rest_021
    ridgeSupport76_018 ridgeSupport76_suffix_019 ridgeSupport76_018_decode ridgeSupport76_suffix_decode_019
theorem ridgeSupport76_suffix_decode_017 : PackedRawNatGrowth.readList 14 109 ridgeSupport76_rest_017 =
    (ridgeSupport76_suffix_017, ridgeSupport76_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 77
    ridgeSupport76_rest_017 ridgeSupport76_rest_018 ridgeSupport76_rest_021
    ridgeSupport76_017 ridgeSupport76_suffix_018 ridgeSupport76_017_decode ridgeSupport76_suffix_decode_018
theorem ridgeSupport76_suffix_decode_016 : PackedRawNatGrowth.readList 14 141 ridgeSupport76_rest_016 =
    (ridgeSupport76_suffix_016, ridgeSupport76_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 109
    ridgeSupport76_rest_016 ridgeSupport76_rest_017 ridgeSupport76_rest_021
    ridgeSupport76_016 ridgeSupport76_suffix_017 ridgeSupport76_016_decode ridgeSupport76_suffix_decode_017
theorem ridgeSupport76_suffix_decode_015 : PackedRawNatGrowth.readList 14 173 ridgeSupport76_rest_015 =
    (ridgeSupport76_suffix_015, ridgeSupport76_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 141
    ridgeSupport76_rest_015 ridgeSupport76_rest_016 ridgeSupport76_rest_021
    ridgeSupport76_015 ridgeSupport76_suffix_016 ridgeSupport76_015_decode ridgeSupport76_suffix_decode_016
theorem ridgeSupport76_suffix_decode_014 : PackedRawNatGrowth.readList 14 205 ridgeSupport76_rest_014 =
    (ridgeSupport76_suffix_014, ridgeSupport76_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 173
    ridgeSupport76_rest_014 ridgeSupport76_rest_015 ridgeSupport76_rest_021
    ridgeSupport76_014 ridgeSupport76_suffix_015 ridgeSupport76_014_decode ridgeSupport76_suffix_decode_015
theorem ridgeSupport76_suffix_decode_013 : PackedRawNatGrowth.readList 14 237 ridgeSupport76_rest_013 =
    (ridgeSupport76_suffix_013, ridgeSupport76_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 205
    ridgeSupport76_rest_013 ridgeSupport76_rest_014 ridgeSupport76_rest_021
    ridgeSupport76_013 ridgeSupport76_suffix_014 ridgeSupport76_013_decode ridgeSupport76_suffix_decode_014
theorem ridgeSupport76_suffix_decode_012 : PackedRawNatGrowth.readList 14 269 ridgeSupport76_rest_012 =
    (ridgeSupport76_suffix_012, ridgeSupport76_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 237
    ridgeSupport76_rest_012 ridgeSupport76_rest_013 ridgeSupport76_rest_021
    ridgeSupport76_012 ridgeSupport76_suffix_013 ridgeSupport76_012_decode ridgeSupport76_suffix_decode_013
theorem ridgeSupport76_suffix_decode_011 : PackedRawNatGrowth.readList 14 301 ridgeSupport76_rest_011 =
    (ridgeSupport76_suffix_011, ridgeSupport76_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 269
    ridgeSupport76_rest_011 ridgeSupport76_rest_012 ridgeSupport76_rest_021
    ridgeSupport76_011 ridgeSupport76_suffix_012 ridgeSupport76_011_decode ridgeSupport76_suffix_decode_012
theorem ridgeSupport76_suffix_decode_010 : PackedRawNatGrowth.readList 14 333 ridgeSupport76_rest_010 =
    (ridgeSupport76_suffix_010, ridgeSupport76_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 301
    ridgeSupport76_rest_010 ridgeSupport76_rest_011 ridgeSupport76_rest_021
    ridgeSupport76_010 ridgeSupport76_suffix_011 ridgeSupport76_010_decode ridgeSupport76_suffix_decode_011
theorem ridgeSupport76_suffix_decode_009 : PackedRawNatGrowth.readList 14 365 ridgeSupport76_rest_009 =
    (ridgeSupport76_suffix_009, ridgeSupport76_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 333
    ridgeSupport76_rest_009 ridgeSupport76_rest_010 ridgeSupport76_rest_021
    ridgeSupport76_009 ridgeSupport76_suffix_010 ridgeSupport76_009_decode ridgeSupport76_suffix_decode_010
theorem ridgeSupport76_suffix_decode_008 : PackedRawNatGrowth.readList 14 397 ridgeSupport76_rest_008 =
    (ridgeSupport76_suffix_008, ridgeSupport76_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 365
    ridgeSupport76_rest_008 ridgeSupport76_rest_009 ridgeSupport76_rest_021
    ridgeSupport76_008 ridgeSupport76_suffix_009 ridgeSupport76_008_decode ridgeSupport76_suffix_decode_009
theorem ridgeSupport76_suffix_decode_007 : PackedRawNatGrowth.readList 14 429 ridgeSupport76_rest_007 =
    (ridgeSupport76_suffix_007, ridgeSupport76_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 397
    ridgeSupport76_rest_007 ridgeSupport76_rest_008 ridgeSupport76_rest_021
    ridgeSupport76_007 ridgeSupport76_suffix_008 ridgeSupport76_007_decode ridgeSupport76_suffix_decode_008
theorem ridgeSupport76_suffix_decode_006 : PackedRawNatGrowth.readList 14 461 ridgeSupport76_rest_006 =
    (ridgeSupport76_suffix_006, ridgeSupport76_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 429
    ridgeSupport76_rest_006 ridgeSupport76_rest_007 ridgeSupport76_rest_021
    ridgeSupport76_006 ridgeSupport76_suffix_007 ridgeSupport76_006_decode ridgeSupport76_suffix_decode_007
theorem ridgeSupport76_suffix_decode_005 : PackedRawNatGrowth.readList 14 493 ridgeSupport76_rest_005 =
    (ridgeSupport76_suffix_005, ridgeSupport76_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 461
    ridgeSupport76_rest_005 ridgeSupport76_rest_006 ridgeSupport76_rest_021
    ridgeSupport76_005 ridgeSupport76_suffix_006 ridgeSupport76_005_decode ridgeSupport76_suffix_decode_006
theorem ridgeSupport76_suffix_decode_004 : PackedRawNatGrowth.readList 14 525 ridgeSupport76_rest_004 =
    (ridgeSupport76_suffix_004, ridgeSupport76_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 493
    ridgeSupport76_rest_004 ridgeSupport76_rest_005 ridgeSupport76_rest_021
    ridgeSupport76_004 ridgeSupport76_suffix_005 ridgeSupport76_004_decode ridgeSupport76_suffix_decode_005
theorem ridgeSupport76_suffix_decode_003 : PackedRawNatGrowth.readList 14 557 ridgeSupport76_rest_003 =
    (ridgeSupport76_suffix_003, ridgeSupport76_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 525
    ridgeSupport76_rest_003 ridgeSupport76_rest_004 ridgeSupport76_rest_021
    ridgeSupport76_003 ridgeSupport76_suffix_004 ridgeSupport76_003_decode ridgeSupport76_suffix_decode_004
theorem ridgeSupport76_suffix_decode_002 : PackedRawNatGrowth.readList 14 589 ridgeSupport76_rest_002 =
    (ridgeSupport76_suffix_002, ridgeSupport76_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 557
    ridgeSupport76_rest_002 ridgeSupport76_rest_003 ridgeSupport76_rest_021
    ridgeSupport76_002 ridgeSupport76_suffix_003 ridgeSupport76_002_decode ridgeSupport76_suffix_decode_003
theorem ridgeSupport76_suffix_decode_001 : PackedRawNatGrowth.readList 14 621 ridgeSupport76_rest_001 =
    (ridgeSupport76_suffix_001, ridgeSupport76_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 589
    ridgeSupport76_rest_001 ridgeSupport76_rest_002 ridgeSupport76_rest_021
    ridgeSupport76_001 ridgeSupport76_suffix_002 ridgeSupport76_001_decode ridgeSupport76_suffix_decode_002
theorem ridgeSupport76_suffix_decode_000 : PackedRawNatGrowth.readList 14 653 ridgeSupport76_rest_000 =
    (ridgeSupport76_suffix_000, ridgeSupport76_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 621
    ridgeSupport76_rest_000 ridgeSupport76_rest_001 ridgeSupport76_rest_021
    ridgeSupport76_000 ridgeSupport76_suffix_001 ridgeSupport76_000_decode ridgeSupport76_suffix_decode_001
theorem ridgeSupport76_eq : candidateRows 76 = ridgeSupport76_suffix_000 := by
  rw [ridgeSupport76_source]
  exact congrArg Prod.fst ridgeSupport76_suffix_decode_000
theorem ridgeTest_large_76 : ridgeTest 76 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport76_eq]
    simp only [ridgeSupport76_suffix_000, ridgeSupport76_suffix_001, ridgeSupport76_suffix_002, ridgeSupport76_suffix_003, ridgeSupport76_suffix_004, ridgeSupport76_suffix_005, ridgeSupport76_suffix_006, ridgeSupport76_suffix_007, ridgeSupport76_suffix_008, ridgeSupport76_suffix_009, ridgeSupport76_suffix_010, ridgeSupport76_suffix_011, ridgeSupport76_suffix_012, ridgeSupport76_suffix_013, ridgeSupport76_suffix_014, ridgeSupport76_suffix_015, ridgeSupport76_suffix_016, ridgeSupport76_suffix_017, ridgeSupport76_suffix_018, ridgeSupport76_suffix_019, ridgeSupport76_suffix_020, ridgeSupport76_suffix_021, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport76_000_mask, ridgeSupport76_001_mask, ridgeSupport76_002_mask, ridgeSupport76_003_mask, ridgeSupport76_004_mask, ridgeSupport76_005_mask, ridgeSupport76_006_mask, ridgeSupport76_007_mask, ridgeSupport76_008_mask, ridgeSupport76_009_mask, ridgeSupport76_010_mask, ridgeSupport76_011_mask, ridgeSupport76_012_mask, ridgeSupport76_013_mask, ridgeSupport76_014_mask, ridgeSupport76_015_mask, ridgeSupport76_016_mask, ridgeSupport76_017_mask, ridgeSupport76_018_mask, ridgeSupport76_019_mask, ridgeSupport76_020_mask]
    decide +kernel
  · rw [ridgeSupport76_eq]
    simp only [ridgeSupport76_suffix_000, ridgeSupport76_suffix_001, ridgeSupport76_suffix_002, ridgeSupport76_suffix_003, ridgeSupport76_suffix_004, ridgeSupport76_suffix_005, ridgeSupport76_suffix_006, ridgeSupport76_suffix_007, ridgeSupport76_suffix_008, ridgeSupport76_suffix_009, ridgeSupport76_suffix_010, ridgeSupport76_suffix_011, ridgeSupport76_suffix_012, ridgeSupport76_suffix_013, ridgeSupport76_suffix_014, ridgeSupport76_suffix_015, ridgeSupport76_suffix_016, ridgeSupport76_suffix_017, ridgeSupport76_suffix_018, ridgeSupport76_suffix_019, ridgeSupport76_suffix_020, ridgeSupport76_suffix_021, List.all_append, List.all_nil, ridgeSupport76_000_checked, ridgeSupport76_001_checked, ridgeSupport76_002_checked, ridgeSupport76_003_checked, ridgeSupport76_004_checked, ridgeSupport76_005_checked, ridgeSupport76_006_checked, ridgeSupport76_007_checked, ridgeSupport76_008_checked, ridgeSupport76_009_checked, ridgeSupport76_010_checked, ridgeSupport76_011_checked, ridgeSupport76_012_checked, ridgeSupport76_013_checked, ridgeSupport76_014_checked, ridgeSupport76_015_checked, ridgeSupport76_016_checked, ridgeSupport76_017_checked, ridgeSupport76_018_checked, ridgeSupport76_019_checked, ridgeSupport76_020_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase01
