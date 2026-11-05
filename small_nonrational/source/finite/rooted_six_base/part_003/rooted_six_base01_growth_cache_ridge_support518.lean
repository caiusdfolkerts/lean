module
prelude
public import RootedSixBase01GrowthCacheRidgeSupport518Part000
public import RootedSixBase01GrowthCacheRidgeSupport518Part001
public import RootedSixBase01GrowthCacheRidgeSupport518Part002
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport518_suffix_decode_021 : PackedRawNatGrowth.readList 14 0 ridgeSupport518_rest_021 =
    (ridgeSupport518_suffix_021, ridgeSupport518_rest_021) := by rfl
theorem ridgeSupport518_suffix_decode_020 : PackedRawNatGrowth.readList 14 13 ridgeSupport518_rest_020 =
    (ridgeSupport518_suffix_020, ridgeSupport518_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 13 0
    ridgeSupport518_rest_020 ridgeSupport518_rest_021 ridgeSupport518_rest_021
    ridgeSupport518_020 ridgeSupport518_suffix_021 ridgeSupport518_020_decode ridgeSupport518_suffix_decode_021
theorem ridgeSupport518_suffix_decode_019 : PackedRawNatGrowth.readList 14 45 ridgeSupport518_rest_019 =
    (ridgeSupport518_suffix_019, ridgeSupport518_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 13
    ridgeSupport518_rest_019 ridgeSupport518_rest_020 ridgeSupport518_rest_021
    ridgeSupport518_019 ridgeSupport518_suffix_020 ridgeSupport518_019_decode ridgeSupport518_suffix_decode_020
theorem ridgeSupport518_suffix_decode_018 : PackedRawNatGrowth.readList 14 77 ridgeSupport518_rest_018 =
    (ridgeSupport518_suffix_018, ridgeSupport518_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 45
    ridgeSupport518_rest_018 ridgeSupport518_rest_019 ridgeSupport518_rest_021
    ridgeSupport518_018 ridgeSupport518_suffix_019 ridgeSupport518_018_decode ridgeSupport518_suffix_decode_019
theorem ridgeSupport518_suffix_decode_017 : PackedRawNatGrowth.readList 14 109 ridgeSupport518_rest_017 =
    (ridgeSupport518_suffix_017, ridgeSupport518_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 77
    ridgeSupport518_rest_017 ridgeSupport518_rest_018 ridgeSupport518_rest_021
    ridgeSupport518_017 ridgeSupport518_suffix_018 ridgeSupport518_017_decode ridgeSupport518_suffix_decode_018
theorem ridgeSupport518_suffix_decode_016 : PackedRawNatGrowth.readList 14 141 ridgeSupport518_rest_016 =
    (ridgeSupport518_suffix_016, ridgeSupport518_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 109
    ridgeSupport518_rest_016 ridgeSupport518_rest_017 ridgeSupport518_rest_021
    ridgeSupport518_016 ridgeSupport518_suffix_017 ridgeSupport518_016_decode ridgeSupport518_suffix_decode_017
theorem ridgeSupport518_suffix_decode_015 : PackedRawNatGrowth.readList 14 173 ridgeSupport518_rest_015 =
    (ridgeSupport518_suffix_015, ridgeSupport518_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 141
    ridgeSupport518_rest_015 ridgeSupport518_rest_016 ridgeSupport518_rest_021
    ridgeSupport518_015 ridgeSupport518_suffix_016 ridgeSupport518_015_decode ridgeSupport518_suffix_decode_016
theorem ridgeSupport518_suffix_decode_014 : PackedRawNatGrowth.readList 14 205 ridgeSupport518_rest_014 =
    (ridgeSupport518_suffix_014, ridgeSupport518_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 173
    ridgeSupport518_rest_014 ridgeSupport518_rest_015 ridgeSupport518_rest_021
    ridgeSupport518_014 ridgeSupport518_suffix_015 ridgeSupport518_014_decode ridgeSupport518_suffix_decode_015
theorem ridgeSupport518_suffix_decode_013 : PackedRawNatGrowth.readList 14 237 ridgeSupport518_rest_013 =
    (ridgeSupport518_suffix_013, ridgeSupport518_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 205
    ridgeSupport518_rest_013 ridgeSupport518_rest_014 ridgeSupport518_rest_021
    ridgeSupport518_013 ridgeSupport518_suffix_014 ridgeSupport518_013_decode ridgeSupport518_suffix_decode_014
theorem ridgeSupport518_suffix_decode_012 : PackedRawNatGrowth.readList 14 269 ridgeSupport518_rest_012 =
    (ridgeSupport518_suffix_012, ridgeSupport518_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 237
    ridgeSupport518_rest_012 ridgeSupport518_rest_013 ridgeSupport518_rest_021
    ridgeSupport518_012 ridgeSupport518_suffix_013 ridgeSupport518_012_decode ridgeSupport518_suffix_decode_013
theorem ridgeSupport518_suffix_decode_011 : PackedRawNatGrowth.readList 14 301 ridgeSupport518_rest_011 =
    (ridgeSupport518_suffix_011, ridgeSupport518_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 269
    ridgeSupport518_rest_011 ridgeSupport518_rest_012 ridgeSupport518_rest_021
    ridgeSupport518_011 ridgeSupport518_suffix_012 ridgeSupport518_011_decode ridgeSupport518_suffix_decode_012
theorem ridgeSupport518_suffix_decode_010 : PackedRawNatGrowth.readList 14 333 ridgeSupport518_rest_010 =
    (ridgeSupport518_suffix_010, ridgeSupport518_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 301
    ridgeSupport518_rest_010 ridgeSupport518_rest_011 ridgeSupport518_rest_021
    ridgeSupport518_010 ridgeSupport518_suffix_011 ridgeSupport518_010_decode ridgeSupport518_suffix_decode_011
theorem ridgeSupport518_suffix_decode_009 : PackedRawNatGrowth.readList 14 365 ridgeSupport518_rest_009 =
    (ridgeSupport518_suffix_009, ridgeSupport518_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 333
    ridgeSupport518_rest_009 ridgeSupport518_rest_010 ridgeSupport518_rest_021
    ridgeSupport518_009 ridgeSupport518_suffix_010 ridgeSupport518_009_decode ridgeSupport518_suffix_decode_010
theorem ridgeSupport518_suffix_decode_008 : PackedRawNatGrowth.readList 14 397 ridgeSupport518_rest_008 =
    (ridgeSupport518_suffix_008, ridgeSupport518_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 365
    ridgeSupport518_rest_008 ridgeSupport518_rest_009 ridgeSupport518_rest_021
    ridgeSupport518_008 ridgeSupport518_suffix_009 ridgeSupport518_008_decode ridgeSupport518_suffix_decode_009
theorem ridgeSupport518_suffix_decode_007 : PackedRawNatGrowth.readList 14 429 ridgeSupport518_rest_007 =
    (ridgeSupport518_suffix_007, ridgeSupport518_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 397
    ridgeSupport518_rest_007 ridgeSupport518_rest_008 ridgeSupport518_rest_021
    ridgeSupport518_007 ridgeSupport518_suffix_008 ridgeSupport518_007_decode ridgeSupport518_suffix_decode_008
theorem ridgeSupport518_suffix_decode_006 : PackedRawNatGrowth.readList 14 461 ridgeSupport518_rest_006 =
    (ridgeSupport518_suffix_006, ridgeSupport518_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 429
    ridgeSupport518_rest_006 ridgeSupport518_rest_007 ridgeSupport518_rest_021
    ridgeSupport518_006 ridgeSupport518_suffix_007 ridgeSupport518_006_decode ridgeSupport518_suffix_decode_007
theorem ridgeSupport518_suffix_decode_005 : PackedRawNatGrowth.readList 14 493 ridgeSupport518_rest_005 =
    (ridgeSupport518_suffix_005, ridgeSupport518_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 461
    ridgeSupport518_rest_005 ridgeSupport518_rest_006 ridgeSupport518_rest_021
    ridgeSupport518_005 ridgeSupport518_suffix_006 ridgeSupport518_005_decode ridgeSupport518_suffix_decode_006
theorem ridgeSupport518_suffix_decode_004 : PackedRawNatGrowth.readList 14 525 ridgeSupport518_rest_004 =
    (ridgeSupport518_suffix_004, ridgeSupport518_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 493
    ridgeSupport518_rest_004 ridgeSupport518_rest_005 ridgeSupport518_rest_021
    ridgeSupport518_004 ridgeSupport518_suffix_005 ridgeSupport518_004_decode ridgeSupport518_suffix_decode_005
theorem ridgeSupport518_suffix_decode_003 : PackedRawNatGrowth.readList 14 557 ridgeSupport518_rest_003 =
    (ridgeSupport518_suffix_003, ridgeSupport518_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 525
    ridgeSupport518_rest_003 ridgeSupport518_rest_004 ridgeSupport518_rest_021
    ridgeSupport518_003 ridgeSupport518_suffix_004 ridgeSupport518_003_decode ridgeSupport518_suffix_decode_004
theorem ridgeSupport518_suffix_decode_002 : PackedRawNatGrowth.readList 14 589 ridgeSupport518_rest_002 =
    (ridgeSupport518_suffix_002, ridgeSupport518_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 557
    ridgeSupport518_rest_002 ridgeSupport518_rest_003 ridgeSupport518_rest_021
    ridgeSupport518_002 ridgeSupport518_suffix_003 ridgeSupport518_002_decode ridgeSupport518_suffix_decode_003
theorem ridgeSupport518_suffix_decode_001 : PackedRawNatGrowth.readList 14 621 ridgeSupport518_rest_001 =
    (ridgeSupport518_suffix_001, ridgeSupport518_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 589
    ridgeSupport518_rest_001 ridgeSupport518_rest_002 ridgeSupport518_rest_021
    ridgeSupport518_001 ridgeSupport518_suffix_002 ridgeSupport518_001_decode ridgeSupport518_suffix_decode_002
theorem ridgeSupport518_suffix_decode_000 : PackedRawNatGrowth.readList 14 653 ridgeSupport518_rest_000 =
    (ridgeSupport518_suffix_000, ridgeSupport518_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 621
    ridgeSupport518_rest_000 ridgeSupport518_rest_001 ridgeSupport518_rest_021
    ridgeSupport518_000 ridgeSupport518_suffix_001 ridgeSupport518_000_decode ridgeSupport518_suffix_decode_001
theorem ridgeSupport518_eq : candidateRows 518 = ridgeSupport518_suffix_000 := by
  rw [ridgeSupport518_source]
  exact congrArg Prod.fst ridgeSupport518_suffix_decode_000
theorem ridgeTest_large_518 : ridgeTest 518 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport518_eq]
    simp only [ridgeSupport518_suffix_000, ridgeSupport518_suffix_001, ridgeSupport518_suffix_002, ridgeSupport518_suffix_003, ridgeSupport518_suffix_004, ridgeSupport518_suffix_005, ridgeSupport518_suffix_006, ridgeSupport518_suffix_007, ridgeSupport518_suffix_008, ridgeSupport518_suffix_009, ridgeSupport518_suffix_010, ridgeSupport518_suffix_011, ridgeSupport518_suffix_012, ridgeSupport518_suffix_013, ridgeSupport518_suffix_014, ridgeSupport518_suffix_015, ridgeSupport518_suffix_016, ridgeSupport518_suffix_017, ridgeSupport518_suffix_018, ridgeSupport518_suffix_019, ridgeSupport518_suffix_020, ridgeSupport518_suffix_021, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport518_000_mask, ridgeSupport518_001_mask, ridgeSupport518_002_mask, ridgeSupport518_003_mask, ridgeSupport518_004_mask, ridgeSupport518_005_mask, ridgeSupport518_006_mask, ridgeSupport518_007_mask, ridgeSupport518_008_mask, ridgeSupport518_009_mask, ridgeSupport518_010_mask, ridgeSupport518_011_mask, ridgeSupport518_012_mask, ridgeSupport518_013_mask, ridgeSupport518_014_mask, ridgeSupport518_015_mask, ridgeSupport518_016_mask, ridgeSupport518_017_mask, ridgeSupport518_018_mask, ridgeSupport518_019_mask, ridgeSupport518_020_mask]
    decide +kernel
  · rw [ridgeSupport518_eq]
    simp only [ridgeSupport518_suffix_000, ridgeSupport518_suffix_001, ridgeSupport518_suffix_002, ridgeSupport518_suffix_003, ridgeSupport518_suffix_004, ridgeSupport518_suffix_005, ridgeSupport518_suffix_006, ridgeSupport518_suffix_007, ridgeSupport518_suffix_008, ridgeSupport518_suffix_009, ridgeSupport518_suffix_010, ridgeSupport518_suffix_011, ridgeSupport518_suffix_012, ridgeSupport518_suffix_013, ridgeSupport518_suffix_014, ridgeSupport518_suffix_015, ridgeSupport518_suffix_016, ridgeSupport518_suffix_017, ridgeSupport518_suffix_018, ridgeSupport518_suffix_019, ridgeSupport518_suffix_020, ridgeSupport518_suffix_021, List.all_append, List.all_nil, ridgeSupport518_000_checked, ridgeSupport518_001_checked, ridgeSupport518_002_checked, ridgeSupport518_003_checked, ridgeSupport518_004_checked, ridgeSupport518_005_checked, ridgeSupport518_006_checked, ridgeSupport518_007_checked, ridgeSupport518_008_checked, ridgeSupport518_009_checked, ridgeSupport518_010_checked, ridgeSupport518_011_checked, ridgeSupport518_012_checked, ridgeSupport518_013_checked, ridgeSupport518_014_checked, ridgeSupport518_015_checked, ridgeSupport518_016_checked, ridgeSupport518_017_checked, ridgeSupport518_018_checked, ridgeSupport518_019_checked, ridgeSupport518_020_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase01
