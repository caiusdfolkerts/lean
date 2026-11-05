module
prelude
public import RootedSixBase01GrowthCacheRidgeSupport548Part000
public import RootedSixBase01GrowthCacheRidgeSupport548Part001
public import RootedSixBase01GrowthCacheRidgeSupport548Part002
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport548_suffix_decode_021 : PackedRawNatGrowth.readList 14 0 ridgeSupport548_rest_021 =
    (ridgeSupport548_suffix_021, ridgeSupport548_rest_021) := by rfl
theorem ridgeSupport548_suffix_decode_020 : PackedRawNatGrowth.readList 14 13 ridgeSupport548_rest_020 =
    (ridgeSupport548_suffix_020, ridgeSupport548_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 13 0
    ridgeSupport548_rest_020 ridgeSupport548_rest_021 ridgeSupport548_rest_021
    ridgeSupport548_020 ridgeSupport548_suffix_021 ridgeSupport548_020_decode ridgeSupport548_suffix_decode_021
theorem ridgeSupport548_suffix_decode_019 : PackedRawNatGrowth.readList 14 45 ridgeSupport548_rest_019 =
    (ridgeSupport548_suffix_019, ridgeSupport548_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 13
    ridgeSupport548_rest_019 ridgeSupport548_rest_020 ridgeSupport548_rest_021
    ridgeSupport548_019 ridgeSupport548_suffix_020 ridgeSupport548_019_decode ridgeSupport548_suffix_decode_020
theorem ridgeSupport548_suffix_decode_018 : PackedRawNatGrowth.readList 14 77 ridgeSupport548_rest_018 =
    (ridgeSupport548_suffix_018, ridgeSupport548_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 45
    ridgeSupport548_rest_018 ridgeSupport548_rest_019 ridgeSupport548_rest_021
    ridgeSupport548_018 ridgeSupport548_suffix_019 ridgeSupport548_018_decode ridgeSupport548_suffix_decode_019
theorem ridgeSupport548_suffix_decode_017 : PackedRawNatGrowth.readList 14 109 ridgeSupport548_rest_017 =
    (ridgeSupport548_suffix_017, ridgeSupport548_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 77
    ridgeSupport548_rest_017 ridgeSupport548_rest_018 ridgeSupport548_rest_021
    ridgeSupport548_017 ridgeSupport548_suffix_018 ridgeSupport548_017_decode ridgeSupport548_suffix_decode_018
theorem ridgeSupport548_suffix_decode_016 : PackedRawNatGrowth.readList 14 141 ridgeSupport548_rest_016 =
    (ridgeSupport548_suffix_016, ridgeSupport548_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 109
    ridgeSupport548_rest_016 ridgeSupport548_rest_017 ridgeSupport548_rest_021
    ridgeSupport548_016 ridgeSupport548_suffix_017 ridgeSupport548_016_decode ridgeSupport548_suffix_decode_017
theorem ridgeSupport548_suffix_decode_015 : PackedRawNatGrowth.readList 14 173 ridgeSupport548_rest_015 =
    (ridgeSupport548_suffix_015, ridgeSupport548_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 141
    ridgeSupport548_rest_015 ridgeSupport548_rest_016 ridgeSupport548_rest_021
    ridgeSupport548_015 ridgeSupport548_suffix_016 ridgeSupport548_015_decode ridgeSupport548_suffix_decode_016
theorem ridgeSupport548_suffix_decode_014 : PackedRawNatGrowth.readList 14 205 ridgeSupport548_rest_014 =
    (ridgeSupport548_suffix_014, ridgeSupport548_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 173
    ridgeSupport548_rest_014 ridgeSupport548_rest_015 ridgeSupport548_rest_021
    ridgeSupport548_014 ridgeSupport548_suffix_015 ridgeSupport548_014_decode ridgeSupport548_suffix_decode_015
theorem ridgeSupport548_suffix_decode_013 : PackedRawNatGrowth.readList 14 237 ridgeSupport548_rest_013 =
    (ridgeSupport548_suffix_013, ridgeSupport548_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 205
    ridgeSupport548_rest_013 ridgeSupport548_rest_014 ridgeSupport548_rest_021
    ridgeSupport548_013 ridgeSupport548_suffix_014 ridgeSupport548_013_decode ridgeSupport548_suffix_decode_014
theorem ridgeSupport548_suffix_decode_012 : PackedRawNatGrowth.readList 14 269 ridgeSupport548_rest_012 =
    (ridgeSupport548_suffix_012, ridgeSupport548_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 237
    ridgeSupport548_rest_012 ridgeSupport548_rest_013 ridgeSupport548_rest_021
    ridgeSupport548_012 ridgeSupport548_suffix_013 ridgeSupport548_012_decode ridgeSupport548_suffix_decode_013
theorem ridgeSupport548_suffix_decode_011 : PackedRawNatGrowth.readList 14 301 ridgeSupport548_rest_011 =
    (ridgeSupport548_suffix_011, ridgeSupport548_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 269
    ridgeSupport548_rest_011 ridgeSupport548_rest_012 ridgeSupport548_rest_021
    ridgeSupport548_011 ridgeSupport548_suffix_012 ridgeSupport548_011_decode ridgeSupport548_suffix_decode_012
theorem ridgeSupport548_suffix_decode_010 : PackedRawNatGrowth.readList 14 333 ridgeSupport548_rest_010 =
    (ridgeSupport548_suffix_010, ridgeSupport548_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 301
    ridgeSupport548_rest_010 ridgeSupport548_rest_011 ridgeSupport548_rest_021
    ridgeSupport548_010 ridgeSupport548_suffix_011 ridgeSupport548_010_decode ridgeSupport548_suffix_decode_011
theorem ridgeSupport548_suffix_decode_009 : PackedRawNatGrowth.readList 14 365 ridgeSupport548_rest_009 =
    (ridgeSupport548_suffix_009, ridgeSupport548_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 333
    ridgeSupport548_rest_009 ridgeSupport548_rest_010 ridgeSupport548_rest_021
    ridgeSupport548_009 ridgeSupport548_suffix_010 ridgeSupport548_009_decode ridgeSupport548_suffix_decode_010
theorem ridgeSupport548_suffix_decode_008 : PackedRawNatGrowth.readList 14 397 ridgeSupport548_rest_008 =
    (ridgeSupport548_suffix_008, ridgeSupport548_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 365
    ridgeSupport548_rest_008 ridgeSupport548_rest_009 ridgeSupport548_rest_021
    ridgeSupport548_008 ridgeSupport548_suffix_009 ridgeSupport548_008_decode ridgeSupport548_suffix_decode_009
theorem ridgeSupport548_suffix_decode_007 : PackedRawNatGrowth.readList 14 429 ridgeSupport548_rest_007 =
    (ridgeSupport548_suffix_007, ridgeSupport548_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 397
    ridgeSupport548_rest_007 ridgeSupport548_rest_008 ridgeSupport548_rest_021
    ridgeSupport548_007 ridgeSupport548_suffix_008 ridgeSupport548_007_decode ridgeSupport548_suffix_decode_008
theorem ridgeSupport548_suffix_decode_006 : PackedRawNatGrowth.readList 14 461 ridgeSupport548_rest_006 =
    (ridgeSupport548_suffix_006, ridgeSupport548_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 429
    ridgeSupport548_rest_006 ridgeSupport548_rest_007 ridgeSupport548_rest_021
    ridgeSupport548_006 ridgeSupport548_suffix_007 ridgeSupport548_006_decode ridgeSupport548_suffix_decode_007
theorem ridgeSupport548_suffix_decode_005 : PackedRawNatGrowth.readList 14 493 ridgeSupport548_rest_005 =
    (ridgeSupport548_suffix_005, ridgeSupport548_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 461
    ridgeSupport548_rest_005 ridgeSupport548_rest_006 ridgeSupport548_rest_021
    ridgeSupport548_005 ridgeSupport548_suffix_006 ridgeSupport548_005_decode ridgeSupport548_suffix_decode_006
theorem ridgeSupport548_suffix_decode_004 : PackedRawNatGrowth.readList 14 525 ridgeSupport548_rest_004 =
    (ridgeSupport548_suffix_004, ridgeSupport548_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 493
    ridgeSupport548_rest_004 ridgeSupport548_rest_005 ridgeSupport548_rest_021
    ridgeSupport548_004 ridgeSupport548_suffix_005 ridgeSupport548_004_decode ridgeSupport548_suffix_decode_005
theorem ridgeSupport548_suffix_decode_003 : PackedRawNatGrowth.readList 14 557 ridgeSupport548_rest_003 =
    (ridgeSupport548_suffix_003, ridgeSupport548_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 525
    ridgeSupport548_rest_003 ridgeSupport548_rest_004 ridgeSupport548_rest_021
    ridgeSupport548_003 ridgeSupport548_suffix_004 ridgeSupport548_003_decode ridgeSupport548_suffix_decode_004
theorem ridgeSupport548_suffix_decode_002 : PackedRawNatGrowth.readList 14 589 ridgeSupport548_rest_002 =
    (ridgeSupport548_suffix_002, ridgeSupport548_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 557
    ridgeSupport548_rest_002 ridgeSupport548_rest_003 ridgeSupport548_rest_021
    ridgeSupport548_002 ridgeSupport548_suffix_003 ridgeSupport548_002_decode ridgeSupport548_suffix_decode_003
theorem ridgeSupport548_suffix_decode_001 : PackedRawNatGrowth.readList 14 621 ridgeSupport548_rest_001 =
    (ridgeSupport548_suffix_001, ridgeSupport548_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 589
    ridgeSupport548_rest_001 ridgeSupport548_rest_002 ridgeSupport548_rest_021
    ridgeSupport548_001 ridgeSupport548_suffix_002 ridgeSupport548_001_decode ridgeSupport548_suffix_decode_002
theorem ridgeSupport548_suffix_decode_000 : PackedRawNatGrowth.readList 14 653 ridgeSupport548_rest_000 =
    (ridgeSupport548_suffix_000, ridgeSupport548_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 621
    ridgeSupport548_rest_000 ridgeSupport548_rest_001 ridgeSupport548_rest_021
    ridgeSupport548_000 ridgeSupport548_suffix_001 ridgeSupport548_000_decode ridgeSupport548_suffix_decode_001
theorem ridgeSupport548_eq : candidateRows 548 = ridgeSupport548_suffix_000 := by
  rw [ridgeSupport548_source]
  exact congrArg Prod.fst ridgeSupport548_suffix_decode_000
theorem ridgeTest_large_548 : ridgeTest 548 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport548_eq]
    simp only [ridgeSupport548_suffix_000, ridgeSupport548_suffix_001, ridgeSupport548_suffix_002, ridgeSupport548_suffix_003, ridgeSupport548_suffix_004, ridgeSupport548_suffix_005, ridgeSupport548_suffix_006, ridgeSupport548_suffix_007, ridgeSupport548_suffix_008, ridgeSupport548_suffix_009, ridgeSupport548_suffix_010, ridgeSupport548_suffix_011, ridgeSupport548_suffix_012, ridgeSupport548_suffix_013, ridgeSupport548_suffix_014, ridgeSupport548_suffix_015, ridgeSupport548_suffix_016, ridgeSupport548_suffix_017, ridgeSupport548_suffix_018, ridgeSupport548_suffix_019, ridgeSupport548_suffix_020, ridgeSupport548_suffix_021, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport548_000_mask, ridgeSupport548_001_mask, ridgeSupport548_002_mask, ridgeSupport548_003_mask, ridgeSupport548_004_mask, ridgeSupport548_005_mask, ridgeSupport548_006_mask, ridgeSupport548_007_mask, ridgeSupport548_008_mask, ridgeSupport548_009_mask, ridgeSupport548_010_mask, ridgeSupport548_011_mask, ridgeSupport548_012_mask, ridgeSupport548_013_mask, ridgeSupport548_014_mask, ridgeSupport548_015_mask, ridgeSupport548_016_mask, ridgeSupport548_017_mask, ridgeSupport548_018_mask, ridgeSupport548_019_mask, ridgeSupport548_020_mask]
    decide +kernel
  · rw [ridgeSupport548_eq]
    simp only [ridgeSupport548_suffix_000, ridgeSupport548_suffix_001, ridgeSupport548_suffix_002, ridgeSupport548_suffix_003, ridgeSupport548_suffix_004, ridgeSupport548_suffix_005, ridgeSupport548_suffix_006, ridgeSupport548_suffix_007, ridgeSupport548_suffix_008, ridgeSupport548_suffix_009, ridgeSupport548_suffix_010, ridgeSupport548_suffix_011, ridgeSupport548_suffix_012, ridgeSupport548_suffix_013, ridgeSupport548_suffix_014, ridgeSupport548_suffix_015, ridgeSupport548_suffix_016, ridgeSupport548_suffix_017, ridgeSupport548_suffix_018, ridgeSupport548_suffix_019, ridgeSupport548_suffix_020, ridgeSupport548_suffix_021, List.all_append, List.all_nil, ridgeSupport548_000_checked, ridgeSupport548_001_checked, ridgeSupport548_002_checked, ridgeSupport548_003_checked, ridgeSupport548_004_checked, ridgeSupport548_005_checked, ridgeSupport548_006_checked, ridgeSupport548_007_checked, ridgeSupport548_008_checked, ridgeSupport548_009_checked, ridgeSupport548_010_checked, ridgeSupport548_011_checked, ridgeSupport548_012_checked, ridgeSupport548_013_checked, ridgeSupport548_014_checked, ridgeSupport548_015_checked, ridgeSupport548_016_checked, ridgeSupport548_017_checked, ridgeSupport548_018_checked, ridgeSupport548_019_checked, ridgeSupport548_020_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase01
