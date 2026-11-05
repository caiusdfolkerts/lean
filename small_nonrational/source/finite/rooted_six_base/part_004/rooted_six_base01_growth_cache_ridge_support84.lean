module
prelude
public import RootedSixBase01GrowthCacheRidgeSupport84Part000
public import RootedSixBase01GrowthCacheRidgeSupport84Part001
public import RootedSixBase01GrowthCacheRidgeSupport84Part002
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport84_suffix_decode_021 : PackedRawNatGrowth.readList 14 0 ridgeSupport84_rest_021 =
    (ridgeSupport84_suffix_021, ridgeSupport84_rest_021) := by rfl
theorem ridgeSupport84_suffix_decode_020 : PackedRawNatGrowth.readList 14 13 ridgeSupport84_rest_020 =
    (ridgeSupport84_suffix_020, ridgeSupport84_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 13 0
    ridgeSupport84_rest_020 ridgeSupport84_rest_021 ridgeSupport84_rest_021
    ridgeSupport84_020 ridgeSupport84_suffix_021 ridgeSupport84_020_decode ridgeSupport84_suffix_decode_021
theorem ridgeSupport84_suffix_decode_019 : PackedRawNatGrowth.readList 14 45 ridgeSupport84_rest_019 =
    (ridgeSupport84_suffix_019, ridgeSupport84_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 13
    ridgeSupport84_rest_019 ridgeSupport84_rest_020 ridgeSupport84_rest_021
    ridgeSupport84_019 ridgeSupport84_suffix_020 ridgeSupport84_019_decode ridgeSupport84_suffix_decode_020
theorem ridgeSupport84_suffix_decode_018 : PackedRawNatGrowth.readList 14 77 ridgeSupport84_rest_018 =
    (ridgeSupport84_suffix_018, ridgeSupport84_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 45
    ridgeSupport84_rest_018 ridgeSupport84_rest_019 ridgeSupport84_rest_021
    ridgeSupport84_018 ridgeSupport84_suffix_019 ridgeSupport84_018_decode ridgeSupport84_suffix_decode_019
theorem ridgeSupport84_suffix_decode_017 : PackedRawNatGrowth.readList 14 109 ridgeSupport84_rest_017 =
    (ridgeSupport84_suffix_017, ridgeSupport84_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 77
    ridgeSupport84_rest_017 ridgeSupport84_rest_018 ridgeSupport84_rest_021
    ridgeSupport84_017 ridgeSupport84_suffix_018 ridgeSupport84_017_decode ridgeSupport84_suffix_decode_018
theorem ridgeSupport84_suffix_decode_016 : PackedRawNatGrowth.readList 14 141 ridgeSupport84_rest_016 =
    (ridgeSupport84_suffix_016, ridgeSupport84_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 109
    ridgeSupport84_rest_016 ridgeSupport84_rest_017 ridgeSupport84_rest_021
    ridgeSupport84_016 ridgeSupport84_suffix_017 ridgeSupport84_016_decode ridgeSupport84_suffix_decode_017
theorem ridgeSupport84_suffix_decode_015 : PackedRawNatGrowth.readList 14 173 ridgeSupport84_rest_015 =
    (ridgeSupport84_suffix_015, ridgeSupport84_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 141
    ridgeSupport84_rest_015 ridgeSupport84_rest_016 ridgeSupport84_rest_021
    ridgeSupport84_015 ridgeSupport84_suffix_016 ridgeSupport84_015_decode ridgeSupport84_suffix_decode_016
theorem ridgeSupport84_suffix_decode_014 : PackedRawNatGrowth.readList 14 205 ridgeSupport84_rest_014 =
    (ridgeSupport84_suffix_014, ridgeSupport84_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 173
    ridgeSupport84_rest_014 ridgeSupport84_rest_015 ridgeSupport84_rest_021
    ridgeSupport84_014 ridgeSupport84_suffix_015 ridgeSupport84_014_decode ridgeSupport84_suffix_decode_015
theorem ridgeSupport84_suffix_decode_013 : PackedRawNatGrowth.readList 14 237 ridgeSupport84_rest_013 =
    (ridgeSupport84_suffix_013, ridgeSupport84_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 205
    ridgeSupport84_rest_013 ridgeSupport84_rest_014 ridgeSupport84_rest_021
    ridgeSupport84_013 ridgeSupport84_suffix_014 ridgeSupport84_013_decode ridgeSupport84_suffix_decode_014
theorem ridgeSupport84_suffix_decode_012 : PackedRawNatGrowth.readList 14 269 ridgeSupport84_rest_012 =
    (ridgeSupport84_suffix_012, ridgeSupport84_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 237
    ridgeSupport84_rest_012 ridgeSupport84_rest_013 ridgeSupport84_rest_021
    ridgeSupport84_012 ridgeSupport84_suffix_013 ridgeSupport84_012_decode ridgeSupport84_suffix_decode_013
theorem ridgeSupport84_suffix_decode_011 : PackedRawNatGrowth.readList 14 301 ridgeSupport84_rest_011 =
    (ridgeSupport84_suffix_011, ridgeSupport84_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 269
    ridgeSupport84_rest_011 ridgeSupport84_rest_012 ridgeSupport84_rest_021
    ridgeSupport84_011 ridgeSupport84_suffix_012 ridgeSupport84_011_decode ridgeSupport84_suffix_decode_012
theorem ridgeSupport84_suffix_decode_010 : PackedRawNatGrowth.readList 14 333 ridgeSupport84_rest_010 =
    (ridgeSupport84_suffix_010, ridgeSupport84_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 301
    ridgeSupport84_rest_010 ridgeSupport84_rest_011 ridgeSupport84_rest_021
    ridgeSupport84_010 ridgeSupport84_suffix_011 ridgeSupport84_010_decode ridgeSupport84_suffix_decode_011
theorem ridgeSupport84_suffix_decode_009 : PackedRawNatGrowth.readList 14 365 ridgeSupport84_rest_009 =
    (ridgeSupport84_suffix_009, ridgeSupport84_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 333
    ridgeSupport84_rest_009 ridgeSupport84_rest_010 ridgeSupport84_rest_021
    ridgeSupport84_009 ridgeSupport84_suffix_010 ridgeSupport84_009_decode ridgeSupport84_suffix_decode_010
theorem ridgeSupport84_suffix_decode_008 : PackedRawNatGrowth.readList 14 397 ridgeSupport84_rest_008 =
    (ridgeSupport84_suffix_008, ridgeSupport84_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 365
    ridgeSupport84_rest_008 ridgeSupport84_rest_009 ridgeSupport84_rest_021
    ridgeSupport84_008 ridgeSupport84_suffix_009 ridgeSupport84_008_decode ridgeSupport84_suffix_decode_009
theorem ridgeSupport84_suffix_decode_007 : PackedRawNatGrowth.readList 14 429 ridgeSupport84_rest_007 =
    (ridgeSupport84_suffix_007, ridgeSupport84_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 397
    ridgeSupport84_rest_007 ridgeSupport84_rest_008 ridgeSupport84_rest_021
    ridgeSupport84_007 ridgeSupport84_suffix_008 ridgeSupport84_007_decode ridgeSupport84_suffix_decode_008
theorem ridgeSupport84_suffix_decode_006 : PackedRawNatGrowth.readList 14 461 ridgeSupport84_rest_006 =
    (ridgeSupport84_suffix_006, ridgeSupport84_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 429
    ridgeSupport84_rest_006 ridgeSupport84_rest_007 ridgeSupport84_rest_021
    ridgeSupport84_006 ridgeSupport84_suffix_007 ridgeSupport84_006_decode ridgeSupport84_suffix_decode_007
theorem ridgeSupport84_suffix_decode_005 : PackedRawNatGrowth.readList 14 493 ridgeSupport84_rest_005 =
    (ridgeSupport84_suffix_005, ridgeSupport84_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 461
    ridgeSupport84_rest_005 ridgeSupport84_rest_006 ridgeSupport84_rest_021
    ridgeSupport84_005 ridgeSupport84_suffix_006 ridgeSupport84_005_decode ridgeSupport84_suffix_decode_006
theorem ridgeSupport84_suffix_decode_004 : PackedRawNatGrowth.readList 14 525 ridgeSupport84_rest_004 =
    (ridgeSupport84_suffix_004, ridgeSupport84_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 493
    ridgeSupport84_rest_004 ridgeSupport84_rest_005 ridgeSupport84_rest_021
    ridgeSupport84_004 ridgeSupport84_suffix_005 ridgeSupport84_004_decode ridgeSupport84_suffix_decode_005
theorem ridgeSupport84_suffix_decode_003 : PackedRawNatGrowth.readList 14 557 ridgeSupport84_rest_003 =
    (ridgeSupport84_suffix_003, ridgeSupport84_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 525
    ridgeSupport84_rest_003 ridgeSupport84_rest_004 ridgeSupport84_rest_021
    ridgeSupport84_003 ridgeSupport84_suffix_004 ridgeSupport84_003_decode ridgeSupport84_suffix_decode_004
theorem ridgeSupport84_suffix_decode_002 : PackedRawNatGrowth.readList 14 589 ridgeSupport84_rest_002 =
    (ridgeSupport84_suffix_002, ridgeSupport84_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 557
    ridgeSupport84_rest_002 ridgeSupport84_rest_003 ridgeSupport84_rest_021
    ridgeSupport84_002 ridgeSupport84_suffix_003 ridgeSupport84_002_decode ridgeSupport84_suffix_decode_003
theorem ridgeSupport84_suffix_decode_001 : PackedRawNatGrowth.readList 14 621 ridgeSupport84_rest_001 =
    (ridgeSupport84_suffix_001, ridgeSupport84_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 589
    ridgeSupport84_rest_001 ridgeSupport84_rest_002 ridgeSupport84_rest_021
    ridgeSupport84_001 ridgeSupport84_suffix_002 ridgeSupport84_001_decode ridgeSupport84_suffix_decode_002
theorem ridgeSupport84_suffix_decode_000 : PackedRawNatGrowth.readList 14 653 ridgeSupport84_rest_000 =
    (ridgeSupport84_suffix_000, ridgeSupport84_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 621
    ridgeSupport84_rest_000 ridgeSupport84_rest_001 ridgeSupport84_rest_021
    ridgeSupport84_000 ridgeSupport84_suffix_001 ridgeSupport84_000_decode ridgeSupport84_suffix_decode_001
theorem ridgeSupport84_eq : candidateRows 84 = ridgeSupport84_suffix_000 := by
  rw [ridgeSupport84_source]
  exact congrArg Prod.fst ridgeSupport84_suffix_decode_000
theorem ridgeTest_large_84 : ridgeTest 84 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport84_eq]
    simp only [ridgeSupport84_suffix_000, ridgeSupport84_suffix_001, ridgeSupport84_suffix_002, ridgeSupport84_suffix_003, ridgeSupport84_suffix_004, ridgeSupport84_suffix_005, ridgeSupport84_suffix_006, ridgeSupport84_suffix_007, ridgeSupport84_suffix_008, ridgeSupport84_suffix_009, ridgeSupport84_suffix_010, ridgeSupport84_suffix_011, ridgeSupport84_suffix_012, ridgeSupport84_suffix_013, ridgeSupport84_suffix_014, ridgeSupport84_suffix_015, ridgeSupport84_suffix_016, ridgeSupport84_suffix_017, ridgeSupport84_suffix_018, ridgeSupport84_suffix_019, ridgeSupport84_suffix_020, ridgeSupport84_suffix_021, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport84_000_mask, ridgeSupport84_001_mask, ridgeSupport84_002_mask, ridgeSupport84_003_mask, ridgeSupport84_004_mask, ridgeSupport84_005_mask, ridgeSupport84_006_mask, ridgeSupport84_007_mask, ridgeSupport84_008_mask, ridgeSupport84_009_mask, ridgeSupport84_010_mask, ridgeSupport84_011_mask, ridgeSupport84_012_mask, ridgeSupport84_013_mask, ridgeSupport84_014_mask, ridgeSupport84_015_mask, ridgeSupport84_016_mask, ridgeSupport84_017_mask, ridgeSupport84_018_mask, ridgeSupport84_019_mask, ridgeSupport84_020_mask]
    decide +kernel
  · rw [ridgeSupport84_eq]
    simp only [ridgeSupport84_suffix_000, ridgeSupport84_suffix_001, ridgeSupport84_suffix_002, ridgeSupport84_suffix_003, ridgeSupport84_suffix_004, ridgeSupport84_suffix_005, ridgeSupport84_suffix_006, ridgeSupport84_suffix_007, ridgeSupport84_suffix_008, ridgeSupport84_suffix_009, ridgeSupport84_suffix_010, ridgeSupport84_suffix_011, ridgeSupport84_suffix_012, ridgeSupport84_suffix_013, ridgeSupport84_suffix_014, ridgeSupport84_suffix_015, ridgeSupport84_suffix_016, ridgeSupport84_suffix_017, ridgeSupport84_suffix_018, ridgeSupport84_suffix_019, ridgeSupport84_suffix_020, ridgeSupport84_suffix_021, List.all_append, List.all_nil, ridgeSupport84_000_checked, ridgeSupport84_001_checked, ridgeSupport84_002_checked, ridgeSupport84_003_checked, ridgeSupport84_004_checked, ridgeSupport84_005_checked, ridgeSupport84_006_checked, ridgeSupport84_007_checked, ridgeSupport84_008_checked, ridgeSupport84_009_checked, ridgeSupport84_010_checked, ridgeSupport84_011_checked, ridgeSupport84_012_checked, ridgeSupport84_013_checked, ridgeSupport84_014_checked, ridgeSupport84_015_checked, ridgeSupport84_016_checked, ridgeSupport84_017_checked, ridgeSupport84_018_checked, ridgeSupport84_019_checked, ridgeSupport84_020_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase01
