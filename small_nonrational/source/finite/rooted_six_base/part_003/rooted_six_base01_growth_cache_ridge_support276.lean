module
prelude
public import RootedSixBase01GrowthCacheRidgeSupport276Part000
public import RootedSixBase01GrowthCacheRidgeSupport276Part001
public import RootedSixBase01GrowthCacheRidgeSupport276Part002
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport276_suffix_decode_021 : PackedRawNatGrowth.readList 14 0 ridgeSupport276_rest_021 =
    (ridgeSupport276_suffix_021, ridgeSupport276_rest_021) := by rfl
theorem ridgeSupport276_suffix_decode_020 : PackedRawNatGrowth.readList 14 13 ridgeSupport276_rest_020 =
    (ridgeSupport276_suffix_020, ridgeSupport276_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 13 0
    ridgeSupport276_rest_020 ridgeSupport276_rest_021 ridgeSupport276_rest_021
    ridgeSupport276_020 ridgeSupport276_suffix_021 ridgeSupport276_020_decode ridgeSupport276_suffix_decode_021
theorem ridgeSupport276_suffix_decode_019 : PackedRawNatGrowth.readList 14 45 ridgeSupport276_rest_019 =
    (ridgeSupport276_suffix_019, ridgeSupport276_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 13
    ridgeSupport276_rest_019 ridgeSupport276_rest_020 ridgeSupport276_rest_021
    ridgeSupport276_019 ridgeSupport276_suffix_020 ridgeSupport276_019_decode ridgeSupport276_suffix_decode_020
theorem ridgeSupport276_suffix_decode_018 : PackedRawNatGrowth.readList 14 77 ridgeSupport276_rest_018 =
    (ridgeSupport276_suffix_018, ridgeSupport276_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 45
    ridgeSupport276_rest_018 ridgeSupport276_rest_019 ridgeSupport276_rest_021
    ridgeSupport276_018 ridgeSupport276_suffix_019 ridgeSupport276_018_decode ridgeSupport276_suffix_decode_019
theorem ridgeSupport276_suffix_decode_017 : PackedRawNatGrowth.readList 14 109 ridgeSupport276_rest_017 =
    (ridgeSupport276_suffix_017, ridgeSupport276_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 77
    ridgeSupport276_rest_017 ridgeSupport276_rest_018 ridgeSupport276_rest_021
    ridgeSupport276_017 ridgeSupport276_suffix_018 ridgeSupport276_017_decode ridgeSupport276_suffix_decode_018
theorem ridgeSupport276_suffix_decode_016 : PackedRawNatGrowth.readList 14 141 ridgeSupport276_rest_016 =
    (ridgeSupport276_suffix_016, ridgeSupport276_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 109
    ridgeSupport276_rest_016 ridgeSupport276_rest_017 ridgeSupport276_rest_021
    ridgeSupport276_016 ridgeSupport276_suffix_017 ridgeSupport276_016_decode ridgeSupport276_suffix_decode_017
theorem ridgeSupport276_suffix_decode_015 : PackedRawNatGrowth.readList 14 173 ridgeSupport276_rest_015 =
    (ridgeSupport276_suffix_015, ridgeSupport276_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 141
    ridgeSupport276_rest_015 ridgeSupport276_rest_016 ridgeSupport276_rest_021
    ridgeSupport276_015 ridgeSupport276_suffix_016 ridgeSupport276_015_decode ridgeSupport276_suffix_decode_016
theorem ridgeSupport276_suffix_decode_014 : PackedRawNatGrowth.readList 14 205 ridgeSupport276_rest_014 =
    (ridgeSupport276_suffix_014, ridgeSupport276_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 173
    ridgeSupport276_rest_014 ridgeSupport276_rest_015 ridgeSupport276_rest_021
    ridgeSupport276_014 ridgeSupport276_suffix_015 ridgeSupport276_014_decode ridgeSupport276_suffix_decode_015
theorem ridgeSupport276_suffix_decode_013 : PackedRawNatGrowth.readList 14 237 ridgeSupport276_rest_013 =
    (ridgeSupport276_suffix_013, ridgeSupport276_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 205
    ridgeSupport276_rest_013 ridgeSupport276_rest_014 ridgeSupport276_rest_021
    ridgeSupport276_013 ridgeSupport276_suffix_014 ridgeSupport276_013_decode ridgeSupport276_suffix_decode_014
theorem ridgeSupport276_suffix_decode_012 : PackedRawNatGrowth.readList 14 269 ridgeSupport276_rest_012 =
    (ridgeSupport276_suffix_012, ridgeSupport276_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 237
    ridgeSupport276_rest_012 ridgeSupport276_rest_013 ridgeSupport276_rest_021
    ridgeSupport276_012 ridgeSupport276_suffix_013 ridgeSupport276_012_decode ridgeSupport276_suffix_decode_013
theorem ridgeSupport276_suffix_decode_011 : PackedRawNatGrowth.readList 14 301 ridgeSupport276_rest_011 =
    (ridgeSupport276_suffix_011, ridgeSupport276_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 269
    ridgeSupport276_rest_011 ridgeSupport276_rest_012 ridgeSupport276_rest_021
    ridgeSupport276_011 ridgeSupport276_suffix_012 ridgeSupport276_011_decode ridgeSupport276_suffix_decode_012
theorem ridgeSupport276_suffix_decode_010 : PackedRawNatGrowth.readList 14 333 ridgeSupport276_rest_010 =
    (ridgeSupport276_suffix_010, ridgeSupport276_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 301
    ridgeSupport276_rest_010 ridgeSupport276_rest_011 ridgeSupport276_rest_021
    ridgeSupport276_010 ridgeSupport276_suffix_011 ridgeSupport276_010_decode ridgeSupport276_suffix_decode_011
theorem ridgeSupport276_suffix_decode_009 : PackedRawNatGrowth.readList 14 365 ridgeSupport276_rest_009 =
    (ridgeSupport276_suffix_009, ridgeSupport276_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 333
    ridgeSupport276_rest_009 ridgeSupport276_rest_010 ridgeSupport276_rest_021
    ridgeSupport276_009 ridgeSupport276_suffix_010 ridgeSupport276_009_decode ridgeSupport276_suffix_decode_010
theorem ridgeSupport276_suffix_decode_008 : PackedRawNatGrowth.readList 14 397 ridgeSupport276_rest_008 =
    (ridgeSupport276_suffix_008, ridgeSupport276_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 365
    ridgeSupport276_rest_008 ridgeSupport276_rest_009 ridgeSupport276_rest_021
    ridgeSupport276_008 ridgeSupport276_suffix_009 ridgeSupport276_008_decode ridgeSupport276_suffix_decode_009
theorem ridgeSupport276_suffix_decode_007 : PackedRawNatGrowth.readList 14 429 ridgeSupport276_rest_007 =
    (ridgeSupport276_suffix_007, ridgeSupport276_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 397
    ridgeSupport276_rest_007 ridgeSupport276_rest_008 ridgeSupport276_rest_021
    ridgeSupport276_007 ridgeSupport276_suffix_008 ridgeSupport276_007_decode ridgeSupport276_suffix_decode_008
theorem ridgeSupport276_suffix_decode_006 : PackedRawNatGrowth.readList 14 461 ridgeSupport276_rest_006 =
    (ridgeSupport276_suffix_006, ridgeSupport276_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 429
    ridgeSupport276_rest_006 ridgeSupport276_rest_007 ridgeSupport276_rest_021
    ridgeSupport276_006 ridgeSupport276_suffix_007 ridgeSupport276_006_decode ridgeSupport276_suffix_decode_007
theorem ridgeSupport276_suffix_decode_005 : PackedRawNatGrowth.readList 14 493 ridgeSupport276_rest_005 =
    (ridgeSupport276_suffix_005, ridgeSupport276_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 461
    ridgeSupport276_rest_005 ridgeSupport276_rest_006 ridgeSupport276_rest_021
    ridgeSupport276_005 ridgeSupport276_suffix_006 ridgeSupport276_005_decode ridgeSupport276_suffix_decode_006
theorem ridgeSupport276_suffix_decode_004 : PackedRawNatGrowth.readList 14 525 ridgeSupport276_rest_004 =
    (ridgeSupport276_suffix_004, ridgeSupport276_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 493
    ridgeSupport276_rest_004 ridgeSupport276_rest_005 ridgeSupport276_rest_021
    ridgeSupport276_004 ridgeSupport276_suffix_005 ridgeSupport276_004_decode ridgeSupport276_suffix_decode_005
theorem ridgeSupport276_suffix_decode_003 : PackedRawNatGrowth.readList 14 557 ridgeSupport276_rest_003 =
    (ridgeSupport276_suffix_003, ridgeSupport276_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 525
    ridgeSupport276_rest_003 ridgeSupport276_rest_004 ridgeSupport276_rest_021
    ridgeSupport276_003 ridgeSupport276_suffix_004 ridgeSupport276_003_decode ridgeSupport276_suffix_decode_004
theorem ridgeSupport276_suffix_decode_002 : PackedRawNatGrowth.readList 14 589 ridgeSupport276_rest_002 =
    (ridgeSupport276_suffix_002, ridgeSupport276_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 557
    ridgeSupport276_rest_002 ridgeSupport276_rest_003 ridgeSupport276_rest_021
    ridgeSupport276_002 ridgeSupport276_suffix_003 ridgeSupport276_002_decode ridgeSupport276_suffix_decode_003
theorem ridgeSupport276_suffix_decode_001 : PackedRawNatGrowth.readList 14 621 ridgeSupport276_rest_001 =
    (ridgeSupport276_suffix_001, ridgeSupport276_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 589
    ridgeSupport276_rest_001 ridgeSupport276_rest_002 ridgeSupport276_rest_021
    ridgeSupport276_001 ridgeSupport276_suffix_002 ridgeSupport276_001_decode ridgeSupport276_suffix_decode_002
theorem ridgeSupport276_suffix_decode_000 : PackedRawNatGrowth.readList 14 653 ridgeSupport276_rest_000 =
    (ridgeSupport276_suffix_000, ridgeSupport276_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 621
    ridgeSupport276_rest_000 ridgeSupport276_rest_001 ridgeSupport276_rest_021
    ridgeSupport276_000 ridgeSupport276_suffix_001 ridgeSupport276_000_decode ridgeSupport276_suffix_decode_001
theorem ridgeSupport276_eq : candidateRows 276 = ridgeSupport276_suffix_000 := by
  rw [ridgeSupport276_source]
  exact congrArg Prod.fst ridgeSupport276_suffix_decode_000
theorem ridgeTest_large_276 : ridgeTest 276 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport276_eq]
    simp only [ridgeSupport276_suffix_000, ridgeSupport276_suffix_001, ridgeSupport276_suffix_002, ridgeSupport276_suffix_003, ridgeSupport276_suffix_004, ridgeSupport276_suffix_005, ridgeSupport276_suffix_006, ridgeSupport276_suffix_007, ridgeSupport276_suffix_008, ridgeSupport276_suffix_009, ridgeSupport276_suffix_010, ridgeSupport276_suffix_011, ridgeSupport276_suffix_012, ridgeSupport276_suffix_013, ridgeSupport276_suffix_014, ridgeSupport276_suffix_015, ridgeSupport276_suffix_016, ridgeSupport276_suffix_017, ridgeSupport276_suffix_018, ridgeSupport276_suffix_019, ridgeSupport276_suffix_020, ridgeSupport276_suffix_021, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport276_000_mask, ridgeSupport276_001_mask, ridgeSupport276_002_mask, ridgeSupport276_003_mask, ridgeSupport276_004_mask, ridgeSupport276_005_mask, ridgeSupport276_006_mask, ridgeSupport276_007_mask, ridgeSupport276_008_mask, ridgeSupport276_009_mask, ridgeSupport276_010_mask, ridgeSupport276_011_mask, ridgeSupport276_012_mask, ridgeSupport276_013_mask, ridgeSupport276_014_mask, ridgeSupport276_015_mask, ridgeSupport276_016_mask, ridgeSupport276_017_mask, ridgeSupport276_018_mask, ridgeSupport276_019_mask, ridgeSupport276_020_mask]
    decide +kernel
  · rw [ridgeSupport276_eq]
    simp only [ridgeSupport276_suffix_000, ridgeSupport276_suffix_001, ridgeSupport276_suffix_002, ridgeSupport276_suffix_003, ridgeSupport276_suffix_004, ridgeSupport276_suffix_005, ridgeSupport276_suffix_006, ridgeSupport276_suffix_007, ridgeSupport276_suffix_008, ridgeSupport276_suffix_009, ridgeSupport276_suffix_010, ridgeSupport276_suffix_011, ridgeSupport276_suffix_012, ridgeSupport276_suffix_013, ridgeSupport276_suffix_014, ridgeSupport276_suffix_015, ridgeSupport276_suffix_016, ridgeSupport276_suffix_017, ridgeSupport276_suffix_018, ridgeSupport276_suffix_019, ridgeSupport276_suffix_020, ridgeSupport276_suffix_021, List.all_append, List.all_nil, ridgeSupport276_000_checked, ridgeSupport276_001_checked, ridgeSupport276_002_checked, ridgeSupport276_003_checked, ridgeSupport276_004_checked, ridgeSupport276_005_checked, ridgeSupport276_006_checked, ridgeSupport276_007_checked, ridgeSupport276_008_checked, ridgeSupport276_009_checked, ridgeSupport276_010_checked, ridgeSupport276_011_checked, ridgeSupport276_012_checked, ridgeSupport276_013_checked, ridgeSupport276_014_checked, ridgeSupport276_015_checked, ridgeSupport276_016_checked, ridgeSupport276_017_checked, ridgeSupport276_018_checked, ridgeSupport276_019_checked, ridgeSupport276_020_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase01
