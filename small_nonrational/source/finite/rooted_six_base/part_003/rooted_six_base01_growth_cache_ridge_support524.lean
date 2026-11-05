module
prelude
public import RootedSixBase01GrowthCacheRidgeSupport524Part000
public import RootedSixBase01GrowthCacheRidgeSupport524Part001
public import RootedSixBase01GrowthCacheRidgeSupport524Part002
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport524_suffix_decode_021 : PackedRawNatGrowth.readList 14 0 ridgeSupport524_rest_021 =
    (ridgeSupport524_suffix_021, ridgeSupport524_rest_021) := by rfl
theorem ridgeSupport524_suffix_decode_020 : PackedRawNatGrowth.readList 14 13 ridgeSupport524_rest_020 =
    (ridgeSupport524_suffix_020, ridgeSupport524_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 13 0
    ridgeSupport524_rest_020 ridgeSupport524_rest_021 ridgeSupport524_rest_021
    ridgeSupport524_020 ridgeSupport524_suffix_021 ridgeSupport524_020_decode ridgeSupport524_suffix_decode_021
theorem ridgeSupport524_suffix_decode_019 : PackedRawNatGrowth.readList 14 45 ridgeSupport524_rest_019 =
    (ridgeSupport524_suffix_019, ridgeSupport524_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 13
    ridgeSupport524_rest_019 ridgeSupport524_rest_020 ridgeSupport524_rest_021
    ridgeSupport524_019 ridgeSupport524_suffix_020 ridgeSupport524_019_decode ridgeSupport524_suffix_decode_020
theorem ridgeSupport524_suffix_decode_018 : PackedRawNatGrowth.readList 14 77 ridgeSupport524_rest_018 =
    (ridgeSupport524_suffix_018, ridgeSupport524_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 45
    ridgeSupport524_rest_018 ridgeSupport524_rest_019 ridgeSupport524_rest_021
    ridgeSupport524_018 ridgeSupport524_suffix_019 ridgeSupport524_018_decode ridgeSupport524_suffix_decode_019
theorem ridgeSupport524_suffix_decode_017 : PackedRawNatGrowth.readList 14 109 ridgeSupport524_rest_017 =
    (ridgeSupport524_suffix_017, ridgeSupport524_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 77
    ridgeSupport524_rest_017 ridgeSupport524_rest_018 ridgeSupport524_rest_021
    ridgeSupport524_017 ridgeSupport524_suffix_018 ridgeSupport524_017_decode ridgeSupport524_suffix_decode_018
theorem ridgeSupport524_suffix_decode_016 : PackedRawNatGrowth.readList 14 141 ridgeSupport524_rest_016 =
    (ridgeSupport524_suffix_016, ridgeSupport524_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 109
    ridgeSupport524_rest_016 ridgeSupport524_rest_017 ridgeSupport524_rest_021
    ridgeSupport524_016 ridgeSupport524_suffix_017 ridgeSupport524_016_decode ridgeSupport524_suffix_decode_017
theorem ridgeSupport524_suffix_decode_015 : PackedRawNatGrowth.readList 14 173 ridgeSupport524_rest_015 =
    (ridgeSupport524_suffix_015, ridgeSupport524_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 141
    ridgeSupport524_rest_015 ridgeSupport524_rest_016 ridgeSupport524_rest_021
    ridgeSupport524_015 ridgeSupport524_suffix_016 ridgeSupport524_015_decode ridgeSupport524_suffix_decode_016
theorem ridgeSupport524_suffix_decode_014 : PackedRawNatGrowth.readList 14 205 ridgeSupport524_rest_014 =
    (ridgeSupport524_suffix_014, ridgeSupport524_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 173
    ridgeSupport524_rest_014 ridgeSupport524_rest_015 ridgeSupport524_rest_021
    ridgeSupport524_014 ridgeSupport524_suffix_015 ridgeSupport524_014_decode ridgeSupport524_suffix_decode_015
theorem ridgeSupport524_suffix_decode_013 : PackedRawNatGrowth.readList 14 237 ridgeSupport524_rest_013 =
    (ridgeSupport524_suffix_013, ridgeSupport524_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 205
    ridgeSupport524_rest_013 ridgeSupport524_rest_014 ridgeSupport524_rest_021
    ridgeSupport524_013 ridgeSupport524_suffix_014 ridgeSupport524_013_decode ridgeSupport524_suffix_decode_014
theorem ridgeSupport524_suffix_decode_012 : PackedRawNatGrowth.readList 14 269 ridgeSupport524_rest_012 =
    (ridgeSupport524_suffix_012, ridgeSupport524_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 237
    ridgeSupport524_rest_012 ridgeSupport524_rest_013 ridgeSupport524_rest_021
    ridgeSupport524_012 ridgeSupport524_suffix_013 ridgeSupport524_012_decode ridgeSupport524_suffix_decode_013
theorem ridgeSupport524_suffix_decode_011 : PackedRawNatGrowth.readList 14 301 ridgeSupport524_rest_011 =
    (ridgeSupport524_suffix_011, ridgeSupport524_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 269
    ridgeSupport524_rest_011 ridgeSupport524_rest_012 ridgeSupport524_rest_021
    ridgeSupport524_011 ridgeSupport524_suffix_012 ridgeSupport524_011_decode ridgeSupport524_suffix_decode_012
theorem ridgeSupport524_suffix_decode_010 : PackedRawNatGrowth.readList 14 333 ridgeSupport524_rest_010 =
    (ridgeSupport524_suffix_010, ridgeSupport524_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 301
    ridgeSupport524_rest_010 ridgeSupport524_rest_011 ridgeSupport524_rest_021
    ridgeSupport524_010 ridgeSupport524_suffix_011 ridgeSupport524_010_decode ridgeSupport524_suffix_decode_011
theorem ridgeSupport524_suffix_decode_009 : PackedRawNatGrowth.readList 14 365 ridgeSupport524_rest_009 =
    (ridgeSupport524_suffix_009, ridgeSupport524_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 333
    ridgeSupport524_rest_009 ridgeSupport524_rest_010 ridgeSupport524_rest_021
    ridgeSupport524_009 ridgeSupport524_suffix_010 ridgeSupport524_009_decode ridgeSupport524_suffix_decode_010
theorem ridgeSupport524_suffix_decode_008 : PackedRawNatGrowth.readList 14 397 ridgeSupport524_rest_008 =
    (ridgeSupport524_suffix_008, ridgeSupport524_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 365
    ridgeSupport524_rest_008 ridgeSupport524_rest_009 ridgeSupport524_rest_021
    ridgeSupport524_008 ridgeSupport524_suffix_009 ridgeSupport524_008_decode ridgeSupport524_suffix_decode_009
theorem ridgeSupport524_suffix_decode_007 : PackedRawNatGrowth.readList 14 429 ridgeSupport524_rest_007 =
    (ridgeSupport524_suffix_007, ridgeSupport524_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 397
    ridgeSupport524_rest_007 ridgeSupport524_rest_008 ridgeSupport524_rest_021
    ridgeSupport524_007 ridgeSupport524_suffix_008 ridgeSupport524_007_decode ridgeSupport524_suffix_decode_008
theorem ridgeSupport524_suffix_decode_006 : PackedRawNatGrowth.readList 14 461 ridgeSupport524_rest_006 =
    (ridgeSupport524_suffix_006, ridgeSupport524_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 429
    ridgeSupport524_rest_006 ridgeSupport524_rest_007 ridgeSupport524_rest_021
    ridgeSupport524_006 ridgeSupport524_suffix_007 ridgeSupport524_006_decode ridgeSupport524_suffix_decode_007
theorem ridgeSupport524_suffix_decode_005 : PackedRawNatGrowth.readList 14 493 ridgeSupport524_rest_005 =
    (ridgeSupport524_suffix_005, ridgeSupport524_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 461
    ridgeSupport524_rest_005 ridgeSupport524_rest_006 ridgeSupport524_rest_021
    ridgeSupport524_005 ridgeSupport524_suffix_006 ridgeSupport524_005_decode ridgeSupport524_suffix_decode_006
theorem ridgeSupport524_suffix_decode_004 : PackedRawNatGrowth.readList 14 525 ridgeSupport524_rest_004 =
    (ridgeSupport524_suffix_004, ridgeSupport524_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 493
    ridgeSupport524_rest_004 ridgeSupport524_rest_005 ridgeSupport524_rest_021
    ridgeSupport524_004 ridgeSupport524_suffix_005 ridgeSupport524_004_decode ridgeSupport524_suffix_decode_005
theorem ridgeSupport524_suffix_decode_003 : PackedRawNatGrowth.readList 14 557 ridgeSupport524_rest_003 =
    (ridgeSupport524_suffix_003, ridgeSupport524_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 525
    ridgeSupport524_rest_003 ridgeSupport524_rest_004 ridgeSupport524_rest_021
    ridgeSupport524_003 ridgeSupport524_suffix_004 ridgeSupport524_003_decode ridgeSupport524_suffix_decode_004
theorem ridgeSupport524_suffix_decode_002 : PackedRawNatGrowth.readList 14 589 ridgeSupport524_rest_002 =
    (ridgeSupport524_suffix_002, ridgeSupport524_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 557
    ridgeSupport524_rest_002 ridgeSupport524_rest_003 ridgeSupport524_rest_021
    ridgeSupport524_002 ridgeSupport524_suffix_003 ridgeSupport524_002_decode ridgeSupport524_suffix_decode_003
theorem ridgeSupport524_suffix_decode_001 : PackedRawNatGrowth.readList 14 621 ridgeSupport524_rest_001 =
    (ridgeSupport524_suffix_001, ridgeSupport524_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 589
    ridgeSupport524_rest_001 ridgeSupport524_rest_002 ridgeSupport524_rest_021
    ridgeSupport524_001 ridgeSupport524_suffix_002 ridgeSupport524_001_decode ridgeSupport524_suffix_decode_002
theorem ridgeSupport524_suffix_decode_000 : PackedRawNatGrowth.readList 14 653 ridgeSupport524_rest_000 =
    (ridgeSupport524_suffix_000, ridgeSupport524_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 621
    ridgeSupport524_rest_000 ridgeSupport524_rest_001 ridgeSupport524_rest_021
    ridgeSupport524_000 ridgeSupport524_suffix_001 ridgeSupport524_000_decode ridgeSupport524_suffix_decode_001
theorem ridgeSupport524_eq : candidateRows 524 = ridgeSupport524_suffix_000 := by
  rw [ridgeSupport524_source]
  exact congrArg Prod.fst ridgeSupport524_suffix_decode_000
theorem ridgeTest_large_524 : ridgeTest 524 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport524_eq]
    simp only [ridgeSupport524_suffix_000, ridgeSupport524_suffix_001, ridgeSupport524_suffix_002, ridgeSupport524_suffix_003, ridgeSupport524_suffix_004, ridgeSupport524_suffix_005, ridgeSupport524_suffix_006, ridgeSupport524_suffix_007, ridgeSupport524_suffix_008, ridgeSupport524_suffix_009, ridgeSupport524_suffix_010, ridgeSupport524_suffix_011, ridgeSupport524_suffix_012, ridgeSupport524_suffix_013, ridgeSupport524_suffix_014, ridgeSupport524_suffix_015, ridgeSupport524_suffix_016, ridgeSupport524_suffix_017, ridgeSupport524_suffix_018, ridgeSupport524_suffix_019, ridgeSupport524_suffix_020, ridgeSupport524_suffix_021, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport524_000_mask, ridgeSupport524_001_mask, ridgeSupport524_002_mask, ridgeSupport524_003_mask, ridgeSupport524_004_mask, ridgeSupport524_005_mask, ridgeSupport524_006_mask, ridgeSupport524_007_mask, ridgeSupport524_008_mask, ridgeSupport524_009_mask, ridgeSupport524_010_mask, ridgeSupport524_011_mask, ridgeSupport524_012_mask, ridgeSupport524_013_mask, ridgeSupport524_014_mask, ridgeSupport524_015_mask, ridgeSupport524_016_mask, ridgeSupport524_017_mask, ridgeSupport524_018_mask, ridgeSupport524_019_mask, ridgeSupport524_020_mask]
    decide +kernel
  · rw [ridgeSupport524_eq]
    simp only [ridgeSupport524_suffix_000, ridgeSupport524_suffix_001, ridgeSupport524_suffix_002, ridgeSupport524_suffix_003, ridgeSupport524_suffix_004, ridgeSupport524_suffix_005, ridgeSupport524_suffix_006, ridgeSupport524_suffix_007, ridgeSupport524_suffix_008, ridgeSupport524_suffix_009, ridgeSupport524_suffix_010, ridgeSupport524_suffix_011, ridgeSupport524_suffix_012, ridgeSupport524_suffix_013, ridgeSupport524_suffix_014, ridgeSupport524_suffix_015, ridgeSupport524_suffix_016, ridgeSupport524_suffix_017, ridgeSupport524_suffix_018, ridgeSupport524_suffix_019, ridgeSupport524_suffix_020, ridgeSupport524_suffix_021, List.all_append, List.all_nil, ridgeSupport524_000_checked, ridgeSupport524_001_checked, ridgeSupport524_002_checked, ridgeSupport524_003_checked, ridgeSupport524_004_checked, ridgeSupport524_005_checked, ridgeSupport524_006_checked, ridgeSupport524_007_checked, ridgeSupport524_008_checked, ridgeSupport524_009_checked, ridgeSupport524_010_checked, ridgeSupport524_011_checked, ridgeSupport524_012_checked, ridgeSupport524_013_checked, ridgeSupport524_014_checked, ridgeSupport524_015_checked, ridgeSupport524_016_checked, ridgeSupport524_017_checked, ridgeSupport524_018_checked, ridgeSupport524_019_checked, ridgeSupport524_020_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase01
