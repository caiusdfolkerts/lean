module
prelude
public import RootedSixBase01GrowthCacheRidgeSupport100Part000
public import RootedSixBase01GrowthCacheRidgeSupport100Part001
public import RootedSixBase01GrowthCacheRidgeSupport100Part002
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport100_suffix_decode_021 : PackedRawNatGrowth.readList 14 0 ridgeSupport100_rest_021 =
    (ridgeSupport100_suffix_021, ridgeSupport100_rest_021) := by rfl
theorem ridgeSupport100_suffix_decode_020 : PackedRawNatGrowth.readList 14 13 ridgeSupport100_rest_020 =
    (ridgeSupport100_suffix_020, ridgeSupport100_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 13 0
    ridgeSupport100_rest_020 ridgeSupport100_rest_021 ridgeSupport100_rest_021
    ridgeSupport100_020 ridgeSupport100_suffix_021 ridgeSupport100_020_decode ridgeSupport100_suffix_decode_021
theorem ridgeSupport100_suffix_decode_019 : PackedRawNatGrowth.readList 14 45 ridgeSupport100_rest_019 =
    (ridgeSupport100_suffix_019, ridgeSupport100_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 13
    ridgeSupport100_rest_019 ridgeSupport100_rest_020 ridgeSupport100_rest_021
    ridgeSupport100_019 ridgeSupport100_suffix_020 ridgeSupport100_019_decode ridgeSupport100_suffix_decode_020
theorem ridgeSupport100_suffix_decode_018 : PackedRawNatGrowth.readList 14 77 ridgeSupport100_rest_018 =
    (ridgeSupport100_suffix_018, ridgeSupport100_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 45
    ridgeSupport100_rest_018 ridgeSupport100_rest_019 ridgeSupport100_rest_021
    ridgeSupport100_018 ridgeSupport100_suffix_019 ridgeSupport100_018_decode ridgeSupport100_suffix_decode_019
theorem ridgeSupport100_suffix_decode_017 : PackedRawNatGrowth.readList 14 109 ridgeSupport100_rest_017 =
    (ridgeSupport100_suffix_017, ridgeSupport100_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 77
    ridgeSupport100_rest_017 ridgeSupport100_rest_018 ridgeSupport100_rest_021
    ridgeSupport100_017 ridgeSupport100_suffix_018 ridgeSupport100_017_decode ridgeSupport100_suffix_decode_018
theorem ridgeSupport100_suffix_decode_016 : PackedRawNatGrowth.readList 14 141 ridgeSupport100_rest_016 =
    (ridgeSupport100_suffix_016, ridgeSupport100_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 109
    ridgeSupport100_rest_016 ridgeSupport100_rest_017 ridgeSupport100_rest_021
    ridgeSupport100_016 ridgeSupport100_suffix_017 ridgeSupport100_016_decode ridgeSupport100_suffix_decode_017
theorem ridgeSupport100_suffix_decode_015 : PackedRawNatGrowth.readList 14 173 ridgeSupport100_rest_015 =
    (ridgeSupport100_suffix_015, ridgeSupport100_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 141
    ridgeSupport100_rest_015 ridgeSupport100_rest_016 ridgeSupport100_rest_021
    ridgeSupport100_015 ridgeSupport100_suffix_016 ridgeSupport100_015_decode ridgeSupport100_suffix_decode_016
theorem ridgeSupport100_suffix_decode_014 : PackedRawNatGrowth.readList 14 205 ridgeSupport100_rest_014 =
    (ridgeSupport100_suffix_014, ridgeSupport100_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 173
    ridgeSupport100_rest_014 ridgeSupport100_rest_015 ridgeSupport100_rest_021
    ridgeSupport100_014 ridgeSupport100_suffix_015 ridgeSupport100_014_decode ridgeSupport100_suffix_decode_015
theorem ridgeSupport100_suffix_decode_013 : PackedRawNatGrowth.readList 14 237 ridgeSupport100_rest_013 =
    (ridgeSupport100_suffix_013, ridgeSupport100_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 205
    ridgeSupport100_rest_013 ridgeSupport100_rest_014 ridgeSupport100_rest_021
    ridgeSupport100_013 ridgeSupport100_suffix_014 ridgeSupport100_013_decode ridgeSupport100_suffix_decode_014
theorem ridgeSupport100_suffix_decode_012 : PackedRawNatGrowth.readList 14 269 ridgeSupport100_rest_012 =
    (ridgeSupport100_suffix_012, ridgeSupport100_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 237
    ridgeSupport100_rest_012 ridgeSupport100_rest_013 ridgeSupport100_rest_021
    ridgeSupport100_012 ridgeSupport100_suffix_013 ridgeSupport100_012_decode ridgeSupport100_suffix_decode_013
theorem ridgeSupport100_suffix_decode_011 : PackedRawNatGrowth.readList 14 301 ridgeSupport100_rest_011 =
    (ridgeSupport100_suffix_011, ridgeSupport100_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 269
    ridgeSupport100_rest_011 ridgeSupport100_rest_012 ridgeSupport100_rest_021
    ridgeSupport100_011 ridgeSupport100_suffix_012 ridgeSupport100_011_decode ridgeSupport100_suffix_decode_012
theorem ridgeSupport100_suffix_decode_010 : PackedRawNatGrowth.readList 14 333 ridgeSupport100_rest_010 =
    (ridgeSupport100_suffix_010, ridgeSupport100_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 301
    ridgeSupport100_rest_010 ridgeSupport100_rest_011 ridgeSupport100_rest_021
    ridgeSupport100_010 ridgeSupport100_suffix_011 ridgeSupport100_010_decode ridgeSupport100_suffix_decode_011
theorem ridgeSupport100_suffix_decode_009 : PackedRawNatGrowth.readList 14 365 ridgeSupport100_rest_009 =
    (ridgeSupport100_suffix_009, ridgeSupport100_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 333
    ridgeSupport100_rest_009 ridgeSupport100_rest_010 ridgeSupport100_rest_021
    ridgeSupport100_009 ridgeSupport100_suffix_010 ridgeSupport100_009_decode ridgeSupport100_suffix_decode_010
theorem ridgeSupport100_suffix_decode_008 : PackedRawNatGrowth.readList 14 397 ridgeSupport100_rest_008 =
    (ridgeSupport100_suffix_008, ridgeSupport100_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 365
    ridgeSupport100_rest_008 ridgeSupport100_rest_009 ridgeSupport100_rest_021
    ridgeSupport100_008 ridgeSupport100_suffix_009 ridgeSupport100_008_decode ridgeSupport100_suffix_decode_009
theorem ridgeSupport100_suffix_decode_007 : PackedRawNatGrowth.readList 14 429 ridgeSupport100_rest_007 =
    (ridgeSupport100_suffix_007, ridgeSupport100_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 397
    ridgeSupport100_rest_007 ridgeSupport100_rest_008 ridgeSupport100_rest_021
    ridgeSupport100_007 ridgeSupport100_suffix_008 ridgeSupport100_007_decode ridgeSupport100_suffix_decode_008
theorem ridgeSupport100_suffix_decode_006 : PackedRawNatGrowth.readList 14 461 ridgeSupport100_rest_006 =
    (ridgeSupport100_suffix_006, ridgeSupport100_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 429
    ridgeSupport100_rest_006 ridgeSupport100_rest_007 ridgeSupport100_rest_021
    ridgeSupport100_006 ridgeSupport100_suffix_007 ridgeSupport100_006_decode ridgeSupport100_suffix_decode_007
theorem ridgeSupport100_suffix_decode_005 : PackedRawNatGrowth.readList 14 493 ridgeSupport100_rest_005 =
    (ridgeSupport100_suffix_005, ridgeSupport100_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 461
    ridgeSupport100_rest_005 ridgeSupport100_rest_006 ridgeSupport100_rest_021
    ridgeSupport100_005 ridgeSupport100_suffix_006 ridgeSupport100_005_decode ridgeSupport100_suffix_decode_006
theorem ridgeSupport100_suffix_decode_004 : PackedRawNatGrowth.readList 14 525 ridgeSupport100_rest_004 =
    (ridgeSupport100_suffix_004, ridgeSupport100_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 493
    ridgeSupport100_rest_004 ridgeSupport100_rest_005 ridgeSupport100_rest_021
    ridgeSupport100_004 ridgeSupport100_suffix_005 ridgeSupport100_004_decode ridgeSupport100_suffix_decode_005
theorem ridgeSupport100_suffix_decode_003 : PackedRawNatGrowth.readList 14 557 ridgeSupport100_rest_003 =
    (ridgeSupport100_suffix_003, ridgeSupport100_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 525
    ridgeSupport100_rest_003 ridgeSupport100_rest_004 ridgeSupport100_rest_021
    ridgeSupport100_003 ridgeSupport100_suffix_004 ridgeSupport100_003_decode ridgeSupport100_suffix_decode_004
theorem ridgeSupport100_suffix_decode_002 : PackedRawNatGrowth.readList 14 589 ridgeSupport100_rest_002 =
    (ridgeSupport100_suffix_002, ridgeSupport100_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 557
    ridgeSupport100_rest_002 ridgeSupport100_rest_003 ridgeSupport100_rest_021
    ridgeSupport100_002 ridgeSupport100_suffix_003 ridgeSupport100_002_decode ridgeSupport100_suffix_decode_003
theorem ridgeSupport100_suffix_decode_001 : PackedRawNatGrowth.readList 14 621 ridgeSupport100_rest_001 =
    (ridgeSupport100_suffix_001, ridgeSupport100_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 589
    ridgeSupport100_rest_001 ridgeSupport100_rest_002 ridgeSupport100_rest_021
    ridgeSupport100_001 ridgeSupport100_suffix_002 ridgeSupport100_001_decode ridgeSupport100_suffix_decode_002
theorem ridgeSupport100_suffix_decode_000 : PackedRawNatGrowth.readList 14 653 ridgeSupport100_rest_000 =
    (ridgeSupport100_suffix_000, ridgeSupport100_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 621
    ridgeSupport100_rest_000 ridgeSupport100_rest_001 ridgeSupport100_rest_021
    ridgeSupport100_000 ridgeSupport100_suffix_001 ridgeSupport100_000_decode ridgeSupport100_suffix_decode_001
theorem ridgeSupport100_eq : candidateRows 100 = ridgeSupport100_suffix_000 := by
  rw [ridgeSupport100_source]
  exact congrArg Prod.fst ridgeSupport100_suffix_decode_000
theorem ridgeTest_large_100 : ridgeTest 100 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport100_eq]
    simp only [ridgeSupport100_suffix_000, ridgeSupport100_suffix_001, ridgeSupport100_suffix_002, ridgeSupport100_suffix_003, ridgeSupport100_suffix_004, ridgeSupport100_suffix_005, ridgeSupport100_suffix_006, ridgeSupport100_suffix_007, ridgeSupport100_suffix_008, ridgeSupport100_suffix_009, ridgeSupport100_suffix_010, ridgeSupport100_suffix_011, ridgeSupport100_suffix_012, ridgeSupport100_suffix_013, ridgeSupport100_suffix_014, ridgeSupport100_suffix_015, ridgeSupport100_suffix_016, ridgeSupport100_suffix_017, ridgeSupport100_suffix_018, ridgeSupport100_suffix_019, ridgeSupport100_suffix_020, ridgeSupport100_suffix_021, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport100_000_mask, ridgeSupport100_001_mask, ridgeSupport100_002_mask, ridgeSupport100_003_mask, ridgeSupport100_004_mask, ridgeSupport100_005_mask, ridgeSupport100_006_mask, ridgeSupport100_007_mask, ridgeSupport100_008_mask, ridgeSupport100_009_mask, ridgeSupport100_010_mask, ridgeSupport100_011_mask, ridgeSupport100_012_mask, ridgeSupport100_013_mask, ridgeSupport100_014_mask, ridgeSupport100_015_mask, ridgeSupport100_016_mask, ridgeSupport100_017_mask, ridgeSupport100_018_mask, ridgeSupport100_019_mask, ridgeSupport100_020_mask]
    decide +kernel
  · rw [ridgeSupport100_eq]
    simp only [ridgeSupport100_suffix_000, ridgeSupport100_suffix_001, ridgeSupport100_suffix_002, ridgeSupport100_suffix_003, ridgeSupport100_suffix_004, ridgeSupport100_suffix_005, ridgeSupport100_suffix_006, ridgeSupport100_suffix_007, ridgeSupport100_suffix_008, ridgeSupport100_suffix_009, ridgeSupport100_suffix_010, ridgeSupport100_suffix_011, ridgeSupport100_suffix_012, ridgeSupport100_suffix_013, ridgeSupport100_suffix_014, ridgeSupport100_suffix_015, ridgeSupport100_suffix_016, ridgeSupport100_suffix_017, ridgeSupport100_suffix_018, ridgeSupport100_suffix_019, ridgeSupport100_suffix_020, ridgeSupport100_suffix_021, List.all_append, List.all_nil, ridgeSupport100_000_checked, ridgeSupport100_001_checked, ridgeSupport100_002_checked, ridgeSupport100_003_checked, ridgeSupport100_004_checked, ridgeSupport100_005_checked, ridgeSupport100_006_checked, ridgeSupport100_007_checked, ridgeSupport100_008_checked, ridgeSupport100_009_checked, ridgeSupport100_010_checked, ridgeSupport100_011_checked, ridgeSupport100_012_checked, ridgeSupport100_013_checked, ridgeSupport100_014_checked, ridgeSupport100_015_checked, ridgeSupport100_016_checked, ridgeSupport100_017_checked, ridgeSupport100_018_checked, ridgeSupport100_019_checked, ridgeSupport100_020_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase01
