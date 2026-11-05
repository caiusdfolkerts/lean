module
prelude
public import RootedSixBase01GrowthCacheRidgeSupport69Part000
public import RootedSixBase01GrowthCacheRidgeSupport69Part001
public import RootedSixBase01GrowthCacheRidgeSupport69Part002
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport69_suffix_decode_021 : PackedRawNatGrowth.readList 14 0 ridgeSupport69_rest_021 =
    (ridgeSupport69_suffix_021, ridgeSupport69_rest_021) := by rfl
theorem ridgeSupport69_suffix_decode_020 : PackedRawNatGrowth.readList 14 13 ridgeSupport69_rest_020 =
    (ridgeSupport69_suffix_020, ridgeSupport69_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 13 0
    ridgeSupport69_rest_020 ridgeSupport69_rest_021 ridgeSupport69_rest_021
    ridgeSupport69_020 ridgeSupport69_suffix_021 ridgeSupport69_020_decode ridgeSupport69_suffix_decode_021
theorem ridgeSupport69_suffix_decode_019 : PackedRawNatGrowth.readList 14 45 ridgeSupport69_rest_019 =
    (ridgeSupport69_suffix_019, ridgeSupport69_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 13
    ridgeSupport69_rest_019 ridgeSupport69_rest_020 ridgeSupport69_rest_021
    ridgeSupport69_019 ridgeSupport69_suffix_020 ridgeSupport69_019_decode ridgeSupport69_suffix_decode_020
theorem ridgeSupport69_suffix_decode_018 : PackedRawNatGrowth.readList 14 77 ridgeSupport69_rest_018 =
    (ridgeSupport69_suffix_018, ridgeSupport69_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 45
    ridgeSupport69_rest_018 ridgeSupport69_rest_019 ridgeSupport69_rest_021
    ridgeSupport69_018 ridgeSupport69_suffix_019 ridgeSupport69_018_decode ridgeSupport69_suffix_decode_019
theorem ridgeSupport69_suffix_decode_017 : PackedRawNatGrowth.readList 14 109 ridgeSupport69_rest_017 =
    (ridgeSupport69_suffix_017, ridgeSupport69_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 77
    ridgeSupport69_rest_017 ridgeSupport69_rest_018 ridgeSupport69_rest_021
    ridgeSupport69_017 ridgeSupport69_suffix_018 ridgeSupport69_017_decode ridgeSupport69_suffix_decode_018
theorem ridgeSupport69_suffix_decode_016 : PackedRawNatGrowth.readList 14 141 ridgeSupport69_rest_016 =
    (ridgeSupport69_suffix_016, ridgeSupport69_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 109
    ridgeSupport69_rest_016 ridgeSupport69_rest_017 ridgeSupport69_rest_021
    ridgeSupport69_016 ridgeSupport69_suffix_017 ridgeSupport69_016_decode ridgeSupport69_suffix_decode_017
theorem ridgeSupport69_suffix_decode_015 : PackedRawNatGrowth.readList 14 173 ridgeSupport69_rest_015 =
    (ridgeSupport69_suffix_015, ridgeSupport69_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 141
    ridgeSupport69_rest_015 ridgeSupport69_rest_016 ridgeSupport69_rest_021
    ridgeSupport69_015 ridgeSupport69_suffix_016 ridgeSupport69_015_decode ridgeSupport69_suffix_decode_016
theorem ridgeSupport69_suffix_decode_014 : PackedRawNatGrowth.readList 14 205 ridgeSupport69_rest_014 =
    (ridgeSupport69_suffix_014, ridgeSupport69_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 173
    ridgeSupport69_rest_014 ridgeSupport69_rest_015 ridgeSupport69_rest_021
    ridgeSupport69_014 ridgeSupport69_suffix_015 ridgeSupport69_014_decode ridgeSupport69_suffix_decode_015
theorem ridgeSupport69_suffix_decode_013 : PackedRawNatGrowth.readList 14 237 ridgeSupport69_rest_013 =
    (ridgeSupport69_suffix_013, ridgeSupport69_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 205
    ridgeSupport69_rest_013 ridgeSupport69_rest_014 ridgeSupport69_rest_021
    ridgeSupport69_013 ridgeSupport69_suffix_014 ridgeSupport69_013_decode ridgeSupport69_suffix_decode_014
theorem ridgeSupport69_suffix_decode_012 : PackedRawNatGrowth.readList 14 269 ridgeSupport69_rest_012 =
    (ridgeSupport69_suffix_012, ridgeSupport69_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 237
    ridgeSupport69_rest_012 ridgeSupport69_rest_013 ridgeSupport69_rest_021
    ridgeSupport69_012 ridgeSupport69_suffix_013 ridgeSupport69_012_decode ridgeSupport69_suffix_decode_013
theorem ridgeSupport69_suffix_decode_011 : PackedRawNatGrowth.readList 14 301 ridgeSupport69_rest_011 =
    (ridgeSupport69_suffix_011, ridgeSupport69_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 269
    ridgeSupport69_rest_011 ridgeSupport69_rest_012 ridgeSupport69_rest_021
    ridgeSupport69_011 ridgeSupport69_suffix_012 ridgeSupport69_011_decode ridgeSupport69_suffix_decode_012
theorem ridgeSupport69_suffix_decode_010 : PackedRawNatGrowth.readList 14 333 ridgeSupport69_rest_010 =
    (ridgeSupport69_suffix_010, ridgeSupport69_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 301
    ridgeSupport69_rest_010 ridgeSupport69_rest_011 ridgeSupport69_rest_021
    ridgeSupport69_010 ridgeSupport69_suffix_011 ridgeSupport69_010_decode ridgeSupport69_suffix_decode_011
theorem ridgeSupport69_suffix_decode_009 : PackedRawNatGrowth.readList 14 365 ridgeSupport69_rest_009 =
    (ridgeSupport69_suffix_009, ridgeSupport69_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 333
    ridgeSupport69_rest_009 ridgeSupport69_rest_010 ridgeSupport69_rest_021
    ridgeSupport69_009 ridgeSupport69_suffix_010 ridgeSupport69_009_decode ridgeSupport69_suffix_decode_010
theorem ridgeSupport69_suffix_decode_008 : PackedRawNatGrowth.readList 14 397 ridgeSupport69_rest_008 =
    (ridgeSupport69_suffix_008, ridgeSupport69_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 365
    ridgeSupport69_rest_008 ridgeSupport69_rest_009 ridgeSupport69_rest_021
    ridgeSupport69_008 ridgeSupport69_suffix_009 ridgeSupport69_008_decode ridgeSupport69_suffix_decode_009
theorem ridgeSupport69_suffix_decode_007 : PackedRawNatGrowth.readList 14 429 ridgeSupport69_rest_007 =
    (ridgeSupport69_suffix_007, ridgeSupport69_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 397
    ridgeSupport69_rest_007 ridgeSupport69_rest_008 ridgeSupport69_rest_021
    ridgeSupport69_007 ridgeSupport69_suffix_008 ridgeSupport69_007_decode ridgeSupport69_suffix_decode_008
theorem ridgeSupport69_suffix_decode_006 : PackedRawNatGrowth.readList 14 461 ridgeSupport69_rest_006 =
    (ridgeSupport69_suffix_006, ridgeSupport69_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 429
    ridgeSupport69_rest_006 ridgeSupport69_rest_007 ridgeSupport69_rest_021
    ridgeSupport69_006 ridgeSupport69_suffix_007 ridgeSupport69_006_decode ridgeSupport69_suffix_decode_007
theorem ridgeSupport69_suffix_decode_005 : PackedRawNatGrowth.readList 14 493 ridgeSupport69_rest_005 =
    (ridgeSupport69_suffix_005, ridgeSupport69_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 461
    ridgeSupport69_rest_005 ridgeSupport69_rest_006 ridgeSupport69_rest_021
    ridgeSupport69_005 ridgeSupport69_suffix_006 ridgeSupport69_005_decode ridgeSupport69_suffix_decode_006
theorem ridgeSupport69_suffix_decode_004 : PackedRawNatGrowth.readList 14 525 ridgeSupport69_rest_004 =
    (ridgeSupport69_suffix_004, ridgeSupport69_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 493
    ridgeSupport69_rest_004 ridgeSupport69_rest_005 ridgeSupport69_rest_021
    ridgeSupport69_004 ridgeSupport69_suffix_005 ridgeSupport69_004_decode ridgeSupport69_suffix_decode_005
theorem ridgeSupport69_suffix_decode_003 : PackedRawNatGrowth.readList 14 557 ridgeSupport69_rest_003 =
    (ridgeSupport69_suffix_003, ridgeSupport69_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 525
    ridgeSupport69_rest_003 ridgeSupport69_rest_004 ridgeSupport69_rest_021
    ridgeSupport69_003 ridgeSupport69_suffix_004 ridgeSupport69_003_decode ridgeSupport69_suffix_decode_004
theorem ridgeSupport69_suffix_decode_002 : PackedRawNatGrowth.readList 14 589 ridgeSupport69_rest_002 =
    (ridgeSupport69_suffix_002, ridgeSupport69_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 557
    ridgeSupport69_rest_002 ridgeSupport69_rest_003 ridgeSupport69_rest_021
    ridgeSupport69_002 ridgeSupport69_suffix_003 ridgeSupport69_002_decode ridgeSupport69_suffix_decode_003
theorem ridgeSupport69_suffix_decode_001 : PackedRawNatGrowth.readList 14 621 ridgeSupport69_rest_001 =
    (ridgeSupport69_suffix_001, ridgeSupport69_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 589
    ridgeSupport69_rest_001 ridgeSupport69_rest_002 ridgeSupport69_rest_021
    ridgeSupport69_001 ridgeSupport69_suffix_002 ridgeSupport69_001_decode ridgeSupport69_suffix_decode_002
theorem ridgeSupport69_suffix_decode_000 : PackedRawNatGrowth.readList 14 653 ridgeSupport69_rest_000 =
    (ridgeSupport69_suffix_000, ridgeSupport69_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 621
    ridgeSupport69_rest_000 ridgeSupport69_rest_001 ridgeSupport69_rest_021
    ridgeSupport69_000 ridgeSupport69_suffix_001 ridgeSupport69_000_decode ridgeSupport69_suffix_decode_001
theorem ridgeSupport69_eq : candidateRows 69 = ridgeSupport69_suffix_000 := by
  rw [ridgeSupport69_source]
  exact congrArg Prod.fst ridgeSupport69_suffix_decode_000
theorem ridgeTest_large_69 : ridgeTest 69 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport69_eq]
    simp only [ridgeSupport69_suffix_000, ridgeSupport69_suffix_001, ridgeSupport69_suffix_002, ridgeSupport69_suffix_003, ridgeSupport69_suffix_004, ridgeSupport69_suffix_005, ridgeSupport69_suffix_006, ridgeSupport69_suffix_007, ridgeSupport69_suffix_008, ridgeSupport69_suffix_009, ridgeSupport69_suffix_010, ridgeSupport69_suffix_011, ridgeSupport69_suffix_012, ridgeSupport69_suffix_013, ridgeSupport69_suffix_014, ridgeSupport69_suffix_015, ridgeSupport69_suffix_016, ridgeSupport69_suffix_017, ridgeSupport69_suffix_018, ridgeSupport69_suffix_019, ridgeSupport69_suffix_020, ridgeSupport69_suffix_021, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport69_000_mask, ridgeSupport69_001_mask, ridgeSupport69_002_mask, ridgeSupport69_003_mask, ridgeSupport69_004_mask, ridgeSupport69_005_mask, ridgeSupport69_006_mask, ridgeSupport69_007_mask, ridgeSupport69_008_mask, ridgeSupport69_009_mask, ridgeSupport69_010_mask, ridgeSupport69_011_mask, ridgeSupport69_012_mask, ridgeSupport69_013_mask, ridgeSupport69_014_mask, ridgeSupport69_015_mask, ridgeSupport69_016_mask, ridgeSupport69_017_mask, ridgeSupport69_018_mask, ridgeSupport69_019_mask, ridgeSupport69_020_mask]
    decide +kernel
  · rw [ridgeSupport69_eq]
    simp only [ridgeSupport69_suffix_000, ridgeSupport69_suffix_001, ridgeSupport69_suffix_002, ridgeSupport69_suffix_003, ridgeSupport69_suffix_004, ridgeSupport69_suffix_005, ridgeSupport69_suffix_006, ridgeSupport69_suffix_007, ridgeSupport69_suffix_008, ridgeSupport69_suffix_009, ridgeSupport69_suffix_010, ridgeSupport69_suffix_011, ridgeSupport69_suffix_012, ridgeSupport69_suffix_013, ridgeSupport69_suffix_014, ridgeSupport69_suffix_015, ridgeSupport69_suffix_016, ridgeSupport69_suffix_017, ridgeSupport69_suffix_018, ridgeSupport69_suffix_019, ridgeSupport69_suffix_020, ridgeSupport69_suffix_021, List.all_append, List.all_nil, ridgeSupport69_000_checked, ridgeSupport69_001_checked, ridgeSupport69_002_checked, ridgeSupport69_003_checked, ridgeSupport69_004_checked, ridgeSupport69_005_checked, ridgeSupport69_006_checked, ridgeSupport69_007_checked, ridgeSupport69_008_checked, ridgeSupport69_009_checked, ridgeSupport69_010_checked, ridgeSupport69_011_checked, ridgeSupport69_012_checked, ridgeSupport69_013_checked, ridgeSupport69_014_checked, ridgeSupport69_015_checked, ridgeSupport69_016_checked, ridgeSupport69_017_checked, ridgeSupport69_018_checked, ridgeSupport69_019_checked, ridgeSupport69_020_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase01
