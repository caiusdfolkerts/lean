module
prelude
public import RootedSixBase01GrowthCacheRidgeSupport292Part000
public import RootedSixBase01GrowthCacheRidgeSupport292Part001
public import RootedSixBase01GrowthCacheRidgeSupport292Part002
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport292_suffix_decode_021 : PackedRawNatGrowth.readList 14 0 ridgeSupport292_rest_021 =
    (ridgeSupport292_suffix_021, ridgeSupport292_rest_021) := by rfl
theorem ridgeSupport292_suffix_decode_020 : PackedRawNatGrowth.readList 14 13 ridgeSupport292_rest_020 =
    (ridgeSupport292_suffix_020, ridgeSupport292_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 13 0
    ridgeSupport292_rest_020 ridgeSupport292_rest_021 ridgeSupport292_rest_021
    ridgeSupport292_020 ridgeSupport292_suffix_021 ridgeSupport292_020_decode ridgeSupport292_suffix_decode_021
theorem ridgeSupport292_suffix_decode_019 : PackedRawNatGrowth.readList 14 45 ridgeSupport292_rest_019 =
    (ridgeSupport292_suffix_019, ridgeSupport292_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 13
    ridgeSupport292_rest_019 ridgeSupport292_rest_020 ridgeSupport292_rest_021
    ridgeSupport292_019 ridgeSupport292_suffix_020 ridgeSupport292_019_decode ridgeSupport292_suffix_decode_020
theorem ridgeSupport292_suffix_decode_018 : PackedRawNatGrowth.readList 14 77 ridgeSupport292_rest_018 =
    (ridgeSupport292_suffix_018, ridgeSupport292_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 45
    ridgeSupport292_rest_018 ridgeSupport292_rest_019 ridgeSupport292_rest_021
    ridgeSupport292_018 ridgeSupport292_suffix_019 ridgeSupport292_018_decode ridgeSupport292_suffix_decode_019
theorem ridgeSupport292_suffix_decode_017 : PackedRawNatGrowth.readList 14 109 ridgeSupport292_rest_017 =
    (ridgeSupport292_suffix_017, ridgeSupport292_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 77
    ridgeSupport292_rest_017 ridgeSupport292_rest_018 ridgeSupport292_rest_021
    ridgeSupport292_017 ridgeSupport292_suffix_018 ridgeSupport292_017_decode ridgeSupport292_suffix_decode_018
theorem ridgeSupport292_suffix_decode_016 : PackedRawNatGrowth.readList 14 141 ridgeSupport292_rest_016 =
    (ridgeSupport292_suffix_016, ridgeSupport292_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 109
    ridgeSupport292_rest_016 ridgeSupport292_rest_017 ridgeSupport292_rest_021
    ridgeSupport292_016 ridgeSupport292_suffix_017 ridgeSupport292_016_decode ridgeSupport292_suffix_decode_017
theorem ridgeSupport292_suffix_decode_015 : PackedRawNatGrowth.readList 14 173 ridgeSupport292_rest_015 =
    (ridgeSupport292_suffix_015, ridgeSupport292_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 141
    ridgeSupport292_rest_015 ridgeSupport292_rest_016 ridgeSupport292_rest_021
    ridgeSupport292_015 ridgeSupport292_suffix_016 ridgeSupport292_015_decode ridgeSupport292_suffix_decode_016
theorem ridgeSupport292_suffix_decode_014 : PackedRawNatGrowth.readList 14 205 ridgeSupport292_rest_014 =
    (ridgeSupport292_suffix_014, ridgeSupport292_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 173
    ridgeSupport292_rest_014 ridgeSupport292_rest_015 ridgeSupport292_rest_021
    ridgeSupport292_014 ridgeSupport292_suffix_015 ridgeSupport292_014_decode ridgeSupport292_suffix_decode_015
theorem ridgeSupport292_suffix_decode_013 : PackedRawNatGrowth.readList 14 237 ridgeSupport292_rest_013 =
    (ridgeSupport292_suffix_013, ridgeSupport292_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 205
    ridgeSupport292_rest_013 ridgeSupport292_rest_014 ridgeSupport292_rest_021
    ridgeSupport292_013 ridgeSupport292_suffix_014 ridgeSupport292_013_decode ridgeSupport292_suffix_decode_014
theorem ridgeSupport292_suffix_decode_012 : PackedRawNatGrowth.readList 14 269 ridgeSupport292_rest_012 =
    (ridgeSupport292_suffix_012, ridgeSupport292_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 237
    ridgeSupport292_rest_012 ridgeSupport292_rest_013 ridgeSupport292_rest_021
    ridgeSupport292_012 ridgeSupport292_suffix_013 ridgeSupport292_012_decode ridgeSupport292_suffix_decode_013
theorem ridgeSupport292_suffix_decode_011 : PackedRawNatGrowth.readList 14 301 ridgeSupport292_rest_011 =
    (ridgeSupport292_suffix_011, ridgeSupport292_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 269
    ridgeSupport292_rest_011 ridgeSupport292_rest_012 ridgeSupport292_rest_021
    ridgeSupport292_011 ridgeSupport292_suffix_012 ridgeSupport292_011_decode ridgeSupport292_suffix_decode_012
theorem ridgeSupport292_suffix_decode_010 : PackedRawNatGrowth.readList 14 333 ridgeSupport292_rest_010 =
    (ridgeSupport292_suffix_010, ridgeSupport292_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 301
    ridgeSupport292_rest_010 ridgeSupport292_rest_011 ridgeSupport292_rest_021
    ridgeSupport292_010 ridgeSupport292_suffix_011 ridgeSupport292_010_decode ridgeSupport292_suffix_decode_011
theorem ridgeSupport292_suffix_decode_009 : PackedRawNatGrowth.readList 14 365 ridgeSupport292_rest_009 =
    (ridgeSupport292_suffix_009, ridgeSupport292_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 333
    ridgeSupport292_rest_009 ridgeSupport292_rest_010 ridgeSupport292_rest_021
    ridgeSupport292_009 ridgeSupport292_suffix_010 ridgeSupport292_009_decode ridgeSupport292_suffix_decode_010
theorem ridgeSupport292_suffix_decode_008 : PackedRawNatGrowth.readList 14 397 ridgeSupport292_rest_008 =
    (ridgeSupport292_suffix_008, ridgeSupport292_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 365
    ridgeSupport292_rest_008 ridgeSupport292_rest_009 ridgeSupport292_rest_021
    ridgeSupport292_008 ridgeSupport292_suffix_009 ridgeSupport292_008_decode ridgeSupport292_suffix_decode_009
theorem ridgeSupport292_suffix_decode_007 : PackedRawNatGrowth.readList 14 429 ridgeSupport292_rest_007 =
    (ridgeSupport292_suffix_007, ridgeSupport292_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 397
    ridgeSupport292_rest_007 ridgeSupport292_rest_008 ridgeSupport292_rest_021
    ridgeSupport292_007 ridgeSupport292_suffix_008 ridgeSupport292_007_decode ridgeSupport292_suffix_decode_008
theorem ridgeSupport292_suffix_decode_006 : PackedRawNatGrowth.readList 14 461 ridgeSupport292_rest_006 =
    (ridgeSupport292_suffix_006, ridgeSupport292_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 429
    ridgeSupport292_rest_006 ridgeSupport292_rest_007 ridgeSupport292_rest_021
    ridgeSupport292_006 ridgeSupport292_suffix_007 ridgeSupport292_006_decode ridgeSupport292_suffix_decode_007
theorem ridgeSupport292_suffix_decode_005 : PackedRawNatGrowth.readList 14 493 ridgeSupport292_rest_005 =
    (ridgeSupport292_suffix_005, ridgeSupport292_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 461
    ridgeSupport292_rest_005 ridgeSupport292_rest_006 ridgeSupport292_rest_021
    ridgeSupport292_005 ridgeSupport292_suffix_006 ridgeSupport292_005_decode ridgeSupport292_suffix_decode_006
theorem ridgeSupport292_suffix_decode_004 : PackedRawNatGrowth.readList 14 525 ridgeSupport292_rest_004 =
    (ridgeSupport292_suffix_004, ridgeSupport292_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 493
    ridgeSupport292_rest_004 ridgeSupport292_rest_005 ridgeSupport292_rest_021
    ridgeSupport292_004 ridgeSupport292_suffix_005 ridgeSupport292_004_decode ridgeSupport292_suffix_decode_005
theorem ridgeSupport292_suffix_decode_003 : PackedRawNatGrowth.readList 14 557 ridgeSupport292_rest_003 =
    (ridgeSupport292_suffix_003, ridgeSupport292_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 525
    ridgeSupport292_rest_003 ridgeSupport292_rest_004 ridgeSupport292_rest_021
    ridgeSupport292_003 ridgeSupport292_suffix_004 ridgeSupport292_003_decode ridgeSupport292_suffix_decode_004
theorem ridgeSupport292_suffix_decode_002 : PackedRawNatGrowth.readList 14 589 ridgeSupport292_rest_002 =
    (ridgeSupport292_suffix_002, ridgeSupport292_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 557
    ridgeSupport292_rest_002 ridgeSupport292_rest_003 ridgeSupport292_rest_021
    ridgeSupport292_002 ridgeSupport292_suffix_003 ridgeSupport292_002_decode ridgeSupport292_suffix_decode_003
theorem ridgeSupport292_suffix_decode_001 : PackedRawNatGrowth.readList 14 621 ridgeSupport292_rest_001 =
    (ridgeSupport292_suffix_001, ridgeSupport292_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 589
    ridgeSupport292_rest_001 ridgeSupport292_rest_002 ridgeSupport292_rest_021
    ridgeSupport292_001 ridgeSupport292_suffix_002 ridgeSupport292_001_decode ridgeSupport292_suffix_decode_002
theorem ridgeSupport292_suffix_decode_000 : PackedRawNatGrowth.readList 14 653 ridgeSupport292_rest_000 =
    (ridgeSupport292_suffix_000, ridgeSupport292_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 621
    ridgeSupport292_rest_000 ridgeSupport292_rest_001 ridgeSupport292_rest_021
    ridgeSupport292_000 ridgeSupport292_suffix_001 ridgeSupport292_000_decode ridgeSupport292_suffix_decode_001
theorem ridgeSupport292_eq : candidateRows 292 = ridgeSupport292_suffix_000 := by
  rw [ridgeSupport292_source]
  exact congrArg Prod.fst ridgeSupport292_suffix_decode_000
theorem ridgeTest_large_292 : ridgeTest 292 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport292_eq]
    simp only [ridgeSupport292_suffix_000, ridgeSupport292_suffix_001, ridgeSupport292_suffix_002, ridgeSupport292_suffix_003, ridgeSupport292_suffix_004, ridgeSupport292_suffix_005, ridgeSupport292_suffix_006, ridgeSupport292_suffix_007, ridgeSupport292_suffix_008, ridgeSupport292_suffix_009, ridgeSupport292_suffix_010, ridgeSupport292_suffix_011, ridgeSupport292_suffix_012, ridgeSupport292_suffix_013, ridgeSupport292_suffix_014, ridgeSupport292_suffix_015, ridgeSupport292_suffix_016, ridgeSupport292_suffix_017, ridgeSupport292_suffix_018, ridgeSupport292_suffix_019, ridgeSupport292_suffix_020, ridgeSupport292_suffix_021, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport292_000_mask, ridgeSupport292_001_mask, ridgeSupport292_002_mask, ridgeSupport292_003_mask, ridgeSupport292_004_mask, ridgeSupport292_005_mask, ridgeSupport292_006_mask, ridgeSupport292_007_mask, ridgeSupport292_008_mask, ridgeSupport292_009_mask, ridgeSupport292_010_mask, ridgeSupport292_011_mask, ridgeSupport292_012_mask, ridgeSupport292_013_mask, ridgeSupport292_014_mask, ridgeSupport292_015_mask, ridgeSupport292_016_mask, ridgeSupport292_017_mask, ridgeSupport292_018_mask, ridgeSupport292_019_mask, ridgeSupport292_020_mask]
    decide +kernel
  · rw [ridgeSupport292_eq]
    simp only [ridgeSupport292_suffix_000, ridgeSupport292_suffix_001, ridgeSupport292_suffix_002, ridgeSupport292_suffix_003, ridgeSupport292_suffix_004, ridgeSupport292_suffix_005, ridgeSupport292_suffix_006, ridgeSupport292_suffix_007, ridgeSupport292_suffix_008, ridgeSupport292_suffix_009, ridgeSupport292_suffix_010, ridgeSupport292_suffix_011, ridgeSupport292_suffix_012, ridgeSupport292_suffix_013, ridgeSupport292_suffix_014, ridgeSupport292_suffix_015, ridgeSupport292_suffix_016, ridgeSupport292_suffix_017, ridgeSupport292_suffix_018, ridgeSupport292_suffix_019, ridgeSupport292_suffix_020, ridgeSupport292_suffix_021, List.all_append, List.all_nil, ridgeSupport292_000_checked, ridgeSupport292_001_checked, ridgeSupport292_002_checked, ridgeSupport292_003_checked, ridgeSupport292_004_checked, ridgeSupport292_005_checked, ridgeSupport292_006_checked, ridgeSupport292_007_checked, ridgeSupport292_008_checked, ridgeSupport292_009_checked, ridgeSupport292_010_checked, ridgeSupport292_011_checked, ridgeSupport292_012_checked, ridgeSupport292_013_checked, ridgeSupport292_014_checked, ridgeSupport292_015_checked, ridgeSupport292_016_checked, ridgeSupport292_017_checked, ridgeSupport292_018_checked, ridgeSupport292_019_checked, ridgeSupport292_020_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase01
