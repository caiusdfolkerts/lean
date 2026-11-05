module
prelude
public import RootedSixBase01GrowthCacheRidgeSupport268Part000
public import RootedSixBase01GrowthCacheRidgeSupport268Part001
public import RootedSixBase01GrowthCacheRidgeSupport268Part002
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport268_suffix_decode_021 : PackedRawNatGrowth.readList 14 0 ridgeSupport268_rest_021 =
    (ridgeSupport268_suffix_021, ridgeSupport268_rest_021) := by rfl
theorem ridgeSupport268_suffix_decode_020 : PackedRawNatGrowth.readList 14 13 ridgeSupport268_rest_020 =
    (ridgeSupport268_suffix_020, ridgeSupport268_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 13 0
    ridgeSupport268_rest_020 ridgeSupport268_rest_021 ridgeSupport268_rest_021
    ridgeSupport268_020 ridgeSupport268_suffix_021 ridgeSupport268_020_decode ridgeSupport268_suffix_decode_021
theorem ridgeSupport268_suffix_decode_019 : PackedRawNatGrowth.readList 14 45 ridgeSupport268_rest_019 =
    (ridgeSupport268_suffix_019, ridgeSupport268_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 13
    ridgeSupport268_rest_019 ridgeSupport268_rest_020 ridgeSupport268_rest_021
    ridgeSupport268_019 ridgeSupport268_suffix_020 ridgeSupport268_019_decode ridgeSupport268_suffix_decode_020
theorem ridgeSupport268_suffix_decode_018 : PackedRawNatGrowth.readList 14 77 ridgeSupport268_rest_018 =
    (ridgeSupport268_suffix_018, ridgeSupport268_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 45
    ridgeSupport268_rest_018 ridgeSupport268_rest_019 ridgeSupport268_rest_021
    ridgeSupport268_018 ridgeSupport268_suffix_019 ridgeSupport268_018_decode ridgeSupport268_suffix_decode_019
theorem ridgeSupport268_suffix_decode_017 : PackedRawNatGrowth.readList 14 109 ridgeSupport268_rest_017 =
    (ridgeSupport268_suffix_017, ridgeSupport268_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 77
    ridgeSupport268_rest_017 ridgeSupport268_rest_018 ridgeSupport268_rest_021
    ridgeSupport268_017 ridgeSupport268_suffix_018 ridgeSupport268_017_decode ridgeSupport268_suffix_decode_018
theorem ridgeSupport268_suffix_decode_016 : PackedRawNatGrowth.readList 14 141 ridgeSupport268_rest_016 =
    (ridgeSupport268_suffix_016, ridgeSupport268_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 109
    ridgeSupport268_rest_016 ridgeSupport268_rest_017 ridgeSupport268_rest_021
    ridgeSupport268_016 ridgeSupport268_suffix_017 ridgeSupport268_016_decode ridgeSupport268_suffix_decode_017
theorem ridgeSupport268_suffix_decode_015 : PackedRawNatGrowth.readList 14 173 ridgeSupport268_rest_015 =
    (ridgeSupport268_suffix_015, ridgeSupport268_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 141
    ridgeSupport268_rest_015 ridgeSupport268_rest_016 ridgeSupport268_rest_021
    ridgeSupport268_015 ridgeSupport268_suffix_016 ridgeSupport268_015_decode ridgeSupport268_suffix_decode_016
theorem ridgeSupport268_suffix_decode_014 : PackedRawNatGrowth.readList 14 205 ridgeSupport268_rest_014 =
    (ridgeSupport268_suffix_014, ridgeSupport268_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 173
    ridgeSupport268_rest_014 ridgeSupport268_rest_015 ridgeSupport268_rest_021
    ridgeSupport268_014 ridgeSupport268_suffix_015 ridgeSupport268_014_decode ridgeSupport268_suffix_decode_015
theorem ridgeSupport268_suffix_decode_013 : PackedRawNatGrowth.readList 14 237 ridgeSupport268_rest_013 =
    (ridgeSupport268_suffix_013, ridgeSupport268_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 205
    ridgeSupport268_rest_013 ridgeSupport268_rest_014 ridgeSupport268_rest_021
    ridgeSupport268_013 ridgeSupport268_suffix_014 ridgeSupport268_013_decode ridgeSupport268_suffix_decode_014
theorem ridgeSupport268_suffix_decode_012 : PackedRawNatGrowth.readList 14 269 ridgeSupport268_rest_012 =
    (ridgeSupport268_suffix_012, ridgeSupport268_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 237
    ridgeSupport268_rest_012 ridgeSupport268_rest_013 ridgeSupport268_rest_021
    ridgeSupport268_012 ridgeSupport268_suffix_013 ridgeSupport268_012_decode ridgeSupport268_suffix_decode_013
theorem ridgeSupport268_suffix_decode_011 : PackedRawNatGrowth.readList 14 301 ridgeSupport268_rest_011 =
    (ridgeSupport268_suffix_011, ridgeSupport268_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 269
    ridgeSupport268_rest_011 ridgeSupport268_rest_012 ridgeSupport268_rest_021
    ridgeSupport268_011 ridgeSupport268_suffix_012 ridgeSupport268_011_decode ridgeSupport268_suffix_decode_012
theorem ridgeSupport268_suffix_decode_010 : PackedRawNatGrowth.readList 14 333 ridgeSupport268_rest_010 =
    (ridgeSupport268_suffix_010, ridgeSupport268_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 301
    ridgeSupport268_rest_010 ridgeSupport268_rest_011 ridgeSupport268_rest_021
    ridgeSupport268_010 ridgeSupport268_suffix_011 ridgeSupport268_010_decode ridgeSupport268_suffix_decode_011
theorem ridgeSupport268_suffix_decode_009 : PackedRawNatGrowth.readList 14 365 ridgeSupport268_rest_009 =
    (ridgeSupport268_suffix_009, ridgeSupport268_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 333
    ridgeSupport268_rest_009 ridgeSupport268_rest_010 ridgeSupport268_rest_021
    ridgeSupport268_009 ridgeSupport268_suffix_010 ridgeSupport268_009_decode ridgeSupport268_suffix_decode_010
theorem ridgeSupport268_suffix_decode_008 : PackedRawNatGrowth.readList 14 397 ridgeSupport268_rest_008 =
    (ridgeSupport268_suffix_008, ridgeSupport268_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 365
    ridgeSupport268_rest_008 ridgeSupport268_rest_009 ridgeSupport268_rest_021
    ridgeSupport268_008 ridgeSupport268_suffix_009 ridgeSupport268_008_decode ridgeSupport268_suffix_decode_009
theorem ridgeSupport268_suffix_decode_007 : PackedRawNatGrowth.readList 14 429 ridgeSupport268_rest_007 =
    (ridgeSupport268_suffix_007, ridgeSupport268_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 397
    ridgeSupport268_rest_007 ridgeSupport268_rest_008 ridgeSupport268_rest_021
    ridgeSupport268_007 ridgeSupport268_suffix_008 ridgeSupport268_007_decode ridgeSupport268_suffix_decode_008
theorem ridgeSupport268_suffix_decode_006 : PackedRawNatGrowth.readList 14 461 ridgeSupport268_rest_006 =
    (ridgeSupport268_suffix_006, ridgeSupport268_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 429
    ridgeSupport268_rest_006 ridgeSupport268_rest_007 ridgeSupport268_rest_021
    ridgeSupport268_006 ridgeSupport268_suffix_007 ridgeSupport268_006_decode ridgeSupport268_suffix_decode_007
theorem ridgeSupport268_suffix_decode_005 : PackedRawNatGrowth.readList 14 493 ridgeSupport268_rest_005 =
    (ridgeSupport268_suffix_005, ridgeSupport268_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 461
    ridgeSupport268_rest_005 ridgeSupport268_rest_006 ridgeSupport268_rest_021
    ridgeSupport268_005 ridgeSupport268_suffix_006 ridgeSupport268_005_decode ridgeSupport268_suffix_decode_006
theorem ridgeSupport268_suffix_decode_004 : PackedRawNatGrowth.readList 14 525 ridgeSupport268_rest_004 =
    (ridgeSupport268_suffix_004, ridgeSupport268_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 493
    ridgeSupport268_rest_004 ridgeSupport268_rest_005 ridgeSupport268_rest_021
    ridgeSupport268_004 ridgeSupport268_suffix_005 ridgeSupport268_004_decode ridgeSupport268_suffix_decode_005
theorem ridgeSupport268_suffix_decode_003 : PackedRawNatGrowth.readList 14 557 ridgeSupport268_rest_003 =
    (ridgeSupport268_suffix_003, ridgeSupport268_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 525
    ridgeSupport268_rest_003 ridgeSupport268_rest_004 ridgeSupport268_rest_021
    ridgeSupport268_003 ridgeSupport268_suffix_004 ridgeSupport268_003_decode ridgeSupport268_suffix_decode_004
theorem ridgeSupport268_suffix_decode_002 : PackedRawNatGrowth.readList 14 589 ridgeSupport268_rest_002 =
    (ridgeSupport268_suffix_002, ridgeSupport268_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 557
    ridgeSupport268_rest_002 ridgeSupport268_rest_003 ridgeSupport268_rest_021
    ridgeSupport268_002 ridgeSupport268_suffix_003 ridgeSupport268_002_decode ridgeSupport268_suffix_decode_003
theorem ridgeSupport268_suffix_decode_001 : PackedRawNatGrowth.readList 14 621 ridgeSupport268_rest_001 =
    (ridgeSupport268_suffix_001, ridgeSupport268_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 589
    ridgeSupport268_rest_001 ridgeSupport268_rest_002 ridgeSupport268_rest_021
    ridgeSupport268_001 ridgeSupport268_suffix_002 ridgeSupport268_001_decode ridgeSupport268_suffix_decode_002
theorem ridgeSupport268_suffix_decode_000 : PackedRawNatGrowth.readList 14 653 ridgeSupport268_rest_000 =
    (ridgeSupport268_suffix_000, ridgeSupport268_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 621
    ridgeSupport268_rest_000 ridgeSupport268_rest_001 ridgeSupport268_rest_021
    ridgeSupport268_000 ridgeSupport268_suffix_001 ridgeSupport268_000_decode ridgeSupport268_suffix_decode_001
theorem ridgeSupport268_eq : candidateRows 268 = ridgeSupport268_suffix_000 := by
  rw [ridgeSupport268_source]
  exact congrArg Prod.fst ridgeSupport268_suffix_decode_000
theorem ridgeTest_large_268 : ridgeTest 268 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport268_eq]
    simp only [ridgeSupport268_suffix_000, ridgeSupport268_suffix_001, ridgeSupport268_suffix_002, ridgeSupport268_suffix_003, ridgeSupport268_suffix_004, ridgeSupport268_suffix_005, ridgeSupport268_suffix_006, ridgeSupport268_suffix_007, ridgeSupport268_suffix_008, ridgeSupport268_suffix_009, ridgeSupport268_suffix_010, ridgeSupport268_suffix_011, ridgeSupport268_suffix_012, ridgeSupport268_suffix_013, ridgeSupport268_suffix_014, ridgeSupport268_suffix_015, ridgeSupport268_suffix_016, ridgeSupport268_suffix_017, ridgeSupport268_suffix_018, ridgeSupport268_suffix_019, ridgeSupport268_suffix_020, ridgeSupport268_suffix_021, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport268_000_mask, ridgeSupport268_001_mask, ridgeSupport268_002_mask, ridgeSupport268_003_mask, ridgeSupport268_004_mask, ridgeSupport268_005_mask, ridgeSupport268_006_mask, ridgeSupport268_007_mask, ridgeSupport268_008_mask, ridgeSupport268_009_mask, ridgeSupport268_010_mask, ridgeSupport268_011_mask, ridgeSupport268_012_mask, ridgeSupport268_013_mask, ridgeSupport268_014_mask, ridgeSupport268_015_mask, ridgeSupport268_016_mask, ridgeSupport268_017_mask, ridgeSupport268_018_mask, ridgeSupport268_019_mask, ridgeSupport268_020_mask]
    decide +kernel
  · rw [ridgeSupport268_eq]
    simp only [ridgeSupport268_suffix_000, ridgeSupport268_suffix_001, ridgeSupport268_suffix_002, ridgeSupport268_suffix_003, ridgeSupport268_suffix_004, ridgeSupport268_suffix_005, ridgeSupport268_suffix_006, ridgeSupport268_suffix_007, ridgeSupport268_suffix_008, ridgeSupport268_suffix_009, ridgeSupport268_suffix_010, ridgeSupport268_suffix_011, ridgeSupport268_suffix_012, ridgeSupport268_suffix_013, ridgeSupport268_suffix_014, ridgeSupport268_suffix_015, ridgeSupport268_suffix_016, ridgeSupport268_suffix_017, ridgeSupport268_suffix_018, ridgeSupport268_suffix_019, ridgeSupport268_suffix_020, ridgeSupport268_suffix_021, List.all_append, List.all_nil, ridgeSupport268_000_checked, ridgeSupport268_001_checked, ridgeSupport268_002_checked, ridgeSupport268_003_checked, ridgeSupport268_004_checked, ridgeSupport268_005_checked, ridgeSupport268_006_checked, ridgeSupport268_007_checked, ridgeSupport268_008_checked, ridgeSupport268_009_checked, ridgeSupport268_010_checked, ridgeSupport268_011_checked, ridgeSupport268_012_checked, ridgeSupport268_013_checked, ridgeSupport268_014_checked, ridgeSupport268_015_checked, ridgeSupport268_016_checked, ridgeSupport268_017_checked, ridgeSupport268_018_checked, ridgeSupport268_019_checked, ridgeSupport268_020_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase01
