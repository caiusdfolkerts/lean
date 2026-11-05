module
prelude
public import RootedSixBase01GrowthCacheRidgeSupport265Part000
public import RootedSixBase01GrowthCacheRidgeSupport265Part001
public import RootedSixBase01GrowthCacheRidgeSupport265Part002
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport265_suffix_decode_021 : PackedRawNatGrowth.readList 14 0 ridgeSupport265_rest_021 =
    (ridgeSupport265_suffix_021, ridgeSupport265_rest_021) := by rfl
theorem ridgeSupport265_suffix_decode_020 : PackedRawNatGrowth.readList 14 13 ridgeSupport265_rest_020 =
    (ridgeSupport265_suffix_020, ridgeSupport265_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 13 0
    ridgeSupport265_rest_020 ridgeSupport265_rest_021 ridgeSupport265_rest_021
    ridgeSupport265_020 ridgeSupport265_suffix_021 ridgeSupport265_020_decode ridgeSupport265_suffix_decode_021
theorem ridgeSupport265_suffix_decode_019 : PackedRawNatGrowth.readList 14 45 ridgeSupport265_rest_019 =
    (ridgeSupport265_suffix_019, ridgeSupport265_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 13
    ridgeSupport265_rest_019 ridgeSupport265_rest_020 ridgeSupport265_rest_021
    ridgeSupport265_019 ridgeSupport265_suffix_020 ridgeSupport265_019_decode ridgeSupport265_suffix_decode_020
theorem ridgeSupport265_suffix_decode_018 : PackedRawNatGrowth.readList 14 77 ridgeSupport265_rest_018 =
    (ridgeSupport265_suffix_018, ridgeSupport265_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 45
    ridgeSupport265_rest_018 ridgeSupport265_rest_019 ridgeSupport265_rest_021
    ridgeSupport265_018 ridgeSupport265_suffix_019 ridgeSupport265_018_decode ridgeSupport265_suffix_decode_019
theorem ridgeSupport265_suffix_decode_017 : PackedRawNatGrowth.readList 14 109 ridgeSupport265_rest_017 =
    (ridgeSupport265_suffix_017, ridgeSupport265_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 77
    ridgeSupport265_rest_017 ridgeSupport265_rest_018 ridgeSupport265_rest_021
    ridgeSupport265_017 ridgeSupport265_suffix_018 ridgeSupport265_017_decode ridgeSupport265_suffix_decode_018
theorem ridgeSupport265_suffix_decode_016 : PackedRawNatGrowth.readList 14 141 ridgeSupport265_rest_016 =
    (ridgeSupport265_suffix_016, ridgeSupport265_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 109
    ridgeSupport265_rest_016 ridgeSupport265_rest_017 ridgeSupport265_rest_021
    ridgeSupport265_016 ridgeSupport265_suffix_017 ridgeSupport265_016_decode ridgeSupport265_suffix_decode_017
theorem ridgeSupport265_suffix_decode_015 : PackedRawNatGrowth.readList 14 173 ridgeSupport265_rest_015 =
    (ridgeSupport265_suffix_015, ridgeSupport265_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 141
    ridgeSupport265_rest_015 ridgeSupport265_rest_016 ridgeSupport265_rest_021
    ridgeSupport265_015 ridgeSupport265_suffix_016 ridgeSupport265_015_decode ridgeSupport265_suffix_decode_016
theorem ridgeSupport265_suffix_decode_014 : PackedRawNatGrowth.readList 14 205 ridgeSupport265_rest_014 =
    (ridgeSupport265_suffix_014, ridgeSupport265_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 173
    ridgeSupport265_rest_014 ridgeSupport265_rest_015 ridgeSupport265_rest_021
    ridgeSupport265_014 ridgeSupport265_suffix_015 ridgeSupport265_014_decode ridgeSupport265_suffix_decode_015
theorem ridgeSupport265_suffix_decode_013 : PackedRawNatGrowth.readList 14 237 ridgeSupport265_rest_013 =
    (ridgeSupport265_suffix_013, ridgeSupport265_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 205
    ridgeSupport265_rest_013 ridgeSupport265_rest_014 ridgeSupport265_rest_021
    ridgeSupport265_013 ridgeSupport265_suffix_014 ridgeSupport265_013_decode ridgeSupport265_suffix_decode_014
theorem ridgeSupport265_suffix_decode_012 : PackedRawNatGrowth.readList 14 269 ridgeSupport265_rest_012 =
    (ridgeSupport265_suffix_012, ridgeSupport265_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 237
    ridgeSupport265_rest_012 ridgeSupport265_rest_013 ridgeSupport265_rest_021
    ridgeSupport265_012 ridgeSupport265_suffix_013 ridgeSupport265_012_decode ridgeSupport265_suffix_decode_013
theorem ridgeSupport265_suffix_decode_011 : PackedRawNatGrowth.readList 14 301 ridgeSupport265_rest_011 =
    (ridgeSupport265_suffix_011, ridgeSupport265_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 269
    ridgeSupport265_rest_011 ridgeSupport265_rest_012 ridgeSupport265_rest_021
    ridgeSupport265_011 ridgeSupport265_suffix_012 ridgeSupport265_011_decode ridgeSupport265_suffix_decode_012
theorem ridgeSupport265_suffix_decode_010 : PackedRawNatGrowth.readList 14 333 ridgeSupport265_rest_010 =
    (ridgeSupport265_suffix_010, ridgeSupport265_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 301
    ridgeSupport265_rest_010 ridgeSupport265_rest_011 ridgeSupport265_rest_021
    ridgeSupport265_010 ridgeSupport265_suffix_011 ridgeSupport265_010_decode ridgeSupport265_suffix_decode_011
theorem ridgeSupport265_suffix_decode_009 : PackedRawNatGrowth.readList 14 365 ridgeSupport265_rest_009 =
    (ridgeSupport265_suffix_009, ridgeSupport265_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 333
    ridgeSupport265_rest_009 ridgeSupport265_rest_010 ridgeSupport265_rest_021
    ridgeSupport265_009 ridgeSupport265_suffix_010 ridgeSupport265_009_decode ridgeSupport265_suffix_decode_010
theorem ridgeSupport265_suffix_decode_008 : PackedRawNatGrowth.readList 14 397 ridgeSupport265_rest_008 =
    (ridgeSupport265_suffix_008, ridgeSupport265_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 365
    ridgeSupport265_rest_008 ridgeSupport265_rest_009 ridgeSupport265_rest_021
    ridgeSupport265_008 ridgeSupport265_suffix_009 ridgeSupport265_008_decode ridgeSupport265_suffix_decode_009
theorem ridgeSupport265_suffix_decode_007 : PackedRawNatGrowth.readList 14 429 ridgeSupport265_rest_007 =
    (ridgeSupport265_suffix_007, ridgeSupport265_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 397
    ridgeSupport265_rest_007 ridgeSupport265_rest_008 ridgeSupport265_rest_021
    ridgeSupport265_007 ridgeSupport265_suffix_008 ridgeSupport265_007_decode ridgeSupport265_suffix_decode_008
theorem ridgeSupport265_suffix_decode_006 : PackedRawNatGrowth.readList 14 461 ridgeSupport265_rest_006 =
    (ridgeSupport265_suffix_006, ridgeSupport265_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 429
    ridgeSupport265_rest_006 ridgeSupport265_rest_007 ridgeSupport265_rest_021
    ridgeSupport265_006 ridgeSupport265_suffix_007 ridgeSupport265_006_decode ridgeSupport265_suffix_decode_007
theorem ridgeSupport265_suffix_decode_005 : PackedRawNatGrowth.readList 14 493 ridgeSupport265_rest_005 =
    (ridgeSupport265_suffix_005, ridgeSupport265_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 461
    ridgeSupport265_rest_005 ridgeSupport265_rest_006 ridgeSupport265_rest_021
    ridgeSupport265_005 ridgeSupport265_suffix_006 ridgeSupport265_005_decode ridgeSupport265_suffix_decode_006
theorem ridgeSupport265_suffix_decode_004 : PackedRawNatGrowth.readList 14 525 ridgeSupport265_rest_004 =
    (ridgeSupport265_suffix_004, ridgeSupport265_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 493
    ridgeSupport265_rest_004 ridgeSupport265_rest_005 ridgeSupport265_rest_021
    ridgeSupport265_004 ridgeSupport265_suffix_005 ridgeSupport265_004_decode ridgeSupport265_suffix_decode_005
theorem ridgeSupport265_suffix_decode_003 : PackedRawNatGrowth.readList 14 557 ridgeSupport265_rest_003 =
    (ridgeSupport265_suffix_003, ridgeSupport265_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 525
    ridgeSupport265_rest_003 ridgeSupport265_rest_004 ridgeSupport265_rest_021
    ridgeSupport265_003 ridgeSupport265_suffix_004 ridgeSupport265_003_decode ridgeSupport265_suffix_decode_004
theorem ridgeSupport265_suffix_decode_002 : PackedRawNatGrowth.readList 14 589 ridgeSupport265_rest_002 =
    (ridgeSupport265_suffix_002, ridgeSupport265_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 557
    ridgeSupport265_rest_002 ridgeSupport265_rest_003 ridgeSupport265_rest_021
    ridgeSupport265_002 ridgeSupport265_suffix_003 ridgeSupport265_002_decode ridgeSupport265_suffix_decode_003
theorem ridgeSupport265_suffix_decode_001 : PackedRawNatGrowth.readList 14 621 ridgeSupport265_rest_001 =
    (ridgeSupport265_suffix_001, ridgeSupport265_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 589
    ridgeSupport265_rest_001 ridgeSupport265_rest_002 ridgeSupport265_rest_021
    ridgeSupport265_001 ridgeSupport265_suffix_002 ridgeSupport265_001_decode ridgeSupport265_suffix_decode_002
theorem ridgeSupport265_suffix_decode_000 : PackedRawNatGrowth.readList 14 653 ridgeSupport265_rest_000 =
    (ridgeSupport265_suffix_000, ridgeSupport265_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 621
    ridgeSupport265_rest_000 ridgeSupport265_rest_001 ridgeSupport265_rest_021
    ridgeSupport265_000 ridgeSupport265_suffix_001 ridgeSupport265_000_decode ridgeSupport265_suffix_decode_001
theorem ridgeSupport265_eq : candidateRows 265 = ridgeSupport265_suffix_000 := by
  rw [ridgeSupport265_source]
  exact congrArg Prod.fst ridgeSupport265_suffix_decode_000
theorem ridgeTest_large_265 : ridgeTest 265 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport265_eq]
    simp only [ridgeSupport265_suffix_000, ridgeSupport265_suffix_001, ridgeSupport265_suffix_002, ridgeSupport265_suffix_003, ridgeSupport265_suffix_004, ridgeSupport265_suffix_005, ridgeSupport265_suffix_006, ridgeSupport265_suffix_007, ridgeSupport265_suffix_008, ridgeSupport265_suffix_009, ridgeSupport265_suffix_010, ridgeSupport265_suffix_011, ridgeSupport265_suffix_012, ridgeSupport265_suffix_013, ridgeSupport265_suffix_014, ridgeSupport265_suffix_015, ridgeSupport265_suffix_016, ridgeSupport265_suffix_017, ridgeSupport265_suffix_018, ridgeSupport265_suffix_019, ridgeSupport265_suffix_020, ridgeSupport265_suffix_021, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport265_000_mask, ridgeSupport265_001_mask, ridgeSupport265_002_mask, ridgeSupport265_003_mask, ridgeSupport265_004_mask, ridgeSupport265_005_mask, ridgeSupport265_006_mask, ridgeSupport265_007_mask, ridgeSupport265_008_mask, ridgeSupport265_009_mask, ridgeSupport265_010_mask, ridgeSupport265_011_mask, ridgeSupport265_012_mask, ridgeSupport265_013_mask, ridgeSupport265_014_mask, ridgeSupport265_015_mask, ridgeSupport265_016_mask, ridgeSupport265_017_mask, ridgeSupport265_018_mask, ridgeSupport265_019_mask, ridgeSupport265_020_mask]
    decide +kernel
  · rw [ridgeSupport265_eq]
    simp only [ridgeSupport265_suffix_000, ridgeSupport265_suffix_001, ridgeSupport265_suffix_002, ridgeSupport265_suffix_003, ridgeSupport265_suffix_004, ridgeSupport265_suffix_005, ridgeSupport265_suffix_006, ridgeSupport265_suffix_007, ridgeSupport265_suffix_008, ridgeSupport265_suffix_009, ridgeSupport265_suffix_010, ridgeSupport265_suffix_011, ridgeSupport265_suffix_012, ridgeSupport265_suffix_013, ridgeSupport265_suffix_014, ridgeSupport265_suffix_015, ridgeSupport265_suffix_016, ridgeSupport265_suffix_017, ridgeSupport265_suffix_018, ridgeSupport265_suffix_019, ridgeSupport265_suffix_020, ridgeSupport265_suffix_021, List.all_append, List.all_nil, ridgeSupport265_000_checked, ridgeSupport265_001_checked, ridgeSupport265_002_checked, ridgeSupport265_003_checked, ridgeSupport265_004_checked, ridgeSupport265_005_checked, ridgeSupport265_006_checked, ridgeSupport265_007_checked, ridgeSupport265_008_checked, ridgeSupport265_009_checked, ridgeSupport265_010_checked, ridgeSupport265_011_checked, ridgeSupport265_012_checked, ridgeSupport265_013_checked, ridgeSupport265_014_checked, ridgeSupport265_015_checked, ridgeSupport265_016_checked, ridgeSupport265_017_checked, ridgeSupport265_018_checked, ridgeSupport265_019_checked, ridgeSupport265_020_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase01
