module
prelude
public import RootedSixBase01GrowthCacheRidgeSupport133Part000
public import RootedSixBase01GrowthCacheRidgeSupport133Part001
public import RootedSixBase01GrowthCacheRidgeSupport133Part002
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport133_suffix_decode_021 : PackedRawNatGrowth.readList 14 0 ridgeSupport133_rest_021 =
    (ridgeSupport133_suffix_021, ridgeSupport133_rest_021) := by rfl
theorem ridgeSupport133_suffix_decode_020 : PackedRawNatGrowth.readList 14 13 ridgeSupport133_rest_020 =
    (ridgeSupport133_suffix_020, ridgeSupport133_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 13 0
    ridgeSupport133_rest_020 ridgeSupport133_rest_021 ridgeSupport133_rest_021
    ridgeSupport133_020 ridgeSupport133_suffix_021 ridgeSupport133_020_decode ridgeSupport133_suffix_decode_021
theorem ridgeSupport133_suffix_decode_019 : PackedRawNatGrowth.readList 14 45 ridgeSupport133_rest_019 =
    (ridgeSupport133_suffix_019, ridgeSupport133_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 13
    ridgeSupport133_rest_019 ridgeSupport133_rest_020 ridgeSupport133_rest_021
    ridgeSupport133_019 ridgeSupport133_suffix_020 ridgeSupport133_019_decode ridgeSupport133_suffix_decode_020
theorem ridgeSupport133_suffix_decode_018 : PackedRawNatGrowth.readList 14 77 ridgeSupport133_rest_018 =
    (ridgeSupport133_suffix_018, ridgeSupport133_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 45
    ridgeSupport133_rest_018 ridgeSupport133_rest_019 ridgeSupport133_rest_021
    ridgeSupport133_018 ridgeSupport133_suffix_019 ridgeSupport133_018_decode ridgeSupport133_suffix_decode_019
theorem ridgeSupport133_suffix_decode_017 : PackedRawNatGrowth.readList 14 109 ridgeSupport133_rest_017 =
    (ridgeSupport133_suffix_017, ridgeSupport133_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 77
    ridgeSupport133_rest_017 ridgeSupport133_rest_018 ridgeSupport133_rest_021
    ridgeSupport133_017 ridgeSupport133_suffix_018 ridgeSupport133_017_decode ridgeSupport133_suffix_decode_018
theorem ridgeSupport133_suffix_decode_016 : PackedRawNatGrowth.readList 14 141 ridgeSupport133_rest_016 =
    (ridgeSupport133_suffix_016, ridgeSupport133_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 109
    ridgeSupport133_rest_016 ridgeSupport133_rest_017 ridgeSupport133_rest_021
    ridgeSupport133_016 ridgeSupport133_suffix_017 ridgeSupport133_016_decode ridgeSupport133_suffix_decode_017
theorem ridgeSupport133_suffix_decode_015 : PackedRawNatGrowth.readList 14 173 ridgeSupport133_rest_015 =
    (ridgeSupport133_suffix_015, ridgeSupport133_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 141
    ridgeSupport133_rest_015 ridgeSupport133_rest_016 ridgeSupport133_rest_021
    ridgeSupport133_015 ridgeSupport133_suffix_016 ridgeSupport133_015_decode ridgeSupport133_suffix_decode_016
theorem ridgeSupport133_suffix_decode_014 : PackedRawNatGrowth.readList 14 205 ridgeSupport133_rest_014 =
    (ridgeSupport133_suffix_014, ridgeSupport133_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 173
    ridgeSupport133_rest_014 ridgeSupport133_rest_015 ridgeSupport133_rest_021
    ridgeSupport133_014 ridgeSupport133_suffix_015 ridgeSupport133_014_decode ridgeSupport133_suffix_decode_015
theorem ridgeSupport133_suffix_decode_013 : PackedRawNatGrowth.readList 14 237 ridgeSupport133_rest_013 =
    (ridgeSupport133_suffix_013, ridgeSupport133_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 205
    ridgeSupport133_rest_013 ridgeSupport133_rest_014 ridgeSupport133_rest_021
    ridgeSupport133_013 ridgeSupport133_suffix_014 ridgeSupport133_013_decode ridgeSupport133_suffix_decode_014
theorem ridgeSupport133_suffix_decode_012 : PackedRawNatGrowth.readList 14 269 ridgeSupport133_rest_012 =
    (ridgeSupport133_suffix_012, ridgeSupport133_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 237
    ridgeSupport133_rest_012 ridgeSupport133_rest_013 ridgeSupport133_rest_021
    ridgeSupport133_012 ridgeSupport133_suffix_013 ridgeSupport133_012_decode ridgeSupport133_suffix_decode_013
theorem ridgeSupport133_suffix_decode_011 : PackedRawNatGrowth.readList 14 301 ridgeSupport133_rest_011 =
    (ridgeSupport133_suffix_011, ridgeSupport133_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 269
    ridgeSupport133_rest_011 ridgeSupport133_rest_012 ridgeSupport133_rest_021
    ridgeSupport133_011 ridgeSupport133_suffix_012 ridgeSupport133_011_decode ridgeSupport133_suffix_decode_012
theorem ridgeSupport133_suffix_decode_010 : PackedRawNatGrowth.readList 14 333 ridgeSupport133_rest_010 =
    (ridgeSupport133_suffix_010, ridgeSupport133_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 301
    ridgeSupport133_rest_010 ridgeSupport133_rest_011 ridgeSupport133_rest_021
    ridgeSupport133_010 ridgeSupport133_suffix_011 ridgeSupport133_010_decode ridgeSupport133_suffix_decode_011
theorem ridgeSupport133_suffix_decode_009 : PackedRawNatGrowth.readList 14 365 ridgeSupport133_rest_009 =
    (ridgeSupport133_suffix_009, ridgeSupport133_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 333
    ridgeSupport133_rest_009 ridgeSupport133_rest_010 ridgeSupport133_rest_021
    ridgeSupport133_009 ridgeSupport133_suffix_010 ridgeSupport133_009_decode ridgeSupport133_suffix_decode_010
theorem ridgeSupport133_suffix_decode_008 : PackedRawNatGrowth.readList 14 397 ridgeSupport133_rest_008 =
    (ridgeSupport133_suffix_008, ridgeSupport133_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 365
    ridgeSupport133_rest_008 ridgeSupport133_rest_009 ridgeSupport133_rest_021
    ridgeSupport133_008 ridgeSupport133_suffix_009 ridgeSupport133_008_decode ridgeSupport133_suffix_decode_009
theorem ridgeSupport133_suffix_decode_007 : PackedRawNatGrowth.readList 14 429 ridgeSupport133_rest_007 =
    (ridgeSupport133_suffix_007, ridgeSupport133_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 397
    ridgeSupport133_rest_007 ridgeSupport133_rest_008 ridgeSupport133_rest_021
    ridgeSupport133_007 ridgeSupport133_suffix_008 ridgeSupport133_007_decode ridgeSupport133_suffix_decode_008
theorem ridgeSupport133_suffix_decode_006 : PackedRawNatGrowth.readList 14 461 ridgeSupport133_rest_006 =
    (ridgeSupport133_suffix_006, ridgeSupport133_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 429
    ridgeSupport133_rest_006 ridgeSupport133_rest_007 ridgeSupport133_rest_021
    ridgeSupport133_006 ridgeSupport133_suffix_007 ridgeSupport133_006_decode ridgeSupport133_suffix_decode_007
theorem ridgeSupport133_suffix_decode_005 : PackedRawNatGrowth.readList 14 493 ridgeSupport133_rest_005 =
    (ridgeSupport133_suffix_005, ridgeSupport133_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 461
    ridgeSupport133_rest_005 ridgeSupport133_rest_006 ridgeSupport133_rest_021
    ridgeSupport133_005 ridgeSupport133_suffix_006 ridgeSupport133_005_decode ridgeSupport133_suffix_decode_006
theorem ridgeSupport133_suffix_decode_004 : PackedRawNatGrowth.readList 14 525 ridgeSupport133_rest_004 =
    (ridgeSupport133_suffix_004, ridgeSupport133_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 493
    ridgeSupport133_rest_004 ridgeSupport133_rest_005 ridgeSupport133_rest_021
    ridgeSupport133_004 ridgeSupport133_suffix_005 ridgeSupport133_004_decode ridgeSupport133_suffix_decode_005
theorem ridgeSupport133_suffix_decode_003 : PackedRawNatGrowth.readList 14 557 ridgeSupport133_rest_003 =
    (ridgeSupport133_suffix_003, ridgeSupport133_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 525
    ridgeSupport133_rest_003 ridgeSupport133_rest_004 ridgeSupport133_rest_021
    ridgeSupport133_003 ridgeSupport133_suffix_004 ridgeSupport133_003_decode ridgeSupport133_suffix_decode_004
theorem ridgeSupport133_suffix_decode_002 : PackedRawNatGrowth.readList 14 589 ridgeSupport133_rest_002 =
    (ridgeSupport133_suffix_002, ridgeSupport133_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 557
    ridgeSupport133_rest_002 ridgeSupport133_rest_003 ridgeSupport133_rest_021
    ridgeSupport133_002 ridgeSupport133_suffix_003 ridgeSupport133_002_decode ridgeSupport133_suffix_decode_003
theorem ridgeSupport133_suffix_decode_001 : PackedRawNatGrowth.readList 14 621 ridgeSupport133_rest_001 =
    (ridgeSupport133_suffix_001, ridgeSupport133_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 589
    ridgeSupport133_rest_001 ridgeSupport133_rest_002 ridgeSupport133_rest_021
    ridgeSupport133_001 ridgeSupport133_suffix_002 ridgeSupport133_001_decode ridgeSupport133_suffix_decode_002
theorem ridgeSupport133_suffix_decode_000 : PackedRawNatGrowth.readList 14 653 ridgeSupport133_rest_000 =
    (ridgeSupport133_suffix_000, ridgeSupport133_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 621
    ridgeSupport133_rest_000 ridgeSupport133_rest_001 ridgeSupport133_rest_021
    ridgeSupport133_000 ridgeSupport133_suffix_001 ridgeSupport133_000_decode ridgeSupport133_suffix_decode_001
theorem ridgeSupport133_eq : candidateRows 133 = ridgeSupport133_suffix_000 := by
  rw [ridgeSupport133_source]
  exact congrArg Prod.fst ridgeSupport133_suffix_decode_000
theorem ridgeTest_large_133 : ridgeTest 133 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport133_eq]
    simp only [ridgeSupport133_suffix_000, ridgeSupport133_suffix_001, ridgeSupport133_suffix_002, ridgeSupport133_suffix_003, ridgeSupport133_suffix_004, ridgeSupport133_suffix_005, ridgeSupport133_suffix_006, ridgeSupport133_suffix_007, ridgeSupport133_suffix_008, ridgeSupport133_suffix_009, ridgeSupport133_suffix_010, ridgeSupport133_suffix_011, ridgeSupport133_suffix_012, ridgeSupport133_suffix_013, ridgeSupport133_suffix_014, ridgeSupport133_suffix_015, ridgeSupport133_suffix_016, ridgeSupport133_suffix_017, ridgeSupport133_suffix_018, ridgeSupport133_suffix_019, ridgeSupport133_suffix_020, ridgeSupport133_suffix_021, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport133_000_mask, ridgeSupport133_001_mask, ridgeSupport133_002_mask, ridgeSupport133_003_mask, ridgeSupport133_004_mask, ridgeSupport133_005_mask, ridgeSupport133_006_mask, ridgeSupport133_007_mask, ridgeSupport133_008_mask, ridgeSupport133_009_mask, ridgeSupport133_010_mask, ridgeSupport133_011_mask, ridgeSupport133_012_mask, ridgeSupport133_013_mask, ridgeSupport133_014_mask, ridgeSupport133_015_mask, ridgeSupport133_016_mask, ridgeSupport133_017_mask, ridgeSupport133_018_mask, ridgeSupport133_019_mask, ridgeSupport133_020_mask]
    decide +kernel
  · rw [ridgeSupport133_eq]
    simp only [ridgeSupport133_suffix_000, ridgeSupport133_suffix_001, ridgeSupport133_suffix_002, ridgeSupport133_suffix_003, ridgeSupport133_suffix_004, ridgeSupport133_suffix_005, ridgeSupport133_suffix_006, ridgeSupport133_suffix_007, ridgeSupport133_suffix_008, ridgeSupport133_suffix_009, ridgeSupport133_suffix_010, ridgeSupport133_suffix_011, ridgeSupport133_suffix_012, ridgeSupport133_suffix_013, ridgeSupport133_suffix_014, ridgeSupport133_suffix_015, ridgeSupport133_suffix_016, ridgeSupport133_suffix_017, ridgeSupport133_suffix_018, ridgeSupport133_suffix_019, ridgeSupport133_suffix_020, ridgeSupport133_suffix_021, List.all_append, List.all_nil, ridgeSupport133_000_checked, ridgeSupport133_001_checked, ridgeSupport133_002_checked, ridgeSupport133_003_checked, ridgeSupport133_004_checked, ridgeSupport133_005_checked, ridgeSupport133_006_checked, ridgeSupport133_007_checked, ridgeSupport133_008_checked, ridgeSupport133_009_checked, ridgeSupport133_010_checked, ridgeSupport133_011_checked, ridgeSupport133_012_checked, ridgeSupport133_013_checked, ridgeSupport133_014_checked, ridgeSupport133_015_checked, ridgeSupport133_016_checked, ridgeSupport133_017_checked, ridgeSupport133_018_checked, ridgeSupport133_019_checked, ridgeSupport133_020_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase01
