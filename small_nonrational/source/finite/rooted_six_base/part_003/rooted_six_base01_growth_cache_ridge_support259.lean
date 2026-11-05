module
prelude
public import RootedSixBase01GrowthCacheRidgeSupport259Part000
public import RootedSixBase01GrowthCacheRidgeSupport259Part001
public import RootedSixBase01GrowthCacheRidgeSupport259Part002
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport259_suffix_decode_021 : PackedRawNatGrowth.readList 14 0 ridgeSupport259_rest_021 =
    (ridgeSupport259_suffix_021, ridgeSupport259_rest_021) := by rfl
theorem ridgeSupport259_suffix_decode_020 : PackedRawNatGrowth.readList 14 13 ridgeSupport259_rest_020 =
    (ridgeSupport259_suffix_020, ridgeSupport259_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 13 0
    ridgeSupport259_rest_020 ridgeSupport259_rest_021 ridgeSupport259_rest_021
    ridgeSupport259_020 ridgeSupport259_suffix_021 ridgeSupport259_020_decode ridgeSupport259_suffix_decode_021
theorem ridgeSupport259_suffix_decode_019 : PackedRawNatGrowth.readList 14 45 ridgeSupport259_rest_019 =
    (ridgeSupport259_suffix_019, ridgeSupport259_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 13
    ridgeSupport259_rest_019 ridgeSupport259_rest_020 ridgeSupport259_rest_021
    ridgeSupport259_019 ridgeSupport259_suffix_020 ridgeSupport259_019_decode ridgeSupport259_suffix_decode_020
theorem ridgeSupport259_suffix_decode_018 : PackedRawNatGrowth.readList 14 77 ridgeSupport259_rest_018 =
    (ridgeSupport259_suffix_018, ridgeSupport259_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 45
    ridgeSupport259_rest_018 ridgeSupport259_rest_019 ridgeSupport259_rest_021
    ridgeSupport259_018 ridgeSupport259_suffix_019 ridgeSupport259_018_decode ridgeSupport259_suffix_decode_019
theorem ridgeSupport259_suffix_decode_017 : PackedRawNatGrowth.readList 14 109 ridgeSupport259_rest_017 =
    (ridgeSupport259_suffix_017, ridgeSupport259_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 77
    ridgeSupport259_rest_017 ridgeSupport259_rest_018 ridgeSupport259_rest_021
    ridgeSupport259_017 ridgeSupport259_suffix_018 ridgeSupport259_017_decode ridgeSupport259_suffix_decode_018
theorem ridgeSupport259_suffix_decode_016 : PackedRawNatGrowth.readList 14 141 ridgeSupport259_rest_016 =
    (ridgeSupport259_suffix_016, ridgeSupport259_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 109
    ridgeSupport259_rest_016 ridgeSupport259_rest_017 ridgeSupport259_rest_021
    ridgeSupport259_016 ridgeSupport259_suffix_017 ridgeSupport259_016_decode ridgeSupport259_suffix_decode_017
theorem ridgeSupport259_suffix_decode_015 : PackedRawNatGrowth.readList 14 173 ridgeSupport259_rest_015 =
    (ridgeSupport259_suffix_015, ridgeSupport259_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 141
    ridgeSupport259_rest_015 ridgeSupport259_rest_016 ridgeSupport259_rest_021
    ridgeSupport259_015 ridgeSupport259_suffix_016 ridgeSupport259_015_decode ridgeSupport259_suffix_decode_016
theorem ridgeSupport259_suffix_decode_014 : PackedRawNatGrowth.readList 14 205 ridgeSupport259_rest_014 =
    (ridgeSupport259_suffix_014, ridgeSupport259_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 173
    ridgeSupport259_rest_014 ridgeSupport259_rest_015 ridgeSupport259_rest_021
    ridgeSupport259_014 ridgeSupport259_suffix_015 ridgeSupport259_014_decode ridgeSupport259_suffix_decode_015
theorem ridgeSupport259_suffix_decode_013 : PackedRawNatGrowth.readList 14 237 ridgeSupport259_rest_013 =
    (ridgeSupport259_suffix_013, ridgeSupport259_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 205
    ridgeSupport259_rest_013 ridgeSupport259_rest_014 ridgeSupport259_rest_021
    ridgeSupport259_013 ridgeSupport259_suffix_014 ridgeSupport259_013_decode ridgeSupport259_suffix_decode_014
theorem ridgeSupport259_suffix_decode_012 : PackedRawNatGrowth.readList 14 269 ridgeSupport259_rest_012 =
    (ridgeSupport259_suffix_012, ridgeSupport259_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 237
    ridgeSupport259_rest_012 ridgeSupport259_rest_013 ridgeSupport259_rest_021
    ridgeSupport259_012 ridgeSupport259_suffix_013 ridgeSupport259_012_decode ridgeSupport259_suffix_decode_013
theorem ridgeSupport259_suffix_decode_011 : PackedRawNatGrowth.readList 14 301 ridgeSupport259_rest_011 =
    (ridgeSupport259_suffix_011, ridgeSupport259_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 269
    ridgeSupport259_rest_011 ridgeSupport259_rest_012 ridgeSupport259_rest_021
    ridgeSupport259_011 ridgeSupport259_suffix_012 ridgeSupport259_011_decode ridgeSupport259_suffix_decode_012
theorem ridgeSupport259_suffix_decode_010 : PackedRawNatGrowth.readList 14 333 ridgeSupport259_rest_010 =
    (ridgeSupport259_suffix_010, ridgeSupport259_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 301
    ridgeSupport259_rest_010 ridgeSupport259_rest_011 ridgeSupport259_rest_021
    ridgeSupport259_010 ridgeSupport259_suffix_011 ridgeSupport259_010_decode ridgeSupport259_suffix_decode_011
theorem ridgeSupport259_suffix_decode_009 : PackedRawNatGrowth.readList 14 365 ridgeSupport259_rest_009 =
    (ridgeSupport259_suffix_009, ridgeSupport259_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 333
    ridgeSupport259_rest_009 ridgeSupport259_rest_010 ridgeSupport259_rest_021
    ridgeSupport259_009 ridgeSupport259_suffix_010 ridgeSupport259_009_decode ridgeSupport259_suffix_decode_010
theorem ridgeSupport259_suffix_decode_008 : PackedRawNatGrowth.readList 14 397 ridgeSupport259_rest_008 =
    (ridgeSupport259_suffix_008, ridgeSupport259_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 365
    ridgeSupport259_rest_008 ridgeSupport259_rest_009 ridgeSupport259_rest_021
    ridgeSupport259_008 ridgeSupport259_suffix_009 ridgeSupport259_008_decode ridgeSupport259_suffix_decode_009
theorem ridgeSupport259_suffix_decode_007 : PackedRawNatGrowth.readList 14 429 ridgeSupport259_rest_007 =
    (ridgeSupport259_suffix_007, ridgeSupport259_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 397
    ridgeSupport259_rest_007 ridgeSupport259_rest_008 ridgeSupport259_rest_021
    ridgeSupport259_007 ridgeSupport259_suffix_008 ridgeSupport259_007_decode ridgeSupport259_suffix_decode_008
theorem ridgeSupport259_suffix_decode_006 : PackedRawNatGrowth.readList 14 461 ridgeSupport259_rest_006 =
    (ridgeSupport259_suffix_006, ridgeSupport259_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 429
    ridgeSupport259_rest_006 ridgeSupport259_rest_007 ridgeSupport259_rest_021
    ridgeSupport259_006 ridgeSupport259_suffix_007 ridgeSupport259_006_decode ridgeSupport259_suffix_decode_007
theorem ridgeSupport259_suffix_decode_005 : PackedRawNatGrowth.readList 14 493 ridgeSupport259_rest_005 =
    (ridgeSupport259_suffix_005, ridgeSupport259_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 461
    ridgeSupport259_rest_005 ridgeSupport259_rest_006 ridgeSupport259_rest_021
    ridgeSupport259_005 ridgeSupport259_suffix_006 ridgeSupport259_005_decode ridgeSupport259_suffix_decode_006
theorem ridgeSupport259_suffix_decode_004 : PackedRawNatGrowth.readList 14 525 ridgeSupport259_rest_004 =
    (ridgeSupport259_suffix_004, ridgeSupport259_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 493
    ridgeSupport259_rest_004 ridgeSupport259_rest_005 ridgeSupport259_rest_021
    ridgeSupport259_004 ridgeSupport259_suffix_005 ridgeSupport259_004_decode ridgeSupport259_suffix_decode_005
theorem ridgeSupport259_suffix_decode_003 : PackedRawNatGrowth.readList 14 557 ridgeSupport259_rest_003 =
    (ridgeSupport259_suffix_003, ridgeSupport259_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 525
    ridgeSupport259_rest_003 ridgeSupport259_rest_004 ridgeSupport259_rest_021
    ridgeSupport259_003 ridgeSupport259_suffix_004 ridgeSupport259_003_decode ridgeSupport259_suffix_decode_004
theorem ridgeSupport259_suffix_decode_002 : PackedRawNatGrowth.readList 14 589 ridgeSupport259_rest_002 =
    (ridgeSupport259_suffix_002, ridgeSupport259_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 557
    ridgeSupport259_rest_002 ridgeSupport259_rest_003 ridgeSupport259_rest_021
    ridgeSupport259_002 ridgeSupport259_suffix_003 ridgeSupport259_002_decode ridgeSupport259_suffix_decode_003
theorem ridgeSupport259_suffix_decode_001 : PackedRawNatGrowth.readList 14 621 ridgeSupport259_rest_001 =
    (ridgeSupport259_suffix_001, ridgeSupport259_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 589
    ridgeSupport259_rest_001 ridgeSupport259_rest_002 ridgeSupport259_rest_021
    ridgeSupport259_001 ridgeSupport259_suffix_002 ridgeSupport259_001_decode ridgeSupport259_suffix_decode_002
theorem ridgeSupport259_suffix_decode_000 : PackedRawNatGrowth.readList 14 653 ridgeSupport259_rest_000 =
    (ridgeSupport259_suffix_000, ridgeSupport259_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 621
    ridgeSupport259_rest_000 ridgeSupport259_rest_001 ridgeSupport259_rest_021
    ridgeSupport259_000 ridgeSupport259_suffix_001 ridgeSupport259_000_decode ridgeSupport259_suffix_decode_001
theorem ridgeSupport259_eq : candidateRows 259 = ridgeSupport259_suffix_000 := by
  rw [ridgeSupport259_source]
  exact congrArg Prod.fst ridgeSupport259_suffix_decode_000
theorem ridgeTest_large_259 : ridgeTest 259 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport259_eq]
    simp only [ridgeSupport259_suffix_000, ridgeSupport259_suffix_001, ridgeSupport259_suffix_002, ridgeSupport259_suffix_003, ridgeSupport259_suffix_004, ridgeSupport259_suffix_005, ridgeSupport259_suffix_006, ridgeSupport259_suffix_007, ridgeSupport259_suffix_008, ridgeSupport259_suffix_009, ridgeSupport259_suffix_010, ridgeSupport259_suffix_011, ridgeSupport259_suffix_012, ridgeSupport259_suffix_013, ridgeSupport259_suffix_014, ridgeSupport259_suffix_015, ridgeSupport259_suffix_016, ridgeSupport259_suffix_017, ridgeSupport259_suffix_018, ridgeSupport259_suffix_019, ridgeSupport259_suffix_020, ridgeSupport259_suffix_021, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport259_000_mask, ridgeSupport259_001_mask, ridgeSupport259_002_mask, ridgeSupport259_003_mask, ridgeSupport259_004_mask, ridgeSupport259_005_mask, ridgeSupport259_006_mask, ridgeSupport259_007_mask, ridgeSupport259_008_mask, ridgeSupport259_009_mask, ridgeSupport259_010_mask, ridgeSupport259_011_mask, ridgeSupport259_012_mask, ridgeSupport259_013_mask, ridgeSupport259_014_mask, ridgeSupport259_015_mask, ridgeSupport259_016_mask, ridgeSupport259_017_mask, ridgeSupport259_018_mask, ridgeSupport259_019_mask, ridgeSupport259_020_mask]
    decide +kernel
  · rw [ridgeSupport259_eq]
    simp only [ridgeSupport259_suffix_000, ridgeSupport259_suffix_001, ridgeSupport259_suffix_002, ridgeSupport259_suffix_003, ridgeSupport259_suffix_004, ridgeSupport259_suffix_005, ridgeSupport259_suffix_006, ridgeSupport259_suffix_007, ridgeSupport259_suffix_008, ridgeSupport259_suffix_009, ridgeSupport259_suffix_010, ridgeSupport259_suffix_011, ridgeSupport259_suffix_012, ridgeSupport259_suffix_013, ridgeSupport259_suffix_014, ridgeSupport259_suffix_015, ridgeSupport259_suffix_016, ridgeSupport259_suffix_017, ridgeSupport259_suffix_018, ridgeSupport259_suffix_019, ridgeSupport259_suffix_020, ridgeSupport259_suffix_021, List.all_append, List.all_nil, ridgeSupport259_000_checked, ridgeSupport259_001_checked, ridgeSupport259_002_checked, ridgeSupport259_003_checked, ridgeSupport259_004_checked, ridgeSupport259_005_checked, ridgeSupport259_006_checked, ridgeSupport259_007_checked, ridgeSupport259_008_checked, ridgeSupport259_009_checked, ridgeSupport259_010_checked, ridgeSupport259_011_checked, ridgeSupport259_012_checked, ridgeSupport259_013_checked, ridgeSupport259_014_checked, ridgeSupport259_015_checked, ridgeSupport259_016_checked, ridgeSupport259_017_checked, ridgeSupport259_018_checked, ridgeSupport259_019_checked, ridgeSupport259_020_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase01
