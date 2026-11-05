module
prelude
public import RootedSixBase02GrowthCacheRidgeSupport42Part000
public import RootedSixBase02GrowthCacheRidgeSupport42Part001
public import RootedSixBase02GrowthCacheRidgeSupport42Part002
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase02
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport42_suffix_decode_020 : PackedRawNatGrowth.readList 13 0 ridgeSupport42_rest_020 =
    (ridgeSupport42_suffix_020, ridgeSupport42_rest_020) := by rfl
theorem ridgeSupport42_suffix_decode_019 : PackedRawNatGrowth.readList 13 21 ridgeSupport42_rest_019 =
    (ridgeSupport42_suffix_019, ridgeSupport42_rest_020) :=
  PackedRawNatGrowth.readList_append_of_eq 13 21 0
    ridgeSupport42_rest_019 ridgeSupport42_rest_020 ridgeSupport42_rest_020
    ridgeSupport42_019 ridgeSupport42_suffix_020 ridgeSupport42_019_decode ridgeSupport42_suffix_decode_020
theorem ridgeSupport42_suffix_decode_018 : PackedRawNatGrowth.readList 13 53 ridgeSupport42_rest_018 =
    (ridgeSupport42_suffix_018, ridgeSupport42_rest_020) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 21
    ridgeSupport42_rest_018 ridgeSupport42_rest_019 ridgeSupport42_rest_020
    ridgeSupport42_018 ridgeSupport42_suffix_019 ridgeSupport42_018_decode ridgeSupport42_suffix_decode_019
theorem ridgeSupport42_suffix_decode_017 : PackedRawNatGrowth.readList 13 85 ridgeSupport42_rest_017 =
    (ridgeSupport42_suffix_017, ridgeSupport42_rest_020) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 53
    ridgeSupport42_rest_017 ridgeSupport42_rest_018 ridgeSupport42_rest_020
    ridgeSupport42_017 ridgeSupport42_suffix_018 ridgeSupport42_017_decode ridgeSupport42_suffix_decode_018
theorem ridgeSupport42_suffix_decode_016 : PackedRawNatGrowth.readList 13 117 ridgeSupport42_rest_016 =
    (ridgeSupport42_suffix_016, ridgeSupport42_rest_020) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 85
    ridgeSupport42_rest_016 ridgeSupport42_rest_017 ridgeSupport42_rest_020
    ridgeSupport42_016 ridgeSupport42_suffix_017 ridgeSupport42_016_decode ridgeSupport42_suffix_decode_017
theorem ridgeSupport42_suffix_decode_015 : PackedRawNatGrowth.readList 13 149 ridgeSupport42_rest_015 =
    (ridgeSupport42_suffix_015, ridgeSupport42_rest_020) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 117
    ridgeSupport42_rest_015 ridgeSupport42_rest_016 ridgeSupport42_rest_020
    ridgeSupport42_015 ridgeSupport42_suffix_016 ridgeSupport42_015_decode ridgeSupport42_suffix_decode_016
theorem ridgeSupport42_suffix_decode_014 : PackedRawNatGrowth.readList 13 181 ridgeSupport42_rest_014 =
    (ridgeSupport42_suffix_014, ridgeSupport42_rest_020) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 149
    ridgeSupport42_rest_014 ridgeSupport42_rest_015 ridgeSupport42_rest_020
    ridgeSupport42_014 ridgeSupport42_suffix_015 ridgeSupport42_014_decode ridgeSupport42_suffix_decode_015
theorem ridgeSupport42_suffix_decode_013 : PackedRawNatGrowth.readList 13 213 ridgeSupport42_rest_013 =
    (ridgeSupport42_suffix_013, ridgeSupport42_rest_020) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 181
    ridgeSupport42_rest_013 ridgeSupport42_rest_014 ridgeSupport42_rest_020
    ridgeSupport42_013 ridgeSupport42_suffix_014 ridgeSupport42_013_decode ridgeSupport42_suffix_decode_014
theorem ridgeSupport42_suffix_decode_012 : PackedRawNatGrowth.readList 13 245 ridgeSupport42_rest_012 =
    (ridgeSupport42_suffix_012, ridgeSupport42_rest_020) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 213
    ridgeSupport42_rest_012 ridgeSupport42_rest_013 ridgeSupport42_rest_020
    ridgeSupport42_012 ridgeSupport42_suffix_013 ridgeSupport42_012_decode ridgeSupport42_suffix_decode_013
theorem ridgeSupport42_suffix_decode_011 : PackedRawNatGrowth.readList 13 277 ridgeSupport42_rest_011 =
    (ridgeSupport42_suffix_011, ridgeSupport42_rest_020) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 245
    ridgeSupport42_rest_011 ridgeSupport42_rest_012 ridgeSupport42_rest_020
    ridgeSupport42_011 ridgeSupport42_suffix_012 ridgeSupport42_011_decode ridgeSupport42_suffix_decode_012
theorem ridgeSupport42_suffix_decode_010 : PackedRawNatGrowth.readList 13 309 ridgeSupport42_rest_010 =
    (ridgeSupport42_suffix_010, ridgeSupport42_rest_020) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 277
    ridgeSupport42_rest_010 ridgeSupport42_rest_011 ridgeSupport42_rest_020
    ridgeSupport42_010 ridgeSupport42_suffix_011 ridgeSupport42_010_decode ridgeSupport42_suffix_decode_011
theorem ridgeSupport42_suffix_decode_009 : PackedRawNatGrowth.readList 13 341 ridgeSupport42_rest_009 =
    (ridgeSupport42_suffix_009, ridgeSupport42_rest_020) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 309
    ridgeSupport42_rest_009 ridgeSupport42_rest_010 ridgeSupport42_rest_020
    ridgeSupport42_009 ridgeSupport42_suffix_010 ridgeSupport42_009_decode ridgeSupport42_suffix_decode_010
theorem ridgeSupport42_suffix_decode_008 : PackedRawNatGrowth.readList 13 373 ridgeSupport42_rest_008 =
    (ridgeSupport42_suffix_008, ridgeSupport42_rest_020) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 341
    ridgeSupport42_rest_008 ridgeSupport42_rest_009 ridgeSupport42_rest_020
    ridgeSupport42_008 ridgeSupport42_suffix_009 ridgeSupport42_008_decode ridgeSupport42_suffix_decode_009
theorem ridgeSupport42_suffix_decode_007 : PackedRawNatGrowth.readList 13 405 ridgeSupport42_rest_007 =
    (ridgeSupport42_suffix_007, ridgeSupport42_rest_020) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 373
    ridgeSupport42_rest_007 ridgeSupport42_rest_008 ridgeSupport42_rest_020
    ridgeSupport42_007 ridgeSupport42_suffix_008 ridgeSupport42_007_decode ridgeSupport42_suffix_decode_008
theorem ridgeSupport42_suffix_decode_006 : PackedRawNatGrowth.readList 13 437 ridgeSupport42_rest_006 =
    (ridgeSupport42_suffix_006, ridgeSupport42_rest_020) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 405
    ridgeSupport42_rest_006 ridgeSupport42_rest_007 ridgeSupport42_rest_020
    ridgeSupport42_006 ridgeSupport42_suffix_007 ridgeSupport42_006_decode ridgeSupport42_suffix_decode_007
theorem ridgeSupport42_suffix_decode_005 : PackedRawNatGrowth.readList 13 469 ridgeSupport42_rest_005 =
    (ridgeSupport42_suffix_005, ridgeSupport42_rest_020) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 437
    ridgeSupport42_rest_005 ridgeSupport42_rest_006 ridgeSupport42_rest_020
    ridgeSupport42_005 ridgeSupport42_suffix_006 ridgeSupport42_005_decode ridgeSupport42_suffix_decode_006
theorem ridgeSupport42_suffix_decode_004 : PackedRawNatGrowth.readList 13 501 ridgeSupport42_rest_004 =
    (ridgeSupport42_suffix_004, ridgeSupport42_rest_020) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 469
    ridgeSupport42_rest_004 ridgeSupport42_rest_005 ridgeSupport42_rest_020
    ridgeSupport42_004 ridgeSupport42_suffix_005 ridgeSupport42_004_decode ridgeSupport42_suffix_decode_005
theorem ridgeSupport42_suffix_decode_003 : PackedRawNatGrowth.readList 13 533 ridgeSupport42_rest_003 =
    (ridgeSupport42_suffix_003, ridgeSupport42_rest_020) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 501
    ridgeSupport42_rest_003 ridgeSupport42_rest_004 ridgeSupport42_rest_020
    ridgeSupport42_003 ridgeSupport42_suffix_004 ridgeSupport42_003_decode ridgeSupport42_suffix_decode_004
theorem ridgeSupport42_suffix_decode_002 : PackedRawNatGrowth.readList 13 565 ridgeSupport42_rest_002 =
    (ridgeSupport42_suffix_002, ridgeSupport42_rest_020) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 533
    ridgeSupport42_rest_002 ridgeSupport42_rest_003 ridgeSupport42_rest_020
    ridgeSupport42_002 ridgeSupport42_suffix_003 ridgeSupport42_002_decode ridgeSupport42_suffix_decode_003
theorem ridgeSupport42_suffix_decode_001 : PackedRawNatGrowth.readList 13 597 ridgeSupport42_rest_001 =
    (ridgeSupport42_suffix_001, ridgeSupport42_rest_020) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 565
    ridgeSupport42_rest_001 ridgeSupport42_rest_002 ridgeSupport42_rest_020
    ridgeSupport42_001 ridgeSupport42_suffix_002 ridgeSupport42_001_decode ridgeSupport42_suffix_decode_002
theorem ridgeSupport42_suffix_decode_000 : PackedRawNatGrowth.readList 13 629 ridgeSupport42_rest_000 =
    (ridgeSupport42_suffix_000, ridgeSupport42_rest_020) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 597
    ridgeSupport42_rest_000 ridgeSupport42_rest_001 ridgeSupport42_rest_020
    ridgeSupport42_000 ridgeSupport42_suffix_001 ridgeSupport42_000_decode ridgeSupport42_suffix_decode_001
theorem ridgeSupport42_eq : candidateRows 42 = ridgeSupport42_suffix_000 := by
  change candidateSupports 42 = ridgeSupport42_suffix_000
  rw [ridgeSupport42_source]
  exact congrArg Prod.fst ridgeSupport42_suffix_decode_000
theorem ridgeTest_large_42 : ridgeTest 42 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport42_eq]
    simp only [ridgeSupport42_suffix_000, ridgeSupport42_suffix_001, ridgeSupport42_suffix_002, ridgeSupport42_suffix_003, ridgeSupport42_suffix_004, ridgeSupport42_suffix_005, ridgeSupport42_suffix_006, ridgeSupport42_suffix_007, ridgeSupport42_suffix_008, ridgeSupport42_suffix_009, ridgeSupport42_suffix_010, ridgeSupport42_suffix_011, ridgeSupport42_suffix_012, ridgeSupport42_suffix_013, ridgeSupport42_suffix_014, ridgeSupport42_suffix_015, ridgeSupport42_suffix_016, ridgeSupport42_suffix_017, ridgeSupport42_suffix_018, ridgeSupport42_suffix_019, ridgeSupport42_suffix_020, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport42_000_mask, ridgeSupport42_001_mask, ridgeSupport42_002_mask, ridgeSupport42_003_mask, ridgeSupport42_004_mask, ridgeSupport42_005_mask, ridgeSupport42_006_mask, ridgeSupport42_007_mask, ridgeSupport42_008_mask, ridgeSupport42_009_mask, ridgeSupport42_010_mask, ridgeSupport42_011_mask, ridgeSupport42_012_mask, ridgeSupport42_013_mask, ridgeSupport42_014_mask, ridgeSupport42_015_mask, ridgeSupport42_016_mask, ridgeSupport42_017_mask, ridgeSupport42_018_mask, ridgeSupport42_019_mask]
    decide +kernel
  · rw [ridgeSupport42_eq]
    simp only [ridgeSupport42_suffix_000, ridgeSupport42_suffix_001, ridgeSupport42_suffix_002, ridgeSupport42_suffix_003, ridgeSupport42_suffix_004, ridgeSupport42_suffix_005, ridgeSupport42_suffix_006, ridgeSupport42_suffix_007, ridgeSupport42_suffix_008, ridgeSupport42_suffix_009, ridgeSupport42_suffix_010, ridgeSupport42_suffix_011, ridgeSupport42_suffix_012, ridgeSupport42_suffix_013, ridgeSupport42_suffix_014, ridgeSupport42_suffix_015, ridgeSupport42_suffix_016, ridgeSupport42_suffix_017, ridgeSupport42_suffix_018, ridgeSupport42_suffix_019, ridgeSupport42_suffix_020, List.all_append, List.all_nil, ridgeSupport42_000_checked, ridgeSupport42_001_checked, ridgeSupport42_002_checked, ridgeSupport42_003_checked, ridgeSupport42_004_checked, ridgeSupport42_005_checked, ridgeSupport42_006_checked, ridgeSupport42_007_checked, ridgeSupport42_008_checked, ridgeSupport42_009_checked, ridgeSupport42_010_checked, ridgeSupport42_011_checked, ridgeSupport42_012_checked, ridgeSupport42_013_checked, ridgeSupport42_014_checked, ridgeSupport42_015_checked, ridgeSupport42_016_checked, ridgeSupport42_017_checked, ridgeSupport42_018_checked, ridgeSupport42_019_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase02
