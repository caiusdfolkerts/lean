module
prelude
public import RootedSixBase02GrowthCacheRidgeSupport11Part000
public import RootedSixBase02GrowthCacheRidgeSupport11Part001
public import RootedSixBase02GrowthCacheRidgeSupport11Part002
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase02
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport11_suffix_decode_020 : PackedRawNatGrowth.readList 13 0 ridgeSupport11_rest_020 =
    (ridgeSupport11_suffix_020, ridgeSupport11_rest_020) := by rfl
theorem ridgeSupport11_suffix_decode_019 : PackedRawNatGrowth.readList 13 21 ridgeSupport11_rest_019 =
    (ridgeSupport11_suffix_019, ridgeSupport11_rest_020) :=
  PackedRawNatGrowth.readList_append_of_eq 13 21 0
    ridgeSupport11_rest_019 ridgeSupport11_rest_020 ridgeSupport11_rest_020
    ridgeSupport11_019 ridgeSupport11_suffix_020 ridgeSupport11_019_decode ridgeSupport11_suffix_decode_020
theorem ridgeSupport11_suffix_decode_018 : PackedRawNatGrowth.readList 13 53 ridgeSupport11_rest_018 =
    (ridgeSupport11_suffix_018, ridgeSupport11_rest_020) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 21
    ridgeSupport11_rest_018 ridgeSupport11_rest_019 ridgeSupport11_rest_020
    ridgeSupport11_018 ridgeSupport11_suffix_019 ridgeSupport11_018_decode ridgeSupport11_suffix_decode_019
theorem ridgeSupport11_suffix_decode_017 : PackedRawNatGrowth.readList 13 85 ridgeSupport11_rest_017 =
    (ridgeSupport11_suffix_017, ridgeSupport11_rest_020) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 53
    ridgeSupport11_rest_017 ridgeSupport11_rest_018 ridgeSupport11_rest_020
    ridgeSupport11_017 ridgeSupport11_suffix_018 ridgeSupport11_017_decode ridgeSupport11_suffix_decode_018
theorem ridgeSupport11_suffix_decode_016 : PackedRawNatGrowth.readList 13 117 ridgeSupport11_rest_016 =
    (ridgeSupport11_suffix_016, ridgeSupport11_rest_020) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 85
    ridgeSupport11_rest_016 ridgeSupport11_rest_017 ridgeSupport11_rest_020
    ridgeSupport11_016 ridgeSupport11_suffix_017 ridgeSupport11_016_decode ridgeSupport11_suffix_decode_017
theorem ridgeSupport11_suffix_decode_015 : PackedRawNatGrowth.readList 13 149 ridgeSupport11_rest_015 =
    (ridgeSupport11_suffix_015, ridgeSupport11_rest_020) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 117
    ridgeSupport11_rest_015 ridgeSupport11_rest_016 ridgeSupport11_rest_020
    ridgeSupport11_015 ridgeSupport11_suffix_016 ridgeSupport11_015_decode ridgeSupport11_suffix_decode_016
theorem ridgeSupport11_suffix_decode_014 : PackedRawNatGrowth.readList 13 181 ridgeSupport11_rest_014 =
    (ridgeSupport11_suffix_014, ridgeSupport11_rest_020) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 149
    ridgeSupport11_rest_014 ridgeSupport11_rest_015 ridgeSupport11_rest_020
    ridgeSupport11_014 ridgeSupport11_suffix_015 ridgeSupport11_014_decode ridgeSupport11_suffix_decode_015
theorem ridgeSupport11_suffix_decode_013 : PackedRawNatGrowth.readList 13 213 ridgeSupport11_rest_013 =
    (ridgeSupport11_suffix_013, ridgeSupport11_rest_020) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 181
    ridgeSupport11_rest_013 ridgeSupport11_rest_014 ridgeSupport11_rest_020
    ridgeSupport11_013 ridgeSupport11_suffix_014 ridgeSupport11_013_decode ridgeSupport11_suffix_decode_014
theorem ridgeSupport11_suffix_decode_012 : PackedRawNatGrowth.readList 13 245 ridgeSupport11_rest_012 =
    (ridgeSupport11_suffix_012, ridgeSupport11_rest_020) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 213
    ridgeSupport11_rest_012 ridgeSupport11_rest_013 ridgeSupport11_rest_020
    ridgeSupport11_012 ridgeSupport11_suffix_013 ridgeSupport11_012_decode ridgeSupport11_suffix_decode_013
theorem ridgeSupport11_suffix_decode_011 : PackedRawNatGrowth.readList 13 277 ridgeSupport11_rest_011 =
    (ridgeSupport11_suffix_011, ridgeSupport11_rest_020) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 245
    ridgeSupport11_rest_011 ridgeSupport11_rest_012 ridgeSupport11_rest_020
    ridgeSupport11_011 ridgeSupport11_suffix_012 ridgeSupport11_011_decode ridgeSupport11_suffix_decode_012
theorem ridgeSupport11_suffix_decode_010 : PackedRawNatGrowth.readList 13 309 ridgeSupport11_rest_010 =
    (ridgeSupport11_suffix_010, ridgeSupport11_rest_020) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 277
    ridgeSupport11_rest_010 ridgeSupport11_rest_011 ridgeSupport11_rest_020
    ridgeSupport11_010 ridgeSupport11_suffix_011 ridgeSupport11_010_decode ridgeSupport11_suffix_decode_011
theorem ridgeSupport11_suffix_decode_009 : PackedRawNatGrowth.readList 13 341 ridgeSupport11_rest_009 =
    (ridgeSupport11_suffix_009, ridgeSupport11_rest_020) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 309
    ridgeSupport11_rest_009 ridgeSupport11_rest_010 ridgeSupport11_rest_020
    ridgeSupport11_009 ridgeSupport11_suffix_010 ridgeSupport11_009_decode ridgeSupport11_suffix_decode_010
theorem ridgeSupport11_suffix_decode_008 : PackedRawNatGrowth.readList 13 373 ridgeSupport11_rest_008 =
    (ridgeSupport11_suffix_008, ridgeSupport11_rest_020) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 341
    ridgeSupport11_rest_008 ridgeSupport11_rest_009 ridgeSupport11_rest_020
    ridgeSupport11_008 ridgeSupport11_suffix_009 ridgeSupport11_008_decode ridgeSupport11_suffix_decode_009
theorem ridgeSupport11_suffix_decode_007 : PackedRawNatGrowth.readList 13 405 ridgeSupport11_rest_007 =
    (ridgeSupport11_suffix_007, ridgeSupport11_rest_020) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 373
    ridgeSupport11_rest_007 ridgeSupport11_rest_008 ridgeSupport11_rest_020
    ridgeSupport11_007 ridgeSupport11_suffix_008 ridgeSupport11_007_decode ridgeSupport11_suffix_decode_008
theorem ridgeSupport11_suffix_decode_006 : PackedRawNatGrowth.readList 13 437 ridgeSupport11_rest_006 =
    (ridgeSupport11_suffix_006, ridgeSupport11_rest_020) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 405
    ridgeSupport11_rest_006 ridgeSupport11_rest_007 ridgeSupport11_rest_020
    ridgeSupport11_006 ridgeSupport11_suffix_007 ridgeSupport11_006_decode ridgeSupport11_suffix_decode_007
theorem ridgeSupport11_suffix_decode_005 : PackedRawNatGrowth.readList 13 469 ridgeSupport11_rest_005 =
    (ridgeSupport11_suffix_005, ridgeSupport11_rest_020) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 437
    ridgeSupport11_rest_005 ridgeSupport11_rest_006 ridgeSupport11_rest_020
    ridgeSupport11_005 ridgeSupport11_suffix_006 ridgeSupport11_005_decode ridgeSupport11_suffix_decode_006
theorem ridgeSupport11_suffix_decode_004 : PackedRawNatGrowth.readList 13 501 ridgeSupport11_rest_004 =
    (ridgeSupport11_suffix_004, ridgeSupport11_rest_020) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 469
    ridgeSupport11_rest_004 ridgeSupport11_rest_005 ridgeSupport11_rest_020
    ridgeSupport11_004 ridgeSupport11_suffix_005 ridgeSupport11_004_decode ridgeSupport11_suffix_decode_005
theorem ridgeSupport11_suffix_decode_003 : PackedRawNatGrowth.readList 13 533 ridgeSupport11_rest_003 =
    (ridgeSupport11_suffix_003, ridgeSupport11_rest_020) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 501
    ridgeSupport11_rest_003 ridgeSupport11_rest_004 ridgeSupport11_rest_020
    ridgeSupport11_003 ridgeSupport11_suffix_004 ridgeSupport11_003_decode ridgeSupport11_suffix_decode_004
theorem ridgeSupport11_suffix_decode_002 : PackedRawNatGrowth.readList 13 565 ridgeSupport11_rest_002 =
    (ridgeSupport11_suffix_002, ridgeSupport11_rest_020) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 533
    ridgeSupport11_rest_002 ridgeSupport11_rest_003 ridgeSupport11_rest_020
    ridgeSupport11_002 ridgeSupport11_suffix_003 ridgeSupport11_002_decode ridgeSupport11_suffix_decode_003
theorem ridgeSupport11_suffix_decode_001 : PackedRawNatGrowth.readList 13 597 ridgeSupport11_rest_001 =
    (ridgeSupport11_suffix_001, ridgeSupport11_rest_020) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 565
    ridgeSupport11_rest_001 ridgeSupport11_rest_002 ridgeSupport11_rest_020
    ridgeSupport11_001 ridgeSupport11_suffix_002 ridgeSupport11_001_decode ridgeSupport11_suffix_decode_002
theorem ridgeSupport11_suffix_decode_000 : PackedRawNatGrowth.readList 13 629 ridgeSupport11_rest_000 =
    (ridgeSupport11_suffix_000, ridgeSupport11_rest_020) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 597
    ridgeSupport11_rest_000 ridgeSupport11_rest_001 ridgeSupport11_rest_020
    ridgeSupport11_000 ridgeSupport11_suffix_001 ridgeSupport11_000_decode ridgeSupport11_suffix_decode_001
theorem ridgeSupport11_eq : candidateRows 11 = ridgeSupport11_suffix_000 := by
  change candidateSupports 11 = ridgeSupport11_suffix_000
  rw [ridgeSupport11_source]
  exact congrArg Prod.fst ridgeSupport11_suffix_decode_000
theorem ridgeTest_large_11 : ridgeTest 11 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport11_eq]
    simp only [ridgeSupport11_suffix_000, ridgeSupport11_suffix_001, ridgeSupport11_suffix_002, ridgeSupport11_suffix_003, ridgeSupport11_suffix_004, ridgeSupport11_suffix_005, ridgeSupport11_suffix_006, ridgeSupport11_suffix_007, ridgeSupport11_suffix_008, ridgeSupport11_suffix_009, ridgeSupport11_suffix_010, ridgeSupport11_suffix_011, ridgeSupport11_suffix_012, ridgeSupport11_suffix_013, ridgeSupport11_suffix_014, ridgeSupport11_suffix_015, ridgeSupport11_suffix_016, ridgeSupport11_suffix_017, ridgeSupport11_suffix_018, ridgeSupport11_suffix_019, ridgeSupport11_suffix_020, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport11_000_mask, ridgeSupport11_001_mask, ridgeSupport11_002_mask, ridgeSupport11_003_mask, ridgeSupport11_004_mask, ridgeSupport11_005_mask, ridgeSupport11_006_mask, ridgeSupport11_007_mask, ridgeSupport11_008_mask, ridgeSupport11_009_mask, ridgeSupport11_010_mask, ridgeSupport11_011_mask, ridgeSupport11_012_mask, ridgeSupport11_013_mask, ridgeSupport11_014_mask, ridgeSupport11_015_mask, ridgeSupport11_016_mask, ridgeSupport11_017_mask, ridgeSupport11_018_mask, ridgeSupport11_019_mask]
    decide +kernel
  · rw [ridgeSupport11_eq]
    simp only [ridgeSupport11_suffix_000, ridgeSupport11_suffix_001, ridgeSupport11_suffix_002, ridgeSupport11_suffix_003, ridgeSupport11_suffix_004, ridgeSupport11_suffix_005, ridgeSupport11_suffix_006, ridgeSupport11_suffix_007, ridgeSupport11_suffix_008, ridgeSupport11_suffix_009, ridgeSupport11_suffix_010, ridgeSupport11_suffix_011, ridgeSupport11_suffix_012, ridgeSupport11_suffix_013, ridgeSupport11_suffix_014, ridgeSupport11_suffix_015, ridgeSupport11_suffix_016, ridgeSupport11_suffix_017, ridgeSupport11_suffix_018, ridgeSupport11_suffix_019, ridgeSupport11_suffix_020, List.all_append, List.all_nil, ridgeSupport11_000_checked, ridgeSupport11_001_checked, ridgeSupport11_002_checked, ridgeSupport11_003_checked, ridgeSupport11_004_checked, ridgeSupport11_005_checked, ridgeSupport11_006_checked, ridgeSupport11_007_checked, ridgeSupport11_008_checked, ridgeSupport11_009_checked, ridgeSupport11_010_checked, ridgeSupport11_011_checked, ridgeSupport11_012_checked, ridgeSupport11_013_checked, ridgeSupport11_014_checked, ridgeSupport11_015_checked, ridgeSupport11_016_checked, ridgeSupport11_017_checked, ridgeSupport11_018_checked, ridgeSupport11_019_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase02
