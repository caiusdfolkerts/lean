module
prelude
public import RootedSixBase01GrowthCacheRidgeSupport515Part000
public import RootedSixBase01GrowthCacheRidgeSupport515Part001
public import RootedSixBase01GrowthCacheRidgeSupport515Part002
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport515_suffix_decode_021 : PackedRawNatGrowth.readList 14 0 ridgeSupport515_rest_021 =
    (ridgeSupport515_suffix_021, ridgeSupport515_rest_021) := by rfl
theorem ridgeSupport515_suffix_decode_020 : PackedRawNatGrowth.readList 14 13 ridgeSupport515_rest_020 =
    (ridgeSupport515_suffix_020, ridgeSupport515_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 13 0
    ridgeSupport515_rest_020 ridgeSupport515_rest_021 ridgeSupport515_rest_021
    ridgeSupport515_020 ridgeSupport515_suffix_021 ridgeSupport515_020_decode ridgeSupport515_suffix_decode_021
theorem ridgeSupport515_suffix_decode_019 : PackedRawNatGrowth.readList 14 45 ridgeSupport515_rest_019 =
    (ridgeSupport515_suffix_019, ridgeSupport515_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 13
    ridgeSupport515_rest_019 ridgeSupport515_rest_020 ridgeSupport515_rest_021
    ridgeSupport515_019 ridgeSupport515_suffix_020 ridgeSupport515_019_decode ridgeSupport515_suffix_decode_020
theorem ridgeSupport515_suffix_decode_018 : PackedRawNatGrowth.readList 14 77 ridgeSupport515_rest_018 =
    (ridgeSupport515_suffix_018, ridgeSupport515_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 45
    ridgeSupport515_rest_018 ridgeSupport515_rest_019 ridgeSupport515_rest_021
    ridgeSupport515_018 ridgeSupport515_suffix_019 ridgeSupport515_018_decode ridgeSupport515_suffix_decode_019
theorem ridgeSupport515_suffix_decode_017 : PackedRawNatGrowth.readList 14 109 ridgeSupport515_rest_017 =
    (ridgeSupport515_suffix_017, ridgeSupport515_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 77
    ridgeSupport515_rest_017 ridgeSupport515_rest_018 ridgeSupport515_rest_021
    ridgeSupport515_017 ridgeSupport515_suffix_018 ridgeSupport515_017_decode ridgeSupport515_suffix_decode_018
theorem ridgeSupport515_suffix_decode_016 : PackedRawNatGrowth.readList 14 141 ridgeSupport515_rest_016 =
    (ridgeSupport515_suffix_016, ridgeSupport515_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 109
    ridgeSupport515_rest_016 ridgeSupport515_rest_017 ridgeSupport515_rest_021
    ridgeSupport515_016 ridgeSupport515_suffix_017 ridgeSupport515_016_decode ridgeSupport515_suffix_decode_017
theorem ridgeSupport515_suffix_decode_015 : PackedRawNatGrowth.readList 14 173 ridgeSupport515_rest_015 =
    (ridgeSupport515_suffix_015, ridgeSupport515_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 141
    ridgeSupport515_rest_015 ridgeSupport515_rest_016 ridgeSupport515_rest_021
    ridgeSupport515_015 ridgeSupport515_suffix_016 ridgeSupport515_015_decode ridgeSupport515_suffix_decode_016
theorem ridgeSupport515_suffix_decode_014 : PackedRawNatGrowth.readList 14 205 ridgeSupport515_rest_014 =
    (ridgeSupport515_suffix_014, ridgeSupport515_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 173
    ridgeSupport515_rest_014 ridgeSupport515_rest_015 ridgeSupport515_rest_021
    ridgeSupport515_014 ridgeSupport515_suffix_015 ridgeSupport515_014_decode ridgeSupport515_suffix_decode_015
theorem ridgeSupport515_suffix_decode_013 : PackedRawNatGrowth.readList 14 237 ridgeSupport515_rest_013 =
    (ridgeSupport515_suffix_013, ridgeSupport515_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 205
    ridgeSupport515_rest_013 ridgeSupport515_rest_014 ridgeSupport515_rest_021
    ridgeSupport515_013 ridgeSupport515_suffix_014 ridgeSupport515_013_decode ridgeSupport515_suffix_decode_014
theorem ridgeSupport515_suffix_decode_012 : PackedRawNatGrowth.readList 14 269 ridgeSupport515_rest_012 =
    (ridgeSupport515_suffix_012, ridgeSupport515_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 237
    ridgeSupport515_rest_012 ridgeSupport515_rest_013 ridgeSupport515_rest_021
    ridgeSupport515_012 ridgeSupport515_suffix_013 ridgeSupport515_012_decode ridgeSupport515_suffix_decode_013
theorem ridgeSupport515_suffix_decode_011 : PackedRawNatGrowth.readList 14 301 ridgeSupport515_rest_011 =
    (ridgeSupport515_suffix_011, ridgeSupport515_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 269
    ridgeSupport515_rest_011 ridgeSupport515_rest_012 ridgeSupport515_rest_021
    ridgeSupport515_011 ridgeSupport515_suffix_012 ridgeSupport515_011_decode ridgeSupport515_suffix_decode_012
theorem ridgeSupport515_suffix_decode_010 : PackedRawNatGrowth.readList 14 333 ridgeSupport515_rest_010 =
    (ridgeSupport515_suffix_010, ridgeSupport515_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 301
    ridgeSupport515_rest_010 ridgeSupport515_rest_011 ridgeSupport515_rest_021
    ridgeSupport515_010 ridgeSupport515_suffix_011 ridgeSupport515_010_decode ridgeSupport515_suffix_decode_011
theorem ridgeSupport515_suffix_decode_009 : PackedRawNatGrowth.readList 14 365 ridgeSupport515_rest_009 =
    (ridgeSupport515_suffix_009, ridgeSupport515_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 333
    ridgeSupport515_rest_009 ridgeSupport515_rest_010 ridgeSupport515_rest_021
    ridgeSupport515_009 ridgeSupport515_suffix_010 ridgeSupport515_009_decode ridgeSupport515_suffix_decode_010
theorem ridgeSupport515_suffix_decode_008 : PackedRawNatGrowth.readList 14 397 ridgeSupport515_rest_008 =
    (ridgeSupport515_suffix_008, ridgeSupport515_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 365
    ridgeSupport515_rest_008 ridgeSupport515_rest_009 ridgeSupport515_rest_021
    ridgeSupport515_008 ridgeSupport515_suffix_009 ridgeSupport515_008_decode ridgeSupport515_suffix_decode_009
theorem ridgeSupport515_suffix_decode_007 : PackedRawNatGrowth.readList 14 429 ridgeSupport515_rest_007 =
    (ridgeSupport515_suffix_007, ridgeSupport515_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 397
    ridgeSupport515_rest_007 ridgeSupport515_rest_008 ridgeSupport515_rest_021
    ridgeSupport515_007 ridgeSupport515_suffix_008 ridgeSupport515_007_decode ridgeSupport515_suffix_decode_008
theorem ridgeSupport515_suffix_decode_006 : PackedRawNatGrowth.readList 14 461 ridgeSupport515_rest_006 =
    (ridgeSupport515_suffix_006, ridgeSupport515_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 429
    ridgeSupport515_rest_006 ridgeSupport515_rest_007 ridgeSupport515_rest_021
    ridgeSupport515_006 ridgeSupport515_suffix_007 ridgeSupport515_006_decode ridgeSupport515_suffix_decode_007
theorem ridgeSupport515_suffix_decode_005 : PackedRawNatGrowth.readList 14 493 ridgeSupport515_rest_005 =
    (ridgeSupport515_suffix_005, ridgeSupport515_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 461
    ridgeSupport515_rest_005 ridgeSupport515_rest_006 ridgeSupport515_rest_021
    ridgeSupport515_005 ridgeSupport515_suffix_006 ridgeSupport515_005_decode ridgeSupport515_suffix_decode_006
theorem ridgeSupport515_suffix_decode_004 : PackedRawNatGrowth.readList 14 525 ridgeSupport515_rest_004 =
    (ridgeSupport515_suffix_004, ridgeSupport515_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 493
    ridgeSupport515_rest_004 ridgeSupport515_rest_005 ridgeSupport515_rest_021
    ridgeSupport515_004 ridgeSupport515_suffix_005 ridgeSupport515_004_decode ridgeSupport515_suffix_decode_005
theorem ridgeSupport515_suffix_decode_003 : PackedRawNatGrowth.readList 14 557 ridgeSupport515_rest_003 =
    (ridgeSupport515_suffix_003, ridgeSupport515_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 525
    ridgeSupport515_rest_003 ridgeSupport515_rest_004 ridgeSupport515_rest_021
    ridgeSupport515_003 ridgeSupport515_suffix_004 ridgeSupport515_003_decode ridgeSupport515_suffix_decode_004
theorem ridgeSupport515_suffix_decode_002 : PackedRawNatGrowth.readList 14 589 ridgeSupport515_rest_002 =
    (ridgeSupport515_suffix_002, ridgeSupport515_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 557
    ridgeSupport515_rest_002 ridgeSupport515_rest_003 ridgeSupport515_rest_021
    ridgeSupport515_002 ridgeSupport515_suffix_003 ridgeSupport515_002_decode ridgeSupport515_suffix_decode_003
theorem ridgeSupport515_suffix_decode_001 : PackedRawNatGrowth.readList 14 621 ridgeSupport515_rest_001 =
    (ridgeSupport515_suffix_001, ridgeSupport515_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 589
    ridgeSupport515_rest_001 ridgeSupport515_rest_002 ridgeSupport515_rest_021
    ridgeSupport515_001 ridgeSupport515_suffix_002 ridgeSupport515_001_decode ridgeSupport515_suffix_decode_002
theorem ridgeSupport515_suffix_decode_000 : PackedRawNatGrowth.readList 14 653 ridgeSupport515_rest_000 =
    (ridgeSupport515_suffix_000, ridgeSupport515_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 621
    ridgeSupport515_rest_000 ridgeSupport515_rest_001 ridgeSupport515_rest_021
    ridgeSupport515_000 ridgeSupport515_suffix_001 ridgeSupport515_000_decode ridgeSupport515_suffix_decode_001
theorem ridgeSupport515_eq : candidateRows 515 = ridgeSupport515_suffix_000 := by
  rw [ridgeSupport515_source]
  exact congrArg Prod.fst ridgeSupport515_suffix_decode_000
theorem ridgeTest_large_515 : ridgeTest 515 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport515_eq]
    simp only [ridgeSupport515_suffix_000, ridgeSupport515_suffix_001, ridgeSupport515_suffix_002, ridgeSupport515_suffix_003, ridgeSupport515_suffix_004, ridgeSupport515_suffix_005, ridgeSupport515_suffix_006, ridgeSupport515_suffix_007, ridgeSupport515_suffix_008, ridgeSupport515_suffix_009, ridgeSupport515_suffix_010, ridgeSupport515_suffix_011, ridgeSupport515_suffix_012, ridgeSupport515_suffix_013, ridgeSupport515_suffix_014, ridgeSupport515_suffix_015, ridgeSupport515_suffix_016, ridgeSupport515_suffix_017, ridgeSupport515_suffix_018, ridgeSupport515_suffix_019, ridgeSupport515_suffix_020, ridgeSupport515_suffix_021, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport515_000_mask, ridgeSupport515_001_mask, ridgeSupport515_002_mask, ridgeSupport515_003_mask, ridgeSupport515_004_mask, ridgeSupport515_005_mask, ridgeSupport515_006_mask, ridgeSupport515_007_mask, ridgeSupport515_008_mask, ridgeSupport515_009_mask, ridgeSupport515_010_mask, ridgeSupport515_011_mask, ridgeSupport515_012_mask, ridgeSupport515_013_mask, ridgeSupport515_014_mask, ridgeSupport515_015_mask, ridgeSupport515_016_mask, ridgeSupport515_017_mask, ridgeSupport515_018_mask, ridgeSupport515_019_mask, ridgeSupport515_020_mask]
    decide +kernel
  · rw [ridgeSupport515_eq]
    simp only [ridgeSupport515_suffix_000, ridgeSupport515_suffix_001, ridgeSupport515_suffix_002, ridgeSupport515_suffix_003, ridgeSupport515_suffix_004, ridgeSupport515_suffix_005, ridgeSupport515_suffix_006, ridgeSupport515_suffix_007, ridgeSupport515_suffix_008, ridgeSupport515_suffix_009, ridgeSupport515_suffix_010, ridgeSupport515_suffix_011, ridgeSupport515_suffix_012, ridgeSupport515_suffix_013, ridgeSupport515_suffix_014, ridgeSupport515_suffix_015, ridgeSupport515_suffix_016, ridgeSupport515_suffix_017, ridgeSupport515_suffix_018, ridgeSupport515_suffix_019, ridgeSupport515_suffix_020, ridgeSupport515_suffix_021, List.all_append, List.all_nil, ridgeSupport515_000_checked, ridgeSupport515_001_checked, ridgeSupport515_002_checked, ridgeSupport515_003_checked, ridgeSupport515_004_checked, ridgeSupport515_005_checked, ridgeSupport515_006_checked, ridgeSupport515_007_checked, ridgeSupport515_008_checked, ridgeSupport515_009_checked, ridgeSupport515_010_checked, ridgeSupport515_011_checked, ridgeSupport515_012_checked, ridgeSupport515_013_checked, ridgeSupport515_014_checked, ridgeSupport515_015_checked, ridgeSupport515_016_checked, ridgeSupport515_017_checked, ridgeSupport515_018_checked, ridgeSupport515_019_checked, ridgeSupport515_020_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase01
