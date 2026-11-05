module
prelude
public import RootedSixBase01GrowthCacheRidgeSupport70Part000
public import RootedSixBase01GrowthCacheRidgeSupport70Part001
public import RootedSixBase01GrowthCacheRidgeSupport70Part002
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport70_suffix_decode_021 : PackedRawNatGrowth.readList 14 0 ridgeSupport70_rest_021 =
    (ridgeSupport70_suffix_021, ridgeSupport70_rest_021) := by rfl
theorem ridgeSupport70_suffix_decode_020 : PackedRawNatGrowth.readList 14 13 ridgeSupport70_rest_020 =
    (ridgeSupport70_suffix_020, ridgeSupport70_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 13 0
    ridgeSupport70_rest_020 ridgeSupport70_rest_021 ridgeSupport70_rest_021
    ridgeSupport70_020 ridgeSupport70_suffix_021 ridgeSupport70_020_decode ridgeSupport70_suffix_decode_021
theorem ridgeSupport70_suffix_decode_019 : PackedRawNatGrowth.readList 14 45 ridgeSupport70_rest_019 =
    (ridgeSupport70_suffix_019, ridgeSupport70_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 13
    ridgeSupport70_rest_019 ridgeSupport70_rest_020 ridgeSupport70_rest_021
    ridgeSupport70_019 ridgeSupport70_suffix_020 ridgeSupport70_019_decode ridgeSupport70_suffix_decode_020
theorem ridgeSupport70_suffix_decode_018 : PackedRawNatGrowth.readList 14 77 ridgeSupport70_rest_018 =
    (ridgeSupport70_suffix_018, ridgeSupport70_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 45
    ridgeSupport70_rest_018 ridgeSupport70_rest_019 ridgeSupport70_rest_021
    ridgeSupport70_018 ridgeSupport70_suffix_019 ridgeSupport70_018_decode ridgeSupport70_suffix_decode_019
theorem ridgeSupport70_suffix_decode_017 : PackedRawNatGrowth.readList 14 109 ridgeSupport70_rest_017 =
    (ridgeSupport70_suffix_017, ridgeSupport70_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 77
    ridgeSupport70_rest_017 ridgeSupport70_rest_018 ridgeSupport70_rest_021
    ridgeSupport70_017 ridgeSupport70_suffix_018 ridgeSupport70_017_decode ridgeSupport70_suffix_decode_018
theorem ridgeSupport70_suffix_decode_016 : PackedRawNatGrowth.readList 14 141 ridgeSupport70_rest_016 =
    (ridgeSupport70_suffix_016, ridgeSupport70_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 109
    ridgeSupport70_rest_016 ridgeSupport70_rest_017 ridgeSupport70_rest_021
    ridgeSupport70_016 ridgeSupport70_suffix_017 ridgeSupport70_016_decode ridgeSupport70_suffix_decode_017
theorem ridgeSupport70_suffix_decode_015 : PackedRawNatGrowth.readList 14 173 ridgeSupport70_rest_015 =
    (ridgeSupport70_suffix_015, ridgeSupport70_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 141
    ridgeSupport70_rest_015 ridgeSupport70_rest_016 ridgeSupport70_rest_021
    ridgeSupport70_015 ridgeSupport70_suffix_016 ridgeSupport70_015_decode ridgeSupport70_suffix_decode_016
theorem ridgeSupport70_suffix_decode_014 : PackedRawNatGrowth.readList 14 205 ridgeSupport70_rest_014 =
    (ridgeSupport70_suffix_014, ridgeSupport70_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 173
    ridgeSupport70_rest_014 ridgeSupport70_rest_015 ridgeSupport70_rest_021
    ridgeSupport70_014 ridgeSupport70_suffix_015 ridgeSupport70_014_decode ridgeSupport70_suffix_decode_015
theorem ridgeSupport70_suffix_decode_013 : PackedRawNatGrowth.readList 14 237 ridgeSupport70_rest_013 =
    (ridgeSupport70_suffix_013, ridgeSupport70_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 205
    ridgeSupport70_rest_013 ridgeSupport70_rest_014 ridgeSupport70_rest_021
    ridgeSupport70_013 ridgeSupport70_suffix_014 ridgeSupport70_013_decode ridgeSupport70_suffix_decode_014
theorem ridgeSupport70_suffix_decode_012 : PackedRawNatGrowth.readList 14 269 ridgeSupport70_rest_012 =
    (ridgeSupport70_suffix_012, ridgeSupport70_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 237
    ridgeSupport70_rest_012 ridgeSupport70_rest_013 ridgeSupport70_rest_021
    ridgeSupport70_012 ridgeSupport70_suffix_013 ridgeSupport70_012_decode ridgeSupport70_suffix_decode_013
theorem ridgeSupport70_suffix_decode_011 : PackedRawNatGrowth.readList 14 301 ridgeSupport70_rest_011 =
    (ridgeSupport70_suffix_011, ridgeSupport70_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 269
    ridgeSupport70_rest_011 ridgeSupport70_rest_012 ridgeSupport70_rest_021
    ridgeSupport70_011 ridgeSupport70_suffix_012 ridgeSupport70_011_decode ridgeSupport70_suffix_decode_012
theorem ridgeSupport70_suffix_decode_010 : PackedRawNatGrowth.readList 14 333 ridgeSupport70_rest_010 =
    (ridgeSupport70_suffix_010, ridgeSupport70_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 301
    ridgeSupport70_rest_010 ridgeSupport70_rest_011 ridgeSupport70_rest_021
    ridgeSupport70_010 ridgeSupport70_suffix_011 ridgeSupport70_010_decode ridgeSupport70_suffix_decode_011
theorem ridgeSupport70_suffix_decode_009 : PackedRawNatGrowth.readList 14 365 ridgeSupport70_rest_009 =
    (ridgeSupport70_suffix_009, ridgeSupport70_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 333
    ridgeSupport70_rest_009 ridgeSupport70_rest_010 ridgeSupport70_rest_021
    ridgeSupport70_009 ridgeSupport70_suffix_010 ridgeSupport70_009_decode ridgeSupport70_suffix_decode_010
theorem ridgeSupport70_suffix_decode_008 : PackedRawNatGrowth.readList 14 397 ridgeSupport70_rest_008 =
    (ridgeSupport70_suffix_008, ridgeSupport70_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 365
    ridgeSupport70_rest_008 ridgeSupport70_rest_009 ridgeSupport70_rest_021
    ridgeSupport70_008 ridgeSupport70_suffix_009 ridgeSupport70_008_decode ridgeSupport70_suffix_decode_009
theorem ridgeSupport70_suffix_decode_007 : PackedRawNatGrowth.readList 14 429 ridgeSupport70_rest_007 =
    (ridgeSupport70_suffix_007, ridgeSupport70_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 397
    ridgeSupport70_rest_007 ridgeSupport70_rest_008 ridgeSupport70_rest_021
    ridgeSupport70_007 ridgeSupport70_suffix_008 ridgeSupport70_007_decode ridgeSupport70_suffix_decode_008
theorem ridgeSupport70_suffix_decode_006 : PackedRawNatGrowth.readList 14 461 ridgeSupport70_rest_006 =
    (ridgeSupport70_suffix_006, ridgeSupport70_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 429
    ridgeSupport70_rest_006 ridgeSupport70_rest_007 ridgeSupport70_rest_021
    ridgeSupport70_006 ridgeSupport70_suffix_007 ridgeSupport70_006_decode ridgeSupport70_suffix_decode_007
theorem ridgeSupport70_suffix_decode_005 : PackedRawNatGrowth.readList 14 493 ridgeSupport70_rest_005 =
    (ridgeSupport70_suffix_005, ridgeSupport70_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 461
    ridgeSupport70_rest_005 ridgeSupport70_rest_006 ridgeSupport70_rest_021
    ridgeSupport70_005 ridgeSupport70_suffix_006 ridgeSupport70_005_decode ridgeSupport70_suffix_decode_006
theorem ridgeSupport70_suffix_decode_004 : PackedRawNatGrowth.readList 14 525 ridgeSupport70_rest_004 =
    (ridgeSupport70_suffix_004, ridgeSupport70_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 493
    ridgeSupport70_rest_004 ridgeSupport70_rest_005 ridgeSupport70_rest_021
    ridgeSupport70_004 ridgeSupport70_suffix_005 ridgeSupport70_004_decode ridgeSupport70_suffix_decode_005
theorem ridgeSupport70_suffix_decode_003 : PackedRawNatGrowth.readList 14 557 ridgeSupport70_rest_003 =
    (ridgeSupport70_suffix_003, ridgeSupport70_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 525
    ridgeSupport70_rest_003 ridgeSupport70_rest_004 ridgeSupport70_rest_021
    ridgeSupport70_003 ridgeSupport70_suffix_004 ridgeSupport70_003_decode ridgeSupport70_suffix_decode_004
theorem ridgeSupport70_suffix_decode_002 : PackedRawNatGrowth.readList 14 589 ridgeSupport70_rest_002 =
    (ridgeSupport70_suffix_002, ridgeSupport70_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 557
    ridgeSupport70_rest_002 ridgeSupport70_rest_003 ridgeSupport70_rest_021
    ridgeSupport70_002 ridgeSupport70_suffix_003 ridgeSupport70_002_decode ridgeSupport70_suffix_decode_003
theorem ridgeSupport70_suffix_decode_001 : PackedRawNatGrowth.readList 14 621 ridgeSupport70_rest_001 =
    (ridgeSupport70_suffix_001, ridgeSupport70_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 589
    ridgeSupport70_rest_001 ridgeSupport70_rest_002 ridgeSupport70_rest_021
    ridgeSupport70_001 ridgeSupport70_suffix_002 ridgeSupport70_001_decode ridgeSupport70_suffix_decode_002
theorem ridgeSupport70_suffix_decode_000 : PackedRawNatGrowth.readList 14 653 ridgeSupport70_rest_000 =
    (ridgeSupport70_suffix_000, ridgeSupport70_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 621
    ridgeSupport70_rest_000 ridgeSupport70_rest_001 ridgeSupport70_rest_021
    ridgeSupport70_000 ridgeSupport70_suffix_001 ridgeSupport70_000_decode ridgeSupport70_suffix_decode_001
theorem ridgeSupport70_eq : candidateRows 70 = ridgeSupport70_suffix_000 := by
  rw [ridgeSupport70_source]
  exact congrArg Prod.fst ridgeSupport70_suffix_decode_000
theorem ridgeTest_large_70 : ridgeTest 70 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport70_eq]
    simp only [ridgeSupport70_suffix_000, ridgeSupport70_suffix_001, ridgeSupport70_suffix_002, ridgeSupport70_suffix_003, ridgeSupport70_suffix_004, ridgeSupport70_suffix_005, ridgeSupport70_suffix_006, ridgeSupport70_suffix_007, ridgeSupport70_suffix_008, ridgeSupport70_suffix_009, ridgeSupport70_suffix_010, ridgeSupport70_suffix_011, ridgeSupport70_suffix_012, ridgeSupport70_suffix_013, ridgeSupport70_suffix_014, ridgeSupport70_suffix_015, ridgeSupport70_suffix_016, ridgeSupport70_suffix_017, ridgeSupport70_suffix_018, ridgeSupport70_suffix_019, ridgeSupport70_suffix_020, ridgeSupport70_suffix_021, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport70_000_mask, ridgeSupport70_001_mask, ridgeSupport70_002_mask, ridgeSupport70_003_mask, ridgeSupport70_004_mask, ridgeSupport70_005_mask, ridgeSupport70_006_mask, ridgeSupport70_007_mask, ridgeSupport70_008_mask, ridgeSupport70_009_mask, ridgeSupport70_010_mask, ridgeSupport70_011_mask, ridgeSupport70_012_mask, ridgeSupport70_013_mask, ridgeSupport70_014_mask, ridgeSupport70_015_mask, ridgeSupport70_016_mask, ridgeSupport70_017_mask, ridgeSupport70_018_mask, ridgeSupport70_019_mask, ridgeSupport70_020_mask]
    decide +kernel
  · rw [ridgeSupport70_eq]
    simp only [ridgeSupport70_suffix_000, ridgeSupport70_suffix_001, ridgeSupport70_suffix_002, ridgeSupport70_suffix_003, ridgeSupport70_suffix_004, ridgeSupport70_suffix_005, ridgeSupport70_suffix_006, ridgeSupport70_suffix_007, ridgeSupport70_suffix_008, ridgeSupport70_suffix_009, ridgeSupport70_suffix_010, ridgeSupport70_suffix_011, ridgeSupport70_suffix_012, ridgeSupport70_suffix_013, ridgeSupport70_suffix_014, ridgeSupport70_suffix_015, ridgeSupport70_suffix_016, ridgeSupport70_suffix_017, ridgeSupport70_suffix_018, ridgeSupport70_suffix_019, ridgeSupport70_suffix_020, ridgeSupport70_suffix_021, List.all_append, List.all_nil, ridgeSupport70_000_checked, ridgeSupport70_001_checked, ridgeSupport70_002_checked, ridgeSupport70_003_checked, ridgeSupport70_004_checked, ridgeSupport70_005_checked, ridgeSupport70_006_checked, ridgeSupport70_007_checked, ridgeSupport70_008_checked, ridgeSupport70_009_checked, ridgeSupport70_010_checked, ridgeSupport70_011_checked, ridgeSupport70_012_checked, ridgeSupport70_013_checked, ridgeSupport70_014_checked, ridgeSupport70_015_checked, ridgeSupport70_016_checked, ridgeSupport70_017_checked, ridgeSupport70_018_checked, ridgeSupport70_019_checked, ridgeSupport70_020_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase01
