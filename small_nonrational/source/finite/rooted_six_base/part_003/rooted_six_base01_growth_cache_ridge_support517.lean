module
prelude
public import RootedSixBase01GrowthCacheRidgeSupport517Part000
public import RootedSixBase01GrowthCacheRidgeSupport517Part001
public import RootedSixBase01GrowthCacheRidgeSupport517Part002
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport517_suffix_decode_021 : PackedRawNatGrowth.readList 14 0 ridgeSupport517_rest_021 =
    (ridgeSupport517_suffix_021, ridgeSupport517_rest_021) := by rfl
theorem ridgeSupport517_suffix_decode_020 : PackedRawNatGrowth.readList 14 13 ridgeSupport517_rest_020 =
    (ridgeSupport517_suffix_020, ridgeSupport517_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 13 0
    ridgeSupport517_rest_020 ridgeSupport517_rest_021 ridgeSupport517_rest_021
    ridgeSupport517_020 ridgeSupport517_suffix_021 ridgeSupport517_020_decode ridgeSupport517_suffix_decode_021
theorem ridgeSupport517_suffix_decode_019 : PackedRawNatGrowth.readList 14 45 ridgeSupport517_rest_019 =
    (ridgeSupport517_suffix_019, ridgeSupport517_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 13
    ridgeSupport517_rest_019 ridgeSupport517_rest_020 ridgeSupport517_rest_021
    ridgeSupport517_019 ridgeSupport517_suffix_020 ridgeSupport517_019_decode ridgeSupport517_suffix_decode_020
theorem ridgeSupport517_suffix_decode_018 : PackedRawNatGrowth.readList 14 77 ridgeSupport517_rest_018 =
    (ridgeSupport517_suffix_018, ridgeSupport517_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 45
    ridgeSupport517_rest_018 ridgeSupport517_rest_019 ridgeSupport517_rest_021
    ridgeSupport517_018 ridgeSupport517_suffix_019 ridgeSupport517_018_decode ridgeSupport517_suffix_decode_019
theorem ridgeSupport517_suffix_decode_017 : PackedRawNatGrowth.readList 14 109 ridgeSupport517_rest_017 =
    (ridgeSupport517_suffix_017, ridgeSupport517_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 77
    ridgeSupport517_rest_017 ridgeSupport517_rest_018 ridgeSupport517_rest_021
    ridgeSupport517_017 ridgeSupport517_suffix_018 ridgeSupport517_017_decode ridgeSupport517_suffix_decode_018
theorem ridgeSupport517_suffix_decode_016 : PackedRawNatGrowth.readList 14 141 ridgeSupport517_rest_016 =
    (ridgeSupport517_suffix_016, ridgeSupport517_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 109
    ridgeSupport517_rest_016 ridgeSupport517_rest_017 ridgeSupport517_rest_021
    ridgeSupport517_016 ridgeSupport517_suffix_017 ridgeSupport517_016_decode ridgeSupport517_suffix_decode_017
theorem ridgeSupport517_suffix_decode_015 : PackedRawNatGrowth.readList 14 173 ridgeSupport517_rest_015 =
    (ridgeSupport517_suffix_015, ridgeSupport517_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 141
    ridgeSupport517_rest_015 ridgeSupport517_rest_016 ridgeSupport517_rest_021
    ridgeSupport517_015 ridgeSupport517_suffix_016 ridgeSupport517_015_decode ridgeSupport517_suffix_decode_016
theorem ridgeSupport517_suffix_decode_014 : PackedRawNatGrowth.readList 14 205 ridgeSupport517_rest_014 =
    (ridgeSupport517_suffix_014, ridgeSupport517_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 173
    ridgeSupport517_rest_014 ridgeSupport517_rest_015 ridgeSupport517_rest_021
    ridgeSupport517_014 ridgeSupport517_suffix_015 ridgeSupport517_014_decode ridgeSupport517_suffix_decode_015
theorem ridgeSupport517_suffix_decode_013 : PackedRawNatGrowth.readList 14 237 ridgeSupport517_rest_013 =
    (ridgeSupport517_suffix_013, ridgeSupport517_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 205
    ridgeSupport517_rest_013 ridgeSupport517_rest_014 ridgeSupport517_rest_021
    ridgeSupport517_013 ridgeSupport517_suffix_014 ridgeSupport517_013_decode ridgeSupport517_suffix_decode_014
theorem ridgeSupport517_suffix_decode_012 : PackedRawNatGrowth.readList 14 269 ridgeSupport517_rest_012 =
    (ridgeSupport517_suffix_012, ridgeSupport517_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 237
    ridgeSupport517_rest_012 ridgeSupport517_rest_013 ridgeSupport517_rest_021
    ridgeSupport517_012 ridgeSupport517_suffix_013 ridgeSupport517_012_decode ridgeSupport517_suffix_decode_013
theorem ridgeSupport517_suffix_decode_011 : PackedRawNatGrowth.readList 14 301 ridgeSupport517_rest_011 =
    (ridgeSupport517_suffix_011, ridgeSupport517_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 269
    ridgeSupport517_rest_011 ridgeSupport517_rest_012 ridgeSupport517_rest_021
    ridgeSupport517_011 ridgeSupport517_suffix_012 ridgeSupport517_011_decode ridgeSupport517_suffix_decode_012
theorem ridgeSupport517_suffix_decode_010 : PackedRawNatGrowth.readList 14 333 ridgeSupport517_rest_010 =
    (ridgeSupport517_suffix_010, ridgeSupport517_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 301
    ridgeSupport517_rest_010 ridgeSupport517_rest_011 ridgeSupport517_rest_021
    ridgeSupport517_010 ridgeSupport517_suffix_011 ridgeSupport517_010_decode ridgeSupport517_suffix_decode_011
theorem ridgeSupport517_suffix_decode_009 : PackedRawNatGrowth.readList 14 365 ridgeSupport517_rest_009 =
    (ridgeSupport517_suffix_009, ridgeSupport517_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 333
    ridgeSupport517_rest_009 ridgeSupport517_rest_010 ridgeSupport517_rest_021
    ridgeSupport517_009 ridgeSupport517_suffix_010 ridgeSupport517_009_decode ridgeSupport517_suffix_decode_010
theorem ridgeSupport517_suffix_decode_008 : PackedRawNatGrowth.readList 14 397 ridgeSupport517_rest_008 =
    (ridgeSupport517_suffix_008, ridgeSupport517_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 365
    ridgeSupport517_rest_008 ridgeSupport517_rest_009 ridgeSupport517_rest_021
    ridgeSupport517_008 ridgeSupport517_suffix_009 ridgeSupport517_008_decode ridgeSupport517_suffix_decode_009
theorem ridgeSupport517_suffix_decode_007 : PackedRawNatGrowth.readList 14 429 ridgeSupport517_rest_007 =
    (ridgeSupport517_suffix_007, ridgeSupport517_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 397
    ridgeSupport517_rest_007 ridgeSupport517_rest_008 ridgeSupport517_rest_021
    ridgeSupport517_007 ridgeSupport517_suffix_008 ridgeSupport517_007_decode ridgeSupport517_suffix_decode_008
theorem ridgeSupport517_suffix_decode_006 : PackedRawNatGrowth.readList 14 461 ridgeSupport517_rest_006 =
    (ridgeSupport517_suffix_006, ridgeSupport517_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 429
    ridgeSupport517_rest_006 ridgeSupport517_rest_007 ridgeSupport517_rest_021
    ridgeSupport517_006 ridgeSupport517_suffix_007 ridgeSupport517_006_decode ridgeSupport517_suffix_decode_007
theorem ridgeSupport517_suffix_decode_005 : PackedRawNatGrowth.readList 14 493 ridgeSupport517_rest_005 =
    (ridgeSupport517_suffix_005, ridgeSupport517_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 461
    ridgeSupport517_rest_005 ridgeSupport517_rest_006 ridgeSupport517_rest_021
    ridgeSupport517_005 ridgeSupport517_suffix_006 ridgeSupport517_005_decode ridgeSupport517_suffix_decode_006
theorem ridgeSupport517_suffix_decode_004 : PackedRawNatGrowth.readList 14 525 ridgeSupport517_rest_004 =
    (ridgeSupport517_suffix_004, ridgeSupport517_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 493
    ridgeSupport517_rest_004 ridgeSupport517_rest_005 ridgeSupport517_rest_021
    ridgeSupport517_004 ridgeSupport517_suffix_005 ridgeSupport517_004_decode ridgeSupport517_suffix_decode_005
theorem ridgeSupport517_suffix_decode_003 : PackedRawNatGrowth.readList 14 557 ridgeSupport517_rest_003 =
    (ridgeSupport517_suffix_003, ridgeSupport517_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 525
    ridgeSupport517_rest_003 ridgeSupport517_rest_004 ridgeSupport517_rest_021
    ridgeSupport517_003 ridgeSupport517_suffix_004 ridgeSupport517_003_decode ridgeSupport517_suffix_decode_004
theorem ridgeSupport517_suffix_decode_002 : PackedRawNatGrowth.readList 14 589 ridgeSupport517_rest_002 =
    (ridgeSupport517_suffix_002, ridgeSupport517_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 557
    ridgeSupport517_rest_002 ridgeSupport517_rest_003 ridgeSupport517_rest_021
    ridgeSupport517_002 ridgeSupport517_suffix_003 ridgeSupport517_002_decode ridgeSupport517_suffix_decode_003
theorem ridgeSupport517_suffix_decode_001 : PackedRawNatGrowth.readList 14 621 ridgeSupport517_rest_001 =
    (ridgeSupport517_suffix_001, ridgeSupport517_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 589
    ridgeSupport517_rest_001 ridgeSupport517_rest_002 ridgeSupport517_rest_021
    ridgeSupport517_001 ridgeSupport517_suffix_002 ridgeSupport517_001_decode ridgeSupport517_suffix_decode_002
theorem ridgeSupport517_suffix_decode_000 : PackedRawNatGrowth.readList 14 653 ridgeSupport517_rest_000 =
    (ridgeSupport517_suffix_000, ridgeSupport517_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 621
    ridgeSupport517_rest_000 ridgeSupport517_rest_001 ridgeSupport517_rest_021
    ridgeSupport517_000 ridgeSupport517_suffix_001 ridgeSupport517_000_decode ridgeSupport517_suffix_decode_001
theorem ridgeSupport517_eq : candidateRows 517 = ridgeSupport517_suffix_000 := by
  rw [ridgeSupport517_source]
  exact congrArg Prod.fst ridgeSupport517_suffix_decode_000
theorem ridgeTest_large_517 : ridgeTest 517 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport517_eq]
    simp only [ridgeSupport517_suffix_000, ridgeSupport517_suffix_001, ridgeSupport517_suffix_002, ridgeSupport517_suffix_003, ridgeSupport517_suffix_004, ridgeSupport517_suffix_005, ridgeSupport517_suffix_006, ridgeSupport517_suffix_007, ridgeSupport517_suffix_008, ridgeSupport517_suffix_009, ridgeSupport517_suffix_010, ridgeSupport517_suffix_011, ridgeSupport517_suffix_012, ridgeSupport517_suffix_013, ridgeSupport517_suffix_014, ridgeSupport517_suffix_015, ridgeSupport517_suffix_016, ridgeSupport517_suffix_017, ridgeSupport517_suffix_018, ridgeSupport517_suffix_019, ridgeSupport517_suffix_020, ridgeSupport517_suffix_021, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport517_000_mask, ridgeSupport517_001_mask, ridgeSupport517_002_mask, ridgeSupport517_003_mask, ridgeSupport517_004_mask, ridgeSupport517_005_mask, ridgeSupport517_006_mask, ridgeSupport517_007_mask, ridgeSupport517_008_mask, ridgeSupport517_009_mask, ridgeSupport517_010_mask, ridgeSupport517_011_mask, ridgeSupport517_012_mask, ridgeSupport517_013_mask, ridgeSupport517_014_mask, ridgeSupport517_015_mask, ridgeSupport517_016_mask, ridgeSupport517_017_mask, ridgeSupport517_018_mask, ridgeSupport517_019_mask, ridgeSupport517_020_mask]
    decide +kernel
  · rw [ridgeSupport517_eq]
    simp only [ridgeSupport517_suffix_000, ridgeSupport517_suffix_001, ridgeSupport517_suffix_002, ridgeSupport517_suffix_003, ridgeSupport517_suffix_004, ridgeSupport517_suffix_005, ridgeSupport517_suffix_006, ridgeSupport517_suffix_007, ridgeSupport517_suffix_008, ridgeSupport517_suffix_009, ridgeSupport517_suffix_010, ridgeSupport517_suffix_011, ridgeSupport517_suffix_012, ridgeSupport517_suffix_013, ridgeSupport517_suffix_014, ridgeSupport517_suffix_015, ridgeSupport517_suffix_016, ridgeSupport517_suffix_017, ridgeSupport517_suffix_018, ridgeSupport517_suffix_019, ridgeSupport517_suffix_020, ridgeSupport517_suffix_021, List.all_append, List.all_nil, ridgeSupport517_000_checked, ridgeSupport517_001_checked, ridgeSupport517_002_checked, ridgeSupport517_003_checked, ridgeSupport517_004_checked, ridgeSupport517_005_checked, ridgeSupport517_006_checked, ridgeSupport517_007_checked, ridgeSupport517_008_checked, ridgeSupport517_009_checked, ridgeSupport517_010_checked, ridgeSupport517_011_checked, ridgeSupport517_012_checked, ridgeSupport517_013_checked, ridgeSupport517_014_checked, ridgeSupport517_015_checked, ridgeSupport517_016_checked, ridgeSupport517_017_checked, ridgeSupport517_018_checked, ridgeSupport517_019_checked, ridgeSupport517_020_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase01
