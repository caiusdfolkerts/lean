module
prelude
public import RootedSixBase01GrowthCacheRidgeSupport261Part000
public import RootedSixBase01GrowthCacheRidgeSupport261Part001
public import RootedSixBase01GrowthCacheRidgeSupport261Part002
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport261_suffix_decode_021 : PackedRawNatGrowth.readList 14 0 ridgeSupport261_rest_021 =
    (ridgeSupport261_suffix_021, ridgeSupport261_rest_021) := by rfl
theorem ridgeSupport261_suffix_decode_020 : PackedRawNatGrowth.readList 14 13 ridgeSupport261_rest_020 =
    (ridgeSupport261_suffix_020, ridgeSupport261_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 13 0
    ridgeSupport261_rest_020 ridgeSupport261_rest_021 ridgeSupport261_rest_021
    ridgeSupport261_020 ridgeSupport261_suffix_021 ridgeSupport261_020_decode ridgeSupport261_suffix_decode_021
theorem ridgeSupport261_suffix_decode_019 : PackedRawNatGrowth.readList 14 45 ridgeSupport261_rest_019 =
    (ridgeSupport261_suffix_019, ridgeSupport261_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 13
    ridgeSupport261_rest_019 ridgeSupport261_rest_020 ridgeSupport261_rest_021
    ridgeSupport261_019 ridgeSupport261_suffix_020 ridgeSupport261_019_decode ridgeSupport261_suffix_decode_020
theorem ridgeSupport261_suffix_decode_018 : PackedRawNatGrowth.readList 14 77 ridgeSupport261_rest_018 =
    (ridgeSupport261_suffix_018, ridgeSupport261_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 45
    ridgeSupport261_rest_018 ridgeSupport261_rest_019 ridgeSupport261_rest_021
    ridgeSupport261_018 ridgeSupport261_suffix_019 ridgeSupport261_018_decode ridgeSupport261_suffix_decode_019
theorem ridgeSupport261_suffix_decode_017 : PackedRawNatGrowth.readList 14 109 ridgeSupport261_rest_017 =
    (ridgeSupport261_suffix_017, ridgeSupport261_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 77
    ridgeSupport261_rest_017 ridgeSupport261_rest_018 ridgeSupport261_rest_021
    ridgeSupport261_017 ridgeSupport261_suffix_018 ridgeSupport261_017_decode ridgeSupport261_suffix_decode_018
theorem ridgeSupport261_suffix_decode_016 : PackedRawNatGrowth.readList 14 141 ridgeSupport261_rest_016 =
    (ridgeSupport261_suffix_016, ridgeSupport261_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 109
    ridgeSupport261_rest_016 ridgeSupport261_rest_017 ridgeSupport261_rest_021
    ridgeSupport261_016 ridgeSupport261_suffix_017 ridgeSupport261_016_decode ridgeSupport261_suffix_decode_017
theorem ridgeSupport261_suffix_decode_015 : PackedRawNatGrowth.readList 14 173 ridgeSupport261_rest_015 =
    (ridgeSupport261_suffix_015, ridgeSupport261_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 141
    ridgeSupport261_rest_015 ridgeSupport261_rest_016 ridgeSupport261_rest_021
    ridgeSupport261_015 ridgeSupport261_suffix_016 ridgeSupport261_015_decode ridgeSupport261_suffix_decode_016
theorem ridgeSupport261_suffix_decode_014 : PackedRawNatGrowth.readList 14 205 ridgeSupport261_rest_014 =
    (ridgeSupport261_suffix_014, ridgeSupport261_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 173
    ridgeSupport261_rest_014 ridgeSupport261_rest_015 ridgeSupport261_rest_021
    ridgeSupport261_014 ridgeSupport261_suffix_015 ridgeSupport261_014_decode ridgeSupport261_suffix_decode_015
theorem ridgeSupport261_suffix_decode_013 : PackedRawNatGrowth.readList 14 237 ridgeSupport261_rest_013 =
    (ridgeSupport261_suffix_013, ridgeSupport261_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 205
    ridgeSupport261_rest_013 ridgeSupport261_rest_014 ridgeSupport261_rest_021
    ridgeSupport261_013 ridgeSupport261_suffix_014 ridgeSupport261_013_decode ridgeSupport261_suffix_decode_014
theorem ridgeSupport261_suffix_decode_012 : PackedRawNatGrowth.readList 14 269 ridgeSupport261_rest_012 =
    (ridgeSupport261_suffix_012, ridgeSupport261_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 237
    ridgeSupport261_rest_012 ridgeSupport261_rest_013 ridgeSupport261_rest_021
    ridgeSupport261_012 ridgeSupport261_suffix_013 ridgeSupport261_012_decode ridgeSupport261_suffix_decode_013
theorem ridgeSupport261_suffix_decode_011 : PackedRawNatGrowth.readList 14 301 ridgeSupport261_rest_011 =
    (ridgeSupport261_suffix_011, ridgeSupport261_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 269
    ridgeSupport261_rest_011 ridgeSupport261_rest_012 ridgeSupport261_rest_021
    ridgeSupport261_011 ridgeSupport261_suffix_012 ridgeSupport261_011_decode ridgeSupport261_suffix_decode_012
theorem ridgeSupport261_suffix_decode_010 : PackedRawNatGrowth.readList 14 333 ridgeSupport261_rest_010 =
    (ridgeSupport261_suffix_010, ridgeSupport261_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 301
    ridgeSupport261_rest_010 ridgeSupport261_rest_011 ridgeSupport261_rest_021
    ridgeSupport261_010 ridgeSupport261_suffix_011 ridgeSupport261_010_decode ridgeSupport261_suffix_decode_011
theorem ridgeSupport261_suffix_decode_009 : PackedRawNatGrowth.readList 14 365 ridgeSupport261_rest_009 =
    (ridgeSupport261_suffix_009, ridgeSupport261_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 333
    ridgeSupport261_rest_009 ridgeSupport261_rest_010 ridgeSupport261_rest_021
    ridgeSupport261_009 ridgeSupport261_suffix_010 ridgeSupport261_009_decode ridgeSupport261_suffix_decode_010
theorem ridgeSupport261_suffix_decode_008 : PackedRawNatGrowth.readList 14 397 ridgeSupport261_rest_008 =
    (ridgeSupport261_suffix_008, ridgeSupport261_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 365
    ridgeSupport261_rest_008 ridgeSupport261_rest_009 ridgeSupport261_rest_021
    ridgeSupport261_008 ridgeSupport261_suffix_009 ridgeSupport261_008_decode ridgeSupport261_suffix_decode_009
theorem ridgeSupport261_suffix_decode_007 : PackedRawNatGrowth.readList 14 429 ridgeSupport261_rest_007 =
    (ridgeSupport261_suffix_007, ridgeSupport261_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 397
    ridgeSupport261_rest_007 ridgeSupport261_rest_008 ridgeSupport261_rest_021
    ridgeSupport261_007 ridgeSupport261_suffix_008 ridgeSupport261_007_decode ridgeSupport261_suffix_decode_008
theorem ridgeSupport261_suffix_decode_006 : PackedRawNatGrowth.readList 14 461 ridgeSupport261_rest_006 =
    (ridgeSupport261_suffix_006, ridgeSupport261_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 429
    ridgeSupport261_rest_006 ridgeSupport261_rest_007 ridgeSupport261_rest_021
    ridgeSupport261_006 ridgeSupport261_suffix_007 ridgeSupport261_006_decode ridgeSupport261_suffix_decode_007
theorem ridgeSupport261_suffix_decode_005 : PackedRawNatGrowth.readList 14 493 ridgeSupport261_rest_005 =
    (ridgeSupport261_suffix_005, ridgeSupport261_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 461
    ridgeSupport261_rest_005 ridgeSupport261_rest_006 ridgeSupport261_rest_021
    ridgeSupport261_005 ridgeSupport261_suffix_006 ridgeSupport261_005_decode ridgeSupport261_suffix_decode_006
theorem ridgeSupport261_suffix_decode_004 : PackedRawNatGrowth.readList 14 525 ridgeSupport261_rest_004 =
    (ridgeSupport261_suffix_004, ridgeSupport261_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 493
    ridgeSupport261_rest_004 ridgeSupport261_rest_005 ridgeSupport261_rest_021
    ridgeSupport261_004 ridgeSupport261_suffix_005 ridgeSupport261_004_decode ridgeSupport261_suffix_decode_005
theorem ridgeSupport261_suffix_decode_003 : PackedRawNatGrowth.readList 14 557 ridgeSupport261_rest_003 =
    (ridgeSupport261_suffix_003, ridgeSupport261_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 525
    ridgeSupport261_rest_003 ridgeSupport261_rest_004 ridgeSupport261_rest_021
    ridgeSupport261_003 ridgeSupport261_suffix_004 ridgeSupport261_003_decode ridgeSupport261_suffix_decode_004
theorem ridgeSupport261_suffix_decode_002 : PackedRawNatGrowth.readList 14 589 ridgeSupport261_rest_002 =
    (ridgeSupport261_suffix_002, ridgeSupport261_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 557
    ridgeSupport261_rest_002 ridgeSupport261_rest_003 ridgeSupport261_rest_021
    ridgeSupport261_002 ridgeSupport261_suffix_003 ridgeSupport261_002_decode ridgeSupport261_suffix_decode_003
theorem ridgeSupport261_suffix_decode_001 : PackedRawNatGrowth.readList 14 621 ridgeSupport261_rest_001 =
    (ridgeSupport261_suffix_001, ridgeSupport261_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 589
    ridgeSupport261_rest_001 ridgeSupport261_rest_002 ridgeSupport261_rest_021
    ridgeSupport261_001 ridgeSupport261_suffix_002 ridgeSupport261_001_decode ridgeSupport261_suffix_decode_002
theorem ridgeSupport261_suffix_decode_000 : PackedRawNatGrowth.readList 14 653 ridgeSupport261_rest_000 =
    (ridgeSupport261_suffix_000, ridgeSupport261_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 621
    ridgeSupport261_rest_000 ridgeSupport261_rest_001 ridgeSupport261_rest_021
    ridgeSupport261_000 ridgeSupport261_suffix_001 ridgeSupport261_000_decode ridgeSupport261_suffix_decode_001
theorem ridgeSupport261_eq : candidateRows 261 = ridgeSupport261_suffix_000 := by
  rw [ridgeSupport261_source]
  exact congrArg Prod.fst ridgeSupport261_suffix_decode_000
theorem ridgeTest_large_261 : ridgeTest 261 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport261_eq]
    simp only [ridgeSupport261_suffix_000, ridgeSupport261_suffix_001, ridgeSupport261_suffix_002, ridgeSupport261_suffix_003, ridgeSupport261_suffix_004, ridgeSupport261_suffix_005, ridgeSupport261_suffix_006, ridgeSupport261_suffix_007, ridgeSupport261_suffix_008, ridgeSupport261_suffix_009, ridgeSupport261_suffix_010, ridgeSupport261_suffix_011, ridgeSupport261_suffix_012, ridgeSupport261_suffix_013, ridgeSupport261_suffix_014, ridgeSupport261_suffix_015, ridgeSupport261_suffix_016, ridgeSupport261_suffix_017, ridgeSupport261_suffix_018, ridgeSupport261_suffix_019, ridgeSupport261_suffix_020, ridgeSupport261_suffix_021, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport261_000_mask, ridgeSupport261_001_mask, ridgeSupport261_002_mask, ridgeSupport261_003_mask, ridgeSupport261_004_mask, ridgeSupport261_005_mask, ridgeSupport261_006_mask, ridgeSupport261_007_mask, ridgeSupport261_008_mask, ridgeSupport261_009_mask, ridgeSupport261_010_mask, ridgeSupport261_011_mask, ridgeSupport261_012_mask, ridgeSupport261_013_mask, ridgeSupport261_014_mask, ridgeSupport261_015_mask, ridgeSupport261_016_mask, ridgeSupport261_017_mask, ridgeSupport261_018_mask, ridgeSupport261_019_mask, ridgeSupport261_020_mask]
    decide +kernel
  · rw [ridgeSupport261_eq]
    simp only [ridgeSupport261_suffix_000, ridgeSupport261_suffix_001, ridgeSupport261_suffix_002, ridgeSupport261_suffix_003, ridgeSupport261_suffix_004, ridgeSupport261_suffix_005, ridgeSupport261_suffix_006, ridgeSupport261_suffix_007, ridgeSupport261_suffix_008, ridgeSupport261_suffix_009, ridgeSupport261_suffix_010, ridgeSupport261_suffix_011, ridgeSupport261_suffix_012, ridgeSupport261_suffix_013, ridgeSupport261_suffix_014, ridgeSupport261_suffix_015, ridgeSupport261_suffix_016, ridgeSupport261_suffix_017, ridgeSupport261_suffix_018, ridgeSupport261_suffix_019, ridgeSupport261_suffix_020, ridgeSupport261_suffix_021, List.all_append, List.all_nil, ridgeSupport261_000_checked, ridgeSupport261_001_checked, ridgeSupport261_002_checked, ridgeSupport261_003_checked, ridgeSupport261_004_checked, ridgeSupport261_005_checked, ridgeSupport261_006_checked, ridgeSupport261_007_checked, ridgeSupport261_008_checked, ridgeSupport261_009_checked, ridgeSupport261_010_checked, ridgeSupport261_011_checked, ridgeSupport261_012_checked, ridgeSupport261_013_checked, ridgeSupport261_014_checked, ridgeSupport261_015_checked, ridgeSupport261_016_checked, ridgeSupport261_017_checked, ridgeSupport261_018_checked, ridgeSupport261_019_checked, ridgeSupport261_020_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase01
