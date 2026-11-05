module
prelude
public import RootedSixBase01GrowthCacheRidgeSupport262Part000
public import RootedSixBase01GrowthCacheRidgeSupport262Part001
public import RootedSixBase01GrowthCacheRidgeSupport262Part002
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport262_suffix_decode_021 : PackedRawNatGrowth.readList 14 0 ridgeSupport262_rest_021 =
    (ridgeSupport262_suffix_021, ridgeSupport262_rest_021) := by rfl
theorem ridgeSupport262_suffix_decode_020 : PackedRawNatGrowth.readList 14 13 ridgeSupport262_rest_020 =
    (ridgeSupport262_suffix_020, ridgeSupport262_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 13 0
    ridgeSupport262_rest_020 ridgeSupport262_rest_021 ridgeSupport262_rest_021
    ridgeSupport262_020 ridgeSupport262_suffix_021 ridgeSupport262_020_decode ridgeSupport262_suffix_decode_021
theorem ridgeSupport262_suffix_decode_019 : PackedRawNatGrowth.readList 14 45 ridgeSupport262_rest_019 =
    (ridgeSupport262_suffix_019, ridgeSupport262_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 13
    ridgeSupport262_rest_019 ridgeSupport262_rest_020 ridgeSupport262_rest_021
    ridgeSupport262_019 ridgeSupport262_suffix_020 ridgeSupport262_019_decode ridgeSupport262_suffix_decode_020
theorem ridgeSupport262_suffix_decode_018 : PackedRawNatGrowth.readList 14 77 ridgeSupport262_rest_018 =
    (ridgeSupport262_suffix_018, ridgeSupport262_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 45
    ridgeSupport262_rest_018 ridgeSupport262_rest_019 ridgeSupport262_rest_021
    ridgeSupport262_018 ridgeSupport262_suffix_019 ridgeSupport262_018_decode ridgeSupport262_suffix_decode_019
theorem ridgeSupport262_suffix_decode_017 : PackedRawNatGrowth.readList 14 109 ridgeSupport262_rest_017 =
    (ridgeSupport262_suffix_017, ridgeSupport262_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 77
    ridgeSupport262_rest_017 ridgeSupport262_rest_018 ridgeSupport262_rest_021
    ridgeSupport262_017 ridgeSupport262_suffix_018 ridgeSupport262_017_decode ridgeSupport262_suffix_decode_018
theorem ridgeSupport262_suffix_decode_016 : PackedRawNatGrowth.readList 14 141 ridgeSupport262_rest_016 =
    (ridgeSupport262_suffix_016, ridgeSupport262_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 109
    ridgeSupport262_rest_016 ridgeSupport262_rest_017 ridgeSupport262_rest_021
    ridgeSupport262_016 ridgeSupport262_suffix_017 ridgeSupport262_016_decode ridgeSupport262_suffix_decode_017
theorem ridgeSupport262_suffix_decode_015 : PackedRawNatGrowth.readList 14 173 ridgeSupport262_rest_015 =
    (ridgeSupport262_suffix_015, ridgeSupport262_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 141
    ridgeSupport262_rest_015 ridgeSupport262_rest_016 ridgeSupport262_rest_021
    ridgeSupport262_015 ridgeSupport262_suffix_016 ridgeSupport262_015_decode ridgeSupport262_suffix_decode_016
theorem ridgeSupport262_suffix_decode_014 : PackedRawNatGrowth.readList 14 205 ridgeSupport262_rest_014 =
    (ridgeSupport262_suffix_014, ridgeSupport262_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 173
    ridgeSupport262_rest_014 ridgeSupport262_rest_015 ridgeSupport262_rest_021
    ridgeSupport262_014 ridgeSupport262_suffix_015 ridgeSupport262_014_decode ridgeSupport262_suffix_decode_015
theorem ridgeSupport262_suffix_decode_013 : PackedRawNatGrowth.readList 14 237 ridgeSupport262_rest_013 =
    (ridgeSupport262_suffix_013, ridgeSupport262_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 205
    ridgeSupport262_rest_013 ridgeSupport262_rest_014 ridgeSupport262_rest_021
    ridgeSupport262_013 ridgeSupport262_suffix_014 ridgeSupport262_013_decode ridgeSupport262_suffix_decode_014
theorem ridgeSupport262_suffix_decode_012 : PackedRawNatGrowth.readList 14 269 ridgeSupport262_rest_012 =
    (ridgeSupport262_suffix_012, ridgeSupport262_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 237
    ridgeSupport262_rest_012 ridgeSupport262_rest_013 ridgeSupport262_rest_021
    ridgeSupport262_012 ridgeSupport262_suffix_013 ridgeSupport262_012_decode ridgeSupport262_suffix_decode_013
theorem ridgeSupport262_suffix_decode_011 : PackedRawNatGrowth.readList 14 301 ridgeSupport262_rest_011 =
    (ridgeSupport262_suffix_011, ridgeSupport262_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 269
    ridgeSupport262_rest_011 ridgeSupport262_rest_012 ridgeSupport262_rest_021
    ridgeSupport262_011 ridgeSupport262_suffix_012 ridgeSupport262_011_decode ridgeSupport262_suffix_decode_012
theorem ridgeSupport262_suffix_decode_010 : PackedRawNatGrowth.readList 14 333 ridgeSupport262_rest_010 =
    (ridgeSupport262_suffix_010, ridgeSupport262_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 301
    ridgeSupport262_rest_010 ridgeSupport262_rest_011 ridgeSupport262_rest_021
    ridgeSupport262_010 ridgeSupport262_suffix_011 ridgeSupport262_010_decode ridgeSupport262_suffix_decode_011
theorem ridgeSupport262_suffix_decode_009 : PackedRawNatGrowth.readList 14 365 ridgeSupport262_rest_009 =
    (ridgeSupport262_suffix_009, ridgeSupport262_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 333
    ridgeSupport262_rest_009 ridgeSupport262_rest_010 ridgeSupport262_rest_021
    ridgeSupport262_009 ridgeSupport262_suffix_010 ridgeSupport262_009_decode ridgeSupport262_suffix_decode_010
theorem ridgeSupport262_suffix_decode_008 : PackedRawNatGrowth.readList 14 397 ridgeSupport262_rest_008 =
    (ridgeSupport262_suffix_008, ridgeSupport262_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 365
    ridgeSupport262_rest_008 ridgeSupport262_rest_009 ridgeSupport262_rest_021
    ridgeSupport262_008 ridgeSupport262_suffix_009 ridgeSupport262_008_decode ridgeSupport262_suffix_decode_009
theorem ridgeSupport262_suffix_decode_007 : PackedRawNatGrowth.readList 14 429 ridgeSupport262_rest_007 =
    (ridgeSupport262_suffix_007, ridgeSupport262_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 397
    ridgeSupport262_rest_007 ridgeSupport262_rest_008 ridgeSupport262_rest_021
    ridgeSupport262_007 ridgeSupport262_suffix_008 ridgeSupport262_007_decode ridgeSupport262_suffix_decode_008
theorem ridgeSupport262_suffix_decode_006 : PackedRawNatGrowth.readList 14 461 ridgeSupport262_rest_006 =
    (ridgeSupport262_suffix_006, ridgeSupport262_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 429
    ridgeSupport262_rest_006 ridgeSupport262_rest_007 ridgeSupport262_rest_021
    ridgeSupport262_006 ridgeSupport262_suffix_007 ridgeSupport262_006_decode ridgeSupport262_suffix_decode_007
theorem ridgeSupport262_suffix_decode_005 : PackedRawNatGrowth.readList 14 493 ridgeSupport262_rest_005 =
    (ridgeSupport262_suffix_005, ridgeSupport262_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 461
    ridgeSupport262_rest_005 ridgeSupport262_rest_006 ridgeSupport262_rest_021
    ridgeSupport262_005 ridgeSupport262_suffix_006 ridgeSupport262_005_decode ridgeSupport262_suffix_decode_006
theorem ridgeSupport262_suffix_decode_004 : PackedRawNatGrowth.readList 14 525 ridgeSupport262_rest_004 =
    (ridgeSupport262_suffix_004, ridgeSupport262_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 493
    ridgeSupport262_rest_004 ridgeSupport262_rest_005 ridgeSupport262_rest_021
    ridgeSupport262_004 ridgeSupport262_suffix_005 ridgeSupport262_004_decode ridgeSupport262_suffix_decode_005
theorem ridgeSupport262_suffix_decode_003 : PackedRawNatGrowth.readList 14 557 ridgeSupport262_rest_003 =
    (ridgeSupport262_suffix_003, ridgeSupport262_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 525
    ridgeSupport262_rest_003 ridgeSupport262_rest_004 ridgeSupport262_rest_021
    ridgeSupport262_003 ridgeSupport262_suffix_004 ridgeSupport262_003_decode ridgeSupport262_suffix_decode_004
theorem ridgeSupport262_suffix_decode_002 : PackedRawNatGrowth.readList 14 589 ridgeSupport262_rest_002 =
    (ridgeSupport262_suffix_002, ridgeSupport262_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 557
    ridgeSupport262_rest_002 ridgeSupport262_rest_003 ridgeSupport262_rest_021
    ridgeSupport262_002 ridgeSupport262_suffix_003 ridgeSupport262_002_decode ridgeSupport262_suffix_decode_003
theorem ridgeSupport262_suffix_decode_001 : PackedRawNatGrowth.readList 14 621 ridgeSupport262_rest_001 =
    (ridgeSupport262_suffix_001, ridgeSupport262_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 589
    ridgeSupport262_rest_001 ridgeSupport262_rest_002 ridgeSupport262_rest_021
    ridgeSupport262_001 ridgeSupport262_suffix_002 ridgeSupport262_001_decode ridgeSupport262_suffix_decode_002
theorem ridgeSupport262_suffix_decode_000 : PackedRawNatGrowth.readList 14 653 ridgeSupport262_rest_000 =
    (ridgeSupport262_suffix_000, ridgeSupport262_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 621
    ridgeSupport262_rest_000 ridgeSupport262_rest_001 ridgeSupport262_rest_021
    ridgeSupport262_000 ridgeSupport262_suffix_001 ridgeSupport262_000_decode ridgeSupport262_suffix_decode_001
theorem ridgeSupport262_eq : candidateRows 262 = ridgeSupport262_suffix_000 := by
  rw [ridgeSupport262_source]
  exact congrArg Prod.fst ridgeSupport262_suffix_decode_000
theorem ridgeTest_large_262 : ridgeTest 262 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport262_eq]
    simp only [ridgeSupport262_suffix_000, ridgeSupport262_suffix_001, ridgeSupport262_suffix_002, ridgeSupport262_suffix_003, ridgeSupport262_suffix_004, ridgeSupport262_suffix_005, ridgeSupport262_suffix_006, ridgeSupport262_suffix_007, ridgeSupport262_suffix_008, ridgeSupport262_suffix_009, ridgeSupport262_suffix_010, ridgeSupport262_suffix_011, ridgeSupport262_suffix_012, ridgeSupport262_suffix_013, ridgeSupport262_suffix_014, ridgeSupport262_suffix_015, ridgeSupport262_suffix_016, ridgeSupport262_suffix_017, ridgeSupport262_suffix_018, ridgeSupport262_suffix_019, ridgeSupport262_suffix_020, ridgeSupport262_suffix_021, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport262_000_mask, ridgeSupport262_001_mask, ridgeSupport262_002_mask, ridgeSupport262_003_mask, ridgeSupport262_004_mask, ridgeSupport262_005_mask, ridgeSupport262_006_mask, ridgeSupport262_007_mask, ridgeSupport262_008_mask, ridgeSupport262_009_mask, ridgeSupport262_010_mask, ridgeSupport262_011_mask, ridgeSupport262_012_mask, ridgeSupport262_013_mask, ridgeSupport262_014_mask, ridgeSupport262_015_mask, ridgeSupport262_016_mask, ridgeSupport262_017_mask, ridgeSupport262_018_mask, ridgeSupport262_019_mask, ridgeSupport262_020_mask]
    decide +kernel
  · rw [ridgeSupport262_eq]
    simp only [ridgeSupport262_suffix_000, ridgeSupport262_suffix_001, ridgeSupport262_suffix_002, ridgeSupport262_suffix_003, ridgeSupport262_suffix_004, ridgeSupport262_suffix_005, ridgeSupport262_suffix_006, ridgeSupport262_suffix_007, ridgeSupport262_suffix_008, ridgeSupport262_suffix_009, ridgeSupport262_suffix_010, ridgeSupport262_suffix_011, ridgeSupport262_suffix_012, ridgeSupport262_suffix_013, ridgeSupport262_suffix_014, ridgeSupport262_suffix_015, ridgeSupport262_suffix_016, ridgeSupport262_suffix_017, ridgeSupport262_suffix_018, ridgeSupport262_suffix_019, ridgeSupport262_suffix_020, ridgeSupport262_suffix_021, List.all_append, List.all_nil, ridgeSupport262_000_checked, ridgeSupport262_001_checked, ridgeSupport262_002_checked, ridgeSupport262_003_checked, ridgeSupport262_004_checked, ridgeSupport262_005_checked, ridgeSupport262_006_checked, ridgeSupport262_007_checked, ridgeSupport262_008_checked, ridgeSupport262_009_checked, ridgeSupport262_010_checked, ridgeSupport262_011_checked, ridgeSupport262_012_checked, ridgeSupport262_013_checked, ridgeSupport262_014_checked, ridgeSupport262_015_checked, ridgeSupport262_016_checked, ridgeSupport262_017_checked, ridgeSupport262_018_checked, ridgeSupport262_019_checked, ridgeSupport262_020_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase01
