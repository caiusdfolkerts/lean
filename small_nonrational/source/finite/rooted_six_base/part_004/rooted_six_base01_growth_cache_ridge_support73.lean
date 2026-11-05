module
prelude
public import RootedSixBase01GrowthCacheRidgeSupport73Part000
public import RootedSixBase01GrowthCacheRidgeSupport73Part001
public import RootedSixBase01GrowthCacheRidgeSupport73Part002
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport73_suffix_decode_021 : PackedRawNatGrowth.readList 14 0 ridgeSupport73_rest_021 =
    (ridgeSupport73_suffix_021, ridgeSupport73_rest_021) := by rfl
theorem ridgeSupport73_suffix_decode_020 : PackedRawNatGrowth.readList 14 13 ridgeSupport73_rest_020 =
    (ridgeSupport73_suffix_020, ridgeSupport73_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 13 0
    ridgeSupport73_rest_020 ridgeSupport73_rest_021 ridgeSupport73_rest_021
    ridgeSupport73_020 ridgeSupport73_suffix_021 ridgeSupport73_020_decode ridgeSupport73_suffix_decode_021
theorem ridgeSupport73_suffix_decode_019 : PackedRawNatGrowth.readList 14 45 ridgeSupport73_rest_019 =
    (ridgeSupport73_suffix_019, ridgeSupport73_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 13
    ridgeSupport73_rest_019 ridgeSupport73_rest_020 ridgeSupport73_rest_021
    ridgeSupport73_019 ridgeSupport73_suffix_020 ridgeSupport73_019_decode ridgeSupport73_suffix_decode_020
theorem ridgeSupport73_suffix_decode_018 : PackedRawNatGrowth.readList 14 77 ridgeSupport73_rest_018 =
    (ridgeSupport73_suffix_018, ridgeSupport73_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 45
    ridgeSupport73_rest_018 ridgeSupport73_rest_019 ridgeSupport73_rest_021
    ridgeSupport73_018 ridgeSupport73_suffix_019 ridgeSupport73_018_decode ridgeSupport73_suffix_decode_019
theorem ridgeSupport73_suffix_decode_017 : PackedRawNatGrowth.readList 14 109 ridgeSupport73_rest_017 =
    (ridgeSupport73_suffix_017, ridgeSupport73_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 77
    ridgeSupport73_rest_017 ridgeSupport73_rest_018 ridgeSupport73_rest_021
    ridgeSupport73_017 ridgeSupport73_suffix_018 ridgeSupport73_017_decode ridgeSupport73_suffix_decode_018
theorem ridgeSupport73_suffix_decode_016 : PackedRawNatGrowth.readList 14 141 ridgeSupport73_rest_016 =
    (ridgeSupport73_suffix_016, ridgeSupport73_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 109
    ridgeSupport73_rest_016 ridgeSupport73_rest_017 ridgeSupport73_rest_021
    ridgeSupport73_016 ridgeSupport73_suffix_017 ridgeSupport73_016_decode ridgeSupport73_suffix_decode_017
theorem ridgeSupport73_suffix_decode_015 : PackedRawNatGrowth.readList 14 173 ridgeSupport73_rest_015 =
    (ridgeSupport73_suffix_015, ridgeSupport73_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 141
    ridgeSupport73_rest_015 ridgeSupport73_rest_016 ridgeSupport73_rest_021
    ridgeSupport73_015 ridgeSupport73_suffix_016 ridgeSupport73_015_decode ridgeSupport73_suffix_decode_016
theorem ridgeSupport73_suffix_decode_014 : PackedRawNatGrowth.readList 14 205 ridgeSupport73_rest_014 =
    (ridgeSupport73_suffix_014, ridgeSupport73_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 173
    ridgeSupport73_rest_014 ridgeSupport73_rest_015 ridgeSupport73_rest_021
    ridgeSupport73_014 ridgeSupport73_suffix_015 ridgeSupport73_014_decode ridgeSupport73_suffix_decode_015
theorem ridgeSupport73_suffix_decode_013 : PackedRawNatGrowth.readList 14 237 ridgeSupport73_rest_013 =
    (ridgeSupport73_suffix_013, ridgeSupport73_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 205
    ridgeSupport73_rest_013 ridgeSupport73_rest_014 ridgeSupport73_rest_021
    ridgeSupport73_013 ridgeSupport73_suffix_014 ridgeSupport73_013_decode ridgeSupport73_suffix_decode_014
theorem ridgeSupport73_suffix_decode_012 : PackedRawNatGrowth.readList 14 269 ridgeSupport73_rest_012 =
    (ridgeSupport73_suffix_012, ridgeSupport73_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 237
    ridgeSupport73_rest_012 ridgeSupport73_rest_013 ridgeSupport73_rest_021
    ridgeSupport73_012 ridgeSupport73_suffix_013 ridgeSupport73_012_decode ridgeSupport73_suffix_decode_013
theorem ridgeSupport73_suffix_decode_011 : PackedRawNatGrowth.readList 14 301 ridgeSupport73_rest_011 =
    (ridgeSupport73_suffix_011, ridgeSupport73_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 269
    ridgeSupport73_rest_011 ridgeSupport73_rest_012 ridgeSupport73_rest_021
    ridgeSupport73_011 ridgeSupport73_suffix_012 ridgeSupport73_011_decode ridgeSupport73_suffix_decode_012
theorem ridgeSupport73_suffix_decode_010 : PackedRawNatGrowth.readList 14 333 ridgeSupport73_rest_010 =
    (ridgeSupport73_suffix_010, ridgeSupport73_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 301
    ridgeSupport73_rest_010 ridgeSupport73_rest_011 ridgeSupport73_rest_021
    ridgeSupport73_010 ridgeSupport73_suffix_011 ridgeSupport73_010_decode ridgeSupport73_suffix_decode_011
theorem ridgeSupport73_suffix_decode_009 : PackedRawNatGrowth.readList 14 365 ridgeSupport73_rest_009 =
    (ridgeSupport73_suffix_009, ridgeSupport73_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 333
    ridgeSupport73_rest_009 ridgeSupport73_rest_010 ridgeSupport73_rest_021
    ridgeSupport73_009 ridgeSupport73_suffix_010 ridgeSupport73_009_decode ridgeSupport73_suffix_decode_010
theorem ridgeSupport73_suffix_decode_008 : PackedRawNatGrowth.readList 14 397 ridgeSupport73_rest_008 =
    (ridgeSupport73_suffix_008, ridgeSupport73_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 365
    ridgeSupport73_rest_008 ridgeSupport73_rest_009 ridgeSupport73_rest_021
    ridgeSupport73_008 ridgeSupport73_suffix_009 ridgeSupport73_008_decode ridgeSupport73_suffix_decode_009
theorem ridgeSupport73_suffix_decode_007 : PackedRawNatGrowth.readList 14 429 ridgeSupport73_rest_007 =
    (ridgeSupport73_suffix_007, ridgeSupport73_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 397
    ridgeSupport73_rest_007 ridgeSupport73_rest_008 ridgeSupport73_rest_021
    ridgeSupport73_007 ridgeSupport73_suffix_008 ridgeSupport73_007_decode ridgeSupport73_suffix_decode_008
theorem ridgeSupport73_suffix_decode_006 : PackedRawNatGrowth.readList 14 461 ridgeSupport73_rest_006 =
    (ridgeSupport73_suffix_006, ridgeSupport73_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 429
    ridgeSupport73_rest_006 ridgeSupport73_rest_007 ridgeSupport73_rest_021
    ridgeSupport73_006 ridgeSupport73_suffix_007 ridgeSupport73_006_decode ridgeSupport73_suffix_decode_007
theorem ridgeSupport73_suffix_decode_005 : PackedRawNatGrowth.readList 14 493 ridgeSupport73_rest_005 =
    (ridgeSupport73_suffix_005, ridgeSupport73_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 461
    ridgeSupport73_rest_005 ridgeSupport73_rest_006 ridgeSupport73_rest_021
    ridgeSupport73_005 ridgeSupport73_suffix_006 ridgeSupport73_005_decode ridgeSupport73_suffix_decode_006
theorem ridgeSupport73_suffix_decode_004 : PackedRawNatGrowth.readList 14 525 ridgeSupport73_rest_004 =
    (ridgeSupport73_suffix_004, ridgeSupport73_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 493
    ridgeSupport73_rest_004 ridgeSupport73_rest_005 ridgeSupport73_rest_021
    ridgeSupport73_004 ridgeSupport73_suffix_005 ridgeSupport73_004_decode ridgeSupport73_suffix_decode_005
theorem ridgeSupport73_suffix_decode_003 : PackedRawNatGrowth.readList 14 557 ridgeSupport73_rest_003 =
    (ridgeSupport73_suffix_003, ridgeSupport73_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 525
    ridgeSupport73_rest_003 ridgeSupport73_rest_004 ridgeSupport73_rest_021
    ridgeSupport73_003 ridgeSupport73_suffix_004 ridgeSupport73_003_decode ridgeSupport73_suffix_decode_004
theorem ridgeSupport73_suffix_decode_002 : PackedRawNatGrowth.readList 14 589 ridgeSupport73_rest_002 =
    (ridgeSupport73_suffix_002, ridgeSupport73_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 557
    ridgeSupport73_rest_002 ridgeSupport73_rest_003 ridgeSupport73_rest_021
    ridgeSupport73_002 ridgeSupport73_suffix_003 ridgeSupport73_002_decode ridgeSupport73_suffix_decode_003
theorem ridgeSupport73_suffix_decode_001 : PackedRawNatGrowth.readList 14 621 ridgeSupport73_rest_001 =
    (ridgeSupport73_suffix_001, ridgeSupport73_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 589
    ridgeSupport73_rest_001 ridgeSupport73_rest_002 ridgeSupport73_rest_021
    ridgeSupport73_001 ridgeSupport73_suffix_002 ridgeSupport73_001_decode ridgeSupport73_suffix_decode_002
theorem ridgeSupport73_suffix_decode_000 : PackedRawNatGrowth.readList 14 653 ridgeSupport73_rest_000 =
    (ridgeSupport73_suffix_000, ridgeSupport73_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 621
    ridgeSupport73_rest_000 ridgeSupport73_rest_001 ridgeSupport73_rest_021
    ridgeSupport73_000 ridgeSupport73_suffix_001 ridgeSupport73_000_decode ridgeSupport73_suffix_decode_001
theorem ridgeSupport73_eq : candidateRows 73 = ridgeSupport73_suffix_000 := by
  rw [ridgeSupport73_source]
  exact congrArg Prod.fst ridgeSupport73_suffix_decode_000
theorem ridgeTest_large_73 : ridgeTest 73 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport73_eq]
    simp only [ridgeSupport73_suffix_000, ridgeSupport73_suffix_001, ridgeSupport73_suffix_002, ridgeSupport73_suffix_003, ridgeSupport73_suffix_004, ridgeSupport73_suffix_005, ridgeSupport73_suffix_006, ridgeSupport73_suffix_007, ridgeSupport73_suffix_008, ridgeSupport73_suffix_009, ridgeSupport73_suffix_010, ridgeSupport73_suffix_011, ridgeSupport73_suffix_012, ridgeSupport73_suffix_013, ridgeSupport73_suffix_014, ridgeSupport73_suffix_015, ridgeSupport73_suffix_016, ridgeSupport73_suffix_017, ridgeSupport73_suffix_018, ridgeSupport73_suffix_019, ridgeSupport73_suffix_020, ridgeSupport73_suffix_021, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport73_000_mask, ridgeSupport73_001_mask, ridgeSupport73_002_mask, ridgeSupport73_003_mask, ridgeSupport73_004_mask, ridgeSupport73_005_mask, ridgeSupport73_006_mask, ridgeSupport73_007_mask, ridgeSupport73_008_mask, ridgeSupport73_009_mask, ridgeSupport73_010_mask, ridgeSupport73_011_mask, ridgeSupport73_012_mask, ridgeSupport73_013_mask, ridgeSupport73_014_mask, ridgeSupport73_015_mask, ridgeSupport73_016_mask, ridgeSupport73_017_mask, ridgeSupport73_018_mask, ridgeSupport73_019_mask, ridgeSupport73_020_mask]
    decide +kernel
  · rw [ridgeSupport73_eq]
    simp only [ridgeSupport73_suffix_000, ridgeSupport73_suffix_001, ridgeSupport73_suffix_002, ridgeSupport73_suffix_003, ridgeSupport73_suffix_004, ridgeSupport73_suffix_005, ridgeSupport73_suffix_006, ridgeSupport73_suffix_007, ridgeSupport73_suffix_008, ridgeSupport73_suffix_009, ridgeSupport73_suffix_010, ridgeSupport73_suffix_011, ridgeSupport73_suffix_012, ridgeSupport73_suffix_013, ridgeSupport73_suffix_014, ridgeSupport73_suffix_015, ridgeSupport73_suffix_016, ridgeSupport73_suffix_017, ridgeSupport73_suffix_018, ridgeSupport73_suffix_019, ridgeSupport73_suffix_020, ridgeSupport73_suffix_021, List.all_append, List.all_nil, ridgeSupport73_000_checked, ridgeSupport73_001_checked, ridgeSupport73_002_checked, ridgeSupport73_003_checked, ridgeSupport73_004_checked, ridgeSupport73_005_checked, ridgeSupport73_006_checked, ridgeSupport73_007_checked, ridgeSupport73_008_checked, ridgeSupport73_009_checked, ridgeSupport73_010_checked, ridgeSupport73_011_checked, ridgeSupport73_012_checked, ridgeSupport73_013_checked, ridgeSupport73_014_checked, ridgeSupport73_015_checked, ridgeSupport73_016_checked, ridgeSupport73_017_checked, ridgeSupport73_018_checked, ridgeSupport73_019_checked, ridgeSupport73_020_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase01
