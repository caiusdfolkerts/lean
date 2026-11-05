module
prelude
public import RootedSixBase01GrowthCacheRidgeSupport137Part000
public import RootedSixBase01GrowthCacheRidgeSupport137Part001
public import RootedSixBase01GrowthCacheRidgeSupport137Part002
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport137_suffix_decode_021 : PackedRawNatGrowth.readList 14 0 ridgeSupport137_rest_021 =
    (ridgeSupport137_suffix_021, ridgeSupport137_rest_021) := by rfl
theorem ridgeSupport137_suffix_decode_020 : PackedRawNatGrowth.readList 14 13 ridgeSupport137_rest_020 =
    (ridgeSupport137_suffix_020, ridgeSupport137_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 13 0
    ridgeSupport137_rest_020 ridgeSupport137_rest_021 ridgeSupport137_rest_021
    ridgeSupport137_020 ridgeSupport137_suffix_021 ridgeSupport137_020_decode ridgeSupport137_suffix_decode_021
theorem ridgeSupport137_suffix_decode_019 : PackedRawNatGrowth.readList 14 45 ridgeSupport137_rest_019 =
    (ridgeSupport137_suffix_019, ridgeSupport137_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 13
    ridgeSupport137_rest_019 ridgeSupport137_rest_020 ridgeSupport137_rest_021
    ridgeSupport137_019 ridgeSupport137_suffix_020 ridgeSupport137_019_decode ridgeSupport137_suffix_decode_020
theorem ridgeSupport137_suffix_decode_018 : PackedRawNatGrowth.readList 14 77 ridgeSupport137_rest_018 =
    (ridgeSupport137_suffix_018, ridgeSupport137_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 45
    ridgeSupport137_rest_018 ridgeSupport137_rest_019 ridgeSupport137_rest_021
    ridgeSupport137_018 ridgeSupport137_suffix_019 ridgeSupport137_018_decode ridgeSupport137_suffix_decode_019
theorem ridgeSupport137_suffix_decode_017 : PackedRawNatGrowth.readList 14 109 ridgeSupport137_rest_017 =
    (ridgeSupport137_suffix_017, ridgeSupport137_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 77
    ridgeSupport137_rest_017 ridgeSupport137_rest_018 ridgeSupport137_rest_021
    ridgeSupport137_017 ridgeSupport137_suffix_018 ridgeSupport137_017_decode ridgeSupport137_suffix_decode_018
theorem ridgeSupport137_suffix_decode_016 : PackedRawNatGrowth.readList 14 141 ridgeSupport137_rest_016 =
    (ridgeSupport137_suffix_016, ridgeSupport137_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 109
    ridgeSupport137_rest_016 ridgeSupport137_rest_017 ridgeSupport137_rest_021
    ridgeSupport137_016 ridgeSupport137_suffix_017 ridgeSupport137_016_decode ridgeSupport137_suffix_decode_017
theorem ridgeSupport137_suffix_decode_015 : PackedRawNatGrowth.readList 14 173 ridgeSupport137_rest_015 =
    (ridgeSupport137_suffix_015, ridgeSupport137_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 141
    ridgeSupport137_rest_015 ridgeSupport137_rest_016 ridgeSupport137_rest_021
    ridgeSupport137_015 ridgeSupport137_suffix_016 ridgeSupport137_015_decode ridgeSupport137_suffix_decode_016
theorem ridgeSupport137_suffix_decode_014 : PackedRawNatGrowth.readList 14 205 ridgeSupport137_rest_014 =
    (ridgeSupport137_suffix_014, ridgeSupport137_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 173
    ridgeSupport137_rest_014 ridgeSupport137_rest_015 ridgeSupport137_rest_021
    ridgeSupport137_014 ridgeSupport137_suffix_015 ridgeSupport137_014_decode ridgeSupport137_suffix_decode_015
theorem ridgeSupport137_suffix_decode_013 : PackedRawNatGrowth.readList 14 237 ridgeSupport137_rest_013 =
    (ridgeSupport137_suffix_013, ridgeSupport137_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 205
    ridgeSupport137_rest_013 ridgeSupport137_rest_014 ridgeSupport137_rest_021
    ridgeSupport137_013 ridgeSupport137_suffix_014 ridgeSupport137_013_decode ridgeSupport137_suffix_decode_014
theorem ridgeSupport137_suffix_decode_012 : PackedRawNatGrowth.readList 14 269 ridgeSupport137_rest_012 =
    (ridgeSupport137_suffix_012, ridgeSupport137_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 237
    ridgeSupport137_rest_012 ridgeSupport137_rest_013 ridgeSupport137_rest_021
    ridgeSupport137_012 ridgeSupport137_suffix_013 ridgeSupport137_012_decode ridgeSupport137_suffix_decode_013
theorem ridgeSupport137_suffix_decode_011 : PackedRawNatGrowth.readList 14 301 ridgeSupport137_rest_011 =
    (ridgeSupport137_suffix_011, ridgeSupport137_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 269
    ridgeSupport137_rest_011 ridgeSupport137_rest_012 ridgeSupport137_rest_021
    ridgeSupport137_011 ridgeSupport137_suffix_012 ridgeSupport137_011_decode ridgeSupport137_suffix_decode_012
theorem ridgeSupport137_suffix_decode_010 : PackedRawNatGrowth.readList 14 333 ridgeSupport137_rest_010 =
    (ridgeSupport137_suffix_010, ridgeSupport137_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 301
    ridgeSupport137_rest_010 ridgeSupport137_rest_011 ridgeSupport137_rest_021
    ridgeSupport137_010 ridgeSupport137_suffix_011 ridgeSupport137_010_decode ridgeSupport137_suffix_decode_011
theorem ridgeSupport137_suffix_decode_009 : PackedRawNatGrowth.readList 14 365 ridgeSupport137_rest_009 =
    (ridgeSupport137_suffix_009, ridgeSupport137_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 333
    ridgeSupport137_rest_009 ridgeSupport137_rest_010 ridgeSupport137_rest_021
    ridgeSupport137_009 ridgeSupport137_suffix_010 ridgeSupport137_009_decode ridgeSupport137_suffix_decode_010
theorem ridgeSupport137_suffix_decode_008 : PackedRawNatGrowth.readList 14 397 ridgeSupport137_rest_008 =
    (ridgeSupport137_suffix_008, ridgeSupport137_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 365
    ridgeSupport137_rest_008 ridgeSupport137_rest_009 ridgeSupport137_rest_021
    ridgeSupport137_008 ridgeSupport137_suffix_009 ridgeSupport137_008_decode ridgeSupport137_suffix_decode_009
theorem ridgeSupport137_suffix_decode_007 : PackedRawNatGrowth.readList 14 429 ridgeSupport137_rest_007 =
    (ridgeSupport137_suffix_007, ridgeSupport137_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 397
    ridgeSupport137_rest_007 ridgeSupport137_rest_008 ridgeSupport137_rest_021
    ridgeSupport137_007 ridgeSupport137_suffix_008 ridgeSupport137_007_decode ridgeSupport137_suffix_decode_008
theorem ridgeSupport137_suffix_decode_006 : PackedRawNatGrowth.readList 14 461 ridgeSupport137_rest_006 =
    (ridgeSupport137_suffix_006, ridgeSupport137_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 429
    ridgeSupport137_rest_006 ridgeSupport137_rest_007 ridgeSupport137_rest_021
    ridgeSupport137_006 ridgeSupport137_suffix_007 ridgeSupport137_006_decode ridgeSupport137_suffix_decode_007
theorem ridgeSupport137_suffix_decode_005 : PackedRawNatGrowth.readList 14 493 ridgeSupport137_rest_005 =
    (ridgeSupport137_suffix_005, ridgeSupport137_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 461
    ridgeSupport137_rest_005 ridgeSupport137_rest_006 ridgeSupport137_rest_021
    ridgeSupport137_005 ridgeSupport137_suffix_006 ridgeSupport137_005_decode ridgeSupport137_suffix_decode_006
theorem ridgeSupport137_suffix_decode_004 : PackedRawNatGrowth.readList 14 525 ridgeSupport137_rest_004 =
    (ridgeSupport137_suffix_004, ridgeSupport137_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 493
    ridgeSupport137_rest_004 ridgeSupport137_rest_005 ridgeSupport137_rest_021
    ridgeSupport137_004 ridgeSupport137_suffix_005 ridgeSupport137_004_decode ridgeSupport137_suffix_decode_005
theorem ridgeSupport137_suffix_decode_003 : PackedRawNatGrowth.readList 14 557 ridgeSupport137_rest_003 =
    (ridgeSupport137_suffix_003, ridgeSupport137_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 525
    ridgeSupport137_rest_003 ridgeSupport137_rest_004 ridgeSupport137_rest_021
    ridgeSupport137_003 ridgeSupport137_suffix_004 ridgeSupport137_003_decode ridgeSupport137_suffix_decode_004
theorem ridgeSupport137_suffix_decode_002 : PackedRawNatGrowth.readList 14 589 ridgeSupport137_rest_002 =
    (ridgeSupport137_suffix_002, ridgeSupport137_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 557
    ridgeSupport137_rest_002 ridgeSupport137_rest_003 ridgeSupport137_rest_021
    ridgeSupport137_002 ridgeSupport137_suffix_003 ridgeSupport137_002_decode ridgeSupport137_suffix_decode_003
theorem ridgeSupport137_suffix_decode_001 : PackedRawNatGrowth.readList 14 621 ridgeSupport137_rest_001 =
    (ridgeSupport137_suffix_001, ridgeSupport137_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 589
    ridgeSupport137_rest_001 ridgeSupport137_rest_002 ridgeSupport137_rest_021
    ridgeSupport137_001 ridgeSupport137_suffix_002 ridgeSupport137_001_decode ridgeSupport137_suffix_decode_002
theorem ridgeSupport137_suffix_decode_000 : PackedRawNatGrowth.readList 14 653 ridgeSupport137_rest_000 =
    (ridgeSupport137_suffix_000, ridgeSupport137_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 621
    ridgeSupport137_rest_000 ridgeSupport137_rest_001 ridgeSupport137_rest_021
    ridgeSupport137_000 ridgeSupport137_suffix_001 ridgeSupport137_000_decode ridgeSupport137_suffix_decode_001
theorem ridgeSupport137_eq : candidateRows 137 = ridgeSupport137_suffix_000 := by
  rw [ridgeSupport137_source]
  exact congrArg Prod.fst ridgeSupport137_suffix_decode_000
theorem ridgeTest_large_137 : ridgeTest 137 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport137_eq]
    simp only [ridgeSupport137_suffix_000, ridgeSupport137_suffix_001, ridgeSupport137_suffix_002, ridgeSupport137_suffix_003, ridgeSupport137_suffix_004, ridgeSupport137_suffix_005, ridgeSupport137_suffix_006, ridgeSupport137_suffix_007, ridgeSupport137_suffix_008, ridgeSupport137_suffix_009, ridgeSupport137_suffix_010, ridgeSupport137_suffix_011, ridgeSupport137_suffix_012, ridgeSupport137_suffix_013, ridgeSupport137_suffix_014, ridgeSupport137_suffix_015, ridgeSupport137_suffix_016, ridgeSupport137_suffix_017, ridgeSupport137_suffix_018, ridgeSupport137_suffix_019, ridgeSupport137_suffix_020, ridgeSupport137_suffix_021, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport137_000_mask, ridgeSupport137_001_mask, ridgeSupport137_002_mask, ridgeSupport137_003_mask, ridgeSupport137_004_mask, ridgeSupport137_005_mask, ridgeSupport137_006_mask, ridgeSupport137_007_mask, ridgeSupport137_008_mask, ridgeSupport137_009_mask, ridgeSupport137_010_mask, ridgeSupport137_011_mask, ridgeSupport137_012_mask, ridgeSupport137_013_mask, ridgeSupport137_014_mask, ridgeSupport137_015_mask, ridgeSupport137_016_mask, ridgeSupport137_017_mask, ridgeSupport137_018_mask, ridgeSupport137_019_mask, ridgeSupport137_020_mask]
    decide +kernel
  · rw [ridgeSupport137_eq]
    simp only [ridgeSupport137_suffix_000, ridgeSupport137_suffix_001, ridgeSupport137_suffix_002, ridgeSupport137_suffix_003, ridgeSupport137_suffix_004, ridgeSupport137_suffix_005, ridgeSupport137_suffix_006, ridgeSupport137_suffix_007, ridgeSupport137_suffix_008, ridgeSupport137_suffix_009, ridgeSupport137_suffix_010, ridgeSupport137_suffix_011, ridgeSupport137_suffix_012, ridgeSupport137_suffix_013, ridgeSupport137_suffix_014, ridgeSupport137_suffix_015, ridgeSupport137_suffix_016, ridgeSupport137_suffix_017, ridgeSupport137_suffix_018, ridgeSupport137_suffix_019, ridgeSupport137_suffix_020, ridgeSupport137_suffix_021, List.all_append, List.all_nil, ridgeSupport137_000_checked, ridgeSupport137_001_checked, ridgeSupport137_002_checked, ridgeSupport137_003_checked, ridgeSupport137_004_checked, ridgeSupport137_005_checked, ridgeSupport137_006_checked, ridgeSupport137_007_checked, ridgeSupport137_008_checked, ridgeSupport137_009_checked, ridgeSupport137_010_checked, ridgeSupport137_011_checked, ridgeSupport137_012_checked, ridgeSupport137_013_checked, ridgeSupport137_014_checked, ridgeSupport137_015_checked, ridgeSupport137_016_checked, ridgeSupport137_017_checked, ridgeSupport137_018_checked, ridgeSupport137_019_checked, ridgeSupport137_020_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase01
