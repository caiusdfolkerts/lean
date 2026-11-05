module
prelude
public import RootedSixBase01GrowthCacheRidgeSupport131Part000
public import RootedSixBase01GrowthCacheRidgeSupport131Part001
public import RootedSixBase01GrowthCacheRidgeSupport131Part002
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport131_suffix_decode_021 : PackedRawNatGrowth.readList 14 0 ridgeSupport131_rest_021 =
    (ridgeSupport131_suffix_021, ridgeSupport131_rest_021) := by rfl
theorem ridgeSupport131_suffix_decode_020 : PackedRawNatGrowth.readList 14 13 ridgeSupport131_rest_020 =
    (ridgeSupport131_suffix_020, ridgeSupport131_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 13 0
    ridgeSupport131_rest_020 ridgeSupport131_rest_021 ridgeSupport131_rest_021
    ridgeSupport131_020 ridgeSupport131_suffix_021 ridgeSupport131_020_decode ridgeSupport131_suffix_decode_021
theorem ridgeSupport131_suffix_decode_019 : PackedRawNatGrowth.readList 14 45 ridgeSupport131_rest_019 =
    (ridgeSupport131_suffix_019, ridgeSupport131_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 13
    ridgeSupport131_rest_019 ridgeSupport131_rest_020 ridgeSupport131_rest_021
    ridgeSupport131_019 ridgeSupport131_suffix_020 ridgeSupport131_019_decode ridgeSupport131_suffix_decode_020
theorem ridgeSupport131_suffix_decode_018 : PackedRawNatGrowth.readList 14 77 ridgeSupport131_rest_018 =
    (ridgeSupport131_suffix_018, ridgeSupport131_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 45
    ridgeSupport131_rest_018 ridgeSupport131_rest_019 ridgeSupport131_rest_021
    ridgeSupport131_018 ridgeSupport131_suffix_019 ridgeSupport131_018_decode ridgeSupport131_suffix_decode_019
theorem ridgeSupport131_suffix_decode_017 : PackedRawNatGrowth.readList 14 109 ridgeSupport131_rest_017 =
    (ridgeSupport131_suffix_017, ridgeSupport131_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 77
    ridgeSupport131_rest_017 ridgeSupport131_rest_018 ridgeSupport131_rest_021
    ridgeSupport131_017 ridgeSupport131_suffix_018 ridgeSupport131_017_decode ridgeSupport131_suffix_decode_018
theorem ridgeSupport131_suffix_decode_016 : PackedRawNatGrowth.readList 14 141 ridgeSupport131_rest_016 =
    (ridgeSupport131_suffix_016, ridgeSupport131_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 109
    ridgeSupport131_rest_016 ridgeSupport131_rest_017 ridgeSupport131_rest_021
    ridgeSupport131_016 ridgeSupport131_suffix_017 ridgeSupport131_016_decode ridgeSupport131_suffix_decode_017
theorem ridgeSupport131_suffix_decode_015 : PackedRawNatGrowth.readList 14 173 ridgeSupport131_rest_015 =
    (ridgeSupport131_suffix_015, ridgeSupport131_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 141
    ridgeSupport131_rest_015 ridgeSupport131_rest_016 ridgeSupport131_rest_021
    ridgeSupport131_015 ridgeSupport131_suffix_016 ridgeSupport131_015_decode ridgeSupport131_suffix_decode_016
theorem ridgeSupport131_suffix_decode_014 : PackedRawNatGrowth.readList 14 205 ridgeSupport131_rest_014 =
    (ridgeSupport131_suffix_014, ridgeSupport131_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 173
    ridgeSupport131_rest_014 ridgeSupport131_rest_015 ridgeSupport131_rest_021
    ridgeSupport131_014 ridgeSupport131_suffix_015 ridgeSupport131_014_decode ridgeSupport131_suffix_decode_015
theorem ridgeSupport131_suffix_decode_013 : PackedRawNatGrowth.readList 14 237 ridgeSupport131_rest_013 =
    (ridgeSupport131_suffix_013, ridgeSupport131_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 205
    ridgeSupport131_rest_013 ridgeSupport131_rest_014 ridgeSupport131_rest_021
    ridgeSupport131_013 ridgeSupport131_suffix_014 ridgeSupport131_013_decode ridgeSupport131_suffix_decode_014
theorem ridgeSupport131_suffix_decode_012 : PackedRawNatGrowth.readList 14 269 ridgeSupport131_rest_012 =
    (ridgeSupport131_suffix_012, ridgeSupport131_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 237
    ridgeSupport131_rest_012 ridgeSupport131_rest_013 ridgeSupport131_rest_021
    ridgeSupport131_012 ridgeSupport131_suffix_013 ridgeSupport131_012_decode ridgeSupport131_suffix_decode_013
theorem ridgeSupport131_suffix_decode_011 : PackedRawNatGrowth.readList 14 301 ridgeSupport131_rest_011 =
    (ridgeSupport131_suffix_011, ridgeSupport131_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 269
    ridgeSupport131_rest_011 ridgeSupport131_rest_012 ridgeSupport131_rest_021
    ridgeSupport131_011 ridgeSupport131_suffix_012 ridgeSupport131_011_decode ridgeSupport131_suffix_decode_012
theorem ridgeSupport131_suffix_decode_010 : PackedRawNatGrowth.readList 14 333 ridgeSupport131_rest_010 =
    (ridgeSupport131_suffix_010, ridgeSupport131_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 301
    ridgeSupport131_rest_010 ridgeSupport131_rest_011 ridgeSupport131_rest_021
    ridgeSupport131_010 ridgeSupport131_suffix_011 ridgeSupport131_010_decode ridgeSupport131_suffix_decode_011
theorem ridgeSupport131_suffix_decode_009 : PackedRawNatGrowth.readList 14 365 ridgeSupport131_rest_009 =
    (ridgeSupport131_suffix_009, ridgeSupport131_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 333
    ridgeSupport131_rest_009 ridgeSupport131_rest_010 ridgeSupport131_rest_021
    ridgeSupport131_009 ridgeSupport131_suffix_010 ridgeSupport131_009_decode ridgeSupport131_suffix_decode_010
theorem ridgeSupport131_suffix_decode_008 : PackedRawNatGrowth.readList 14 397 ridgeSupport131_rest_008 =
    (ridgeSupport131_suffix_008, ridgeSupport131_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 365
    ridgeSupport131_rest_008 ridgeSupport131_rest_009 ridgeSupport131_rest_021
    ridgeSupport131_008 ridgeSupport131_suffix_009 ridgeSupport131_008_decode ridgeSupport131_suffix_decode_009
theorem ridgeSupport131_suffix_decode_007 : PackedRawNatGrowth.readList 14 429 ridgeSupport131_rest_007 =
    (ridgeSupport131_suffix_007, ridgeSupport131_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 397
    ridgeSupport131_rest_007 ridgeSupport131_rest_008 ridgeSupport131_rest_021
    ridgeSupport131_007 ridgeSupport131_suffix_008 ridgeSupport131_007_decode ridgeSupport131_suffix_decode_008
theorem ridgeSupport131_suffix_decode_006 : PackedRawNatGrowth.readList 14 461 ridgeSupport131_rest_006 =
    (ridgeSupport131_suffix_006, ridgeSupport131_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 429
    ridgeSupport131_rest_006 ridgeSupport131_rest_007 ridgeSupport131_rest_021
    ridgeSupport131_006 ridgeSupport131_suffix_007 ridgeSupport131_006_decode ridgeSupport131_suffix_decode_007
theorem ridgeSupport131_suffix_decode_005 : PackedRawNatGrowth.readList 14 493 ridgeSupport131_rest_005 =
    (ridgeSupport131_suffix_005, ridgeSupport131_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 461
    ridgeSupport131_rest_005 ridgeSupport131_rest_006 ridgeSupport131_rest_021
    ridgeSupport131_005 ridgeSupport131_suffix_006 ridgeSupport131_005_decode ridgeSupport131_suffix_decode_006
theorem ridgeSupport131_suffix_decode_004 : PackedRawNatGrowth.readList 14 525 ridgeSupport131_rest_004 =
    (ridgeSupport131_suffix_004, ridgeSupport131_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 493
    ridgeSupport131_rest_004 ridgeSupport131_rest_005 ridgeSupport131_rest_021
    ridgeSupport131_004 ridgeSupport131_suffix_005 ridgeSupport131_004_decode ridgeSupport131_suffix_decode_005
theorem ridgeSupport131_suffix_decode_003 : PackedRawNatGrowth.readList 14 557 ridgeSupport131_rest_003 =
    (ridgeSupport131_suffix_003, ridgeSupport131_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 525
    ridgeSupport131_rest_003 ridgeSupport131_rest_004 ridgeSupport131_rest_021
    ridgeSupport131_003 ridgeSupport131_suffix_004 ridgeSupport131_003_decode ridgeSupport131_suffix_decode_004
theorem ridgeSupport131_suffix_decode_002 : PackedRawNatGrowth.readList 14 589 ridgeSupport131_rest_002 =
    (ridgeSupport131_suffix_002, ridgeSupport131_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 557
    ridgeSupport131_rest_002 ridgeSupport131_rest_003 ridgeSupport131_rest_021
    ridgeSupport131_002 ridgeSupport131_suffix_003 ridgeSupport131_002_decode ridgeSupport131_suffix_decode_003
theorem ridgeSupport131_suffix_decode_001 : PackedRawNatGrowth.readList 14 621 ridgeSupport131_rest_001 =
    (ridgeSupport131_suffix_001, ridgeSupport131_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 589
    ridgeSupport131_rest_001 ridgeSupport131_rest_002 ridgeSupport131_rest_021
    ridgeSupport131_001 ridgeSupport131_suffix_002 ridgeSupport131_001_decode ridgeSupport131_suffix_decode_002
theorem ridgeSupport131_suffix_decode_000 : PackedRawNatGrowth.readList 14 653 ridgeSupport131_rest_000 =
    (ridgeSupport131_suffix_000, ridgeSupport131_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 621
    ridgeSupport131_rest_000 ridgeSupport131_rest_001 ridgeSupport131_rest_021
    ridgeSupport131_000 ridgeSupport131_suffix_001 ridgeSupport131_000_decode ridgeSupport131_suffix_decode_001
theorem ridgeSupport131_eq : candidateRows 131 = ridgeSupport131_suffix_000 := by
  rw [ridgeSupport131_source]
  exact congrArg Prod.fst ridgeSupport131_suffix_decode_000
theorem ridgeTest_large_131 : ridgeTest 131 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport131_eq]
    simp only [ridgeSupport131_suffix_000, ridgeSupport131_suffix_001, ridgeSupport131_suffix_002, ridgeSupport131_suffix_003, ridgeSupport131_suffix_004, ridgeSupport131_suffix_005, ridgeSupport131_suffix_006, ridgeSupport131_suffix_007, ridgeSupport131_suffix_008, ridgeSupport131_suffix_009, ridgeSupport131_suffix_010, ridgeSupport131_suffix_011, ridgeSupport131_suffix_012, ridgeSupport131_suffix_013, ridgeSupport131_suffix_014, ridgeSupport131_suffix_015, ridgeSupport131_suffix_016, ridgeSupport131_suffix_017, ridgeSupport131_suffix_018, ridgeSupport131_suffix_019, ridgeSupport131_suffix_020, ridgeSupport131_suffix_021, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport131_000_mask, ridgeSupport131_001_mask, ridgeSupport131_002_mask, ridgeSupport131_003_mask, ridgeSupport131_004_mask, ridgeSupport131_005_mask, ridgeSupport131_006_mask, ridgeSupport131_007_mask, ridgeSupport131_008_mask, ridgeSupport131_009_mask, ridgeSupport131_010_mask, ridgeSupport131_011_mask, ridgeSupport131_012_mask, ridgeSupport131_013_mask, ridgeSupport131_014_mask, ridgeSupport131_015_mask, ridgeSupport131_016_mask, ridgeSupport131_017_mask, ridgeSupport131_018_mask, ridgeSupport131_019_mask, ridgeSupport131_020_mask]
    decide +kernel
  · rw [ridgeSupport131_eq]
    simp only [ridgeSupport131_suffix_000, ridgeSupport131_suffix_001, ridgeSupport131_suffix_002, ridgeSupport131_suffix_003, ridgeSupport131_suffix_004, ridgeSupport131_suffix_005, ridgeSupport131_suffix_006, ridgeSupport131_suffix_007, ridgeSupport131_suffix_008, ridgeSupport131_suffix_009, ridgeSupport131_suffix_010, ridgeSupport131_suffix_011, ridgeSupport131_suffix_012, ridgeSupport131_suffix_013, ridgeSupport131_suffix_014, ridgeSupport131_suffix_015, ridgeSupport131_suffix_016, ridgeSupport131_suffix_017, ridgeSupport131_suffix_018, ridgeSupport131_suffix_019, ridgeSupport131_suffix_020, ridgeSupport131_suffix_021, List.all_append, List.all_nil, ridgeSupport131_000_checked, ridgeSupport131_001_checked, ridgeSupport131_002_checked, ridgeSupport131_003_checked, ridgeSupport131_004_checked, ridgeSupport131_005_checked, ridgeSupport131_006_checked, ridgeSupport131_007_checked, ridgeSupport131_008_checked, ridgeSupport131_009_checked, ridgeSupport131_010_checked, ridgeSupport131_011_checked, ridgeSupport131_012_checked, ridgeSupport131_013_checked, ridgeSupport131_014_checked, ridgeSupport131_015_checked, ridgeSupport131_016_checked, ridgeSupport131_017_checked, ridgeSupport131_018_checked, ridgeSupport131_019_checked, ridgeSupport131_020_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase01
