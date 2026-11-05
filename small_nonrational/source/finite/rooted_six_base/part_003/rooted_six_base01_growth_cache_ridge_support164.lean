module
prelude
public import RootedSixBase01GrowthCacheRidgeSupport164Part000
public import RootedSixBase01GrowthCacheRidgeSupport164Part001
public import RootedSixBase01GrowthCacheRidgeSupport164Part002
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport164_suffix_decode_021 : PackedRawNatGrowth.readList 14 0 ridgeSupport164_rest_021 =
    (ridgeSupport164_suffix_021, ridgeSupport164_rest_021) := by rfl
theorem ridgeSupport164_suffix_decode_020 : PackedRawNatGrowth.readList 14 13 ridgeSupport164_rest_020 =
    (ridgeSupport164_suffix_020, ridgeSupport164_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 13 0
    ridgeSupport164_rest_020 ridgeSupport164_rest_021 ridgeSupport164_rest_021
    ridgeSupport164_020 ridgeSupport164_suffix_021 ridgeSupport164_020_decode ridgeSupport164_suffix_decode_021
theorem ridgeSupport164_suffix_decode_019 : PackedRawNatGrowth.readList 14 45 ridgeSupport164_rest_019 =
    (ridgeSupport164_suffix_019, ridgeSupport164_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 13
    ridgeSupport164_rest_019 ridgeSupport164_rest_020 ridgeSupport164_rest_021
    ridgeSupport164_019 ridgeSupport164_suffix_020 ridgeSupport164_019_decode ridgeSupport164_suffix_decode_020
theorem ridgeSupport164_suffix_decode_018 : PackedRawNatGrowth.readList 14 77 ridgeSupport164_rest_018 =
    (ridgeSupport164_suffix_018, ridgeSupport164_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 45
    ridgeSupport164_rest_018 ridgeSupport164_rest_019 ridgeSupport164_rest_021
    ridgeSupport164_018 ridgeSupport164_suffix_019 ridgeSupport164_018_decode ridgeSupport164_suffix_decode_019
theorem ridgeSupport164_suffix_decode_017 : PackedRawNatGrowth.readList 14 109 ridgeSupport164_rest_017 =
    (ridgeSupport164_suffix_017, ridgeSupport164_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 77
    ridgeSupport164_rest_017 ridgeSupport164_rest_018 ridgeSupport164_rest_021
    ridgeSupport164_017 ridgeSupport164_suffix_018 ridgeSupport164_017_decode ridgeSupport164_suffix_decode_018
theorem ridgeSupport164_suffix_decode_016 : PackedRawNatGrowth.readList 14 141 ridgeSupport164_rest_016 =
    (ridgeSupport164_suffix_016, ridgeSupport164_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 109
    ridgeSupport164_rest_016 ridgeSupport164_rest_017 ridgeSupport164_rest_021
    ridgeSupport164_016 ridgeSupport164_suffix_017 ridgeSupport164_016_decode ridgeSupport164_suffix_decode_017
theorem ridgeSupport164_suffix_decode_015 : PackedRawNatGrowth.readList 14 173 ridgeSupport164_rest_015 =
    (ridgeSupport164_suffix_015, ridgeSupport164_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 141
    ridgeSupport164_rest_015 ridgeSupport164_rest_016 ridgeSupport164_rest_021
    ridgeSupport164_015 ridgeSupport164_suffix_016 ridgeSupport164_015_decode ridgeSupport164_suffix_decode_016
theorem ridgeSupport164_suffix_decode_014 : PackedRawNatGrowth.readList 14 205 ridgeSupport164_rest_014 =
    (ridgeSupport164_suffix_014, ridgeSupport164_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 173
    ridgeSupport164_rest_014 ridgeSupport164_rest_015 ridgeSupport164_rest_021
    ridgeSupport164_014 ridgeSupport164_suffix_015 ridgeSupport164_014_decode ridgeSupport164_suffix_decode_015
theorem ridgeSupport164_suffix_decode_013 : PackedRawNatGrowth.readList 14 237 ridgeSupport164_rest_013 =
    (ridgeSupport164_suffix_013, ridgeSupport164_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 205
    ridgeSupport164_rest_013 ridgeSupport164_rest_014 ridgeSupport164_rest_021
    ridgeSupport164_013 ridgeSupport164_suffix_014 ridgeSupport164_013_decode ridgeSupport164_suffix_decode_014
theorem ridgeSupport164_suffix_decode_012 : PackedRawNatGrowth.readList 14 269 ridgeSupport164_rest_012 =
    (ridgeSupport164_suffix_012, ridgeSupport164_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 237
    ridgeSupport164_rest_012 ridgeSupport164_rest_013 ridgeSupport164_rest_021
    ridgeSupport164_012 ridgeSupport164_suffix_013 ridgeSupport164_012_decode ridgeSupport164_suffix_decode_013
theorem ridgeSupport164_suffix_decode_011 : PackedRawNatGrowth.readList 14 301 ridgeSupport164_rest_011 =
    (ridgeSupport164_suffix_011, ridgeSupport164_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 269
    ridgeSupport164_rest_011 ridgeSupport164_rest_012 ridgeSupport164_rest_021
    ridgeSupport164_011 ridgeSupport164_suffix_012 ridgeSupport164_011_decode ridgeSupport164_suffix_decode_012
theorem ridgeSupport164_suffix_decode_010 : PackedRawNatGrowth.readList 14 333 ridgeSupport164_rest_010 =
    (ridgeSupport164_suffix_010, ridgeSupport164_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 301
    ridgeSupport164_rest_010 ridgeSupport164_rest_011 ridgeSupport164_rest_021
    ridgeSupport164_010 ridgeSupport164_suffix_011 ridgeSupport164_010_decode ridgeSupport164_suffix_decode_011
theorem ridgeSupport164_suffix_decode_009 : PackedRawNatGrowth.readList 14 365 ridgeSupport164_rest_009 =
    (ridgeSupport164_suffix_009, ridgeSupport164_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 333
    ridgeSupport164_rest_009 ridgeSupport164_rest_010 ridgeSupport164_rest_021
    ridgeSupport164_009 ridgeSupport164_suffix_010 ridgeSupport164_009_decode ridgeSupport164_suffix_decode_010
theorem ridgeSupport164_suffix_decode_008 : PackedRawNatGrowth.readList 14 397 ridgeSupport164_rest_008 =
    (ridgeSupport164_suffix_008, ridgeSupport164_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 365
    ridgeSupport164_rest_008 ridgeSupport164_rest_009 ridgeSupport164_rest_021
    ridgeSupport164_008 ridgeSupport164_suffix_009 ridgeSupport164_008_decode ridgeSupport164_suffix_decode_009
theorem ridgeSupport164_suffix_decode_007 : PackedRawNatGrowth.readList 14 429 ridgeSupport164_rest_007 =
    (ridgeSupport164_suffix_007, ridgeSupport164_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 397
    ridgeSupport164_rest_007 ridgeSupport164_rest_008 ridgeSupport164_rest_021
    ridgeSupport164_007 ridgeSupport164_suffix_008 ridgeSupport164_007_decode ridgeSupport164_suffix_decode_008
theorem ridgeSupport164_suffix_decode_006 : PackedRawNatGrowth.readList 14 461 ridgeSupport164_rest_006 =
    (ridgeSupport164_suffix_006, ridgeSupport164_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 429
    ridgeSupport164_rest_006 ridgeSupport164_rest_007 ridgeSupport164_rest_021
    ridgeSupport164_006 ridgeSupport164_suffix_007 ridgeSupport164_006_decode ridgeSupport164_suffix_decode_007
theorem ridgeSupport164_suffix_decode_005 : PackedRawNatGrowth.readList 14 493 ridgeSupport164_rest_005 =
    (ridgeSupport164_suffix_005, ridgeSupport164_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 461
    ridgeSupport164_rest_005 ridgeSupport164_rest_006 ridgeSupport164_rest_021
    ridgeSupport164_005 ridgeSupport164_suffix_006 ridgeSupport164_005_decode ridgeSupport164_suffix_decode_006
theorem ridgeSupport164_suffix_decode_004 : PackedRawNatGrowth.readList 14 525 ridgeSupport164_rest_004 =
    (ridgeSupport164_suffix_004, ridgeSupport164_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 493
    ridgeSupport164_rest_004 ridgeSupport164_rest_005 ridgeSupport164_rest_021
    ridgeSupport164_004 ridgeSupport164_suffix_005 ridgeSupport164_004_decode ridgeSupport164_suffix_decode_005
theorem ridgeSupport164_suffix_decode_003 : PackedRawNatGrowth.readList 14 557 ridgeSupport164_rest_003 =
    (ridgeSupport164_suffix_003, ridgeSupport164_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 525
    ridgeSupport164_rest_003 ridgeSupport164_rest_004 ridgeSupport164_rest_021
    ridgeSupport164_003 ridgeSupport164_suffix_004 ridgeSupport164_003_decode ridgeSupport164_suffix_decode_004
theorem ridgeSupport164_suffix_decode_002 : PackedRawNatGrowth.readList 14 589 ridgeSupport164_rest_002 =
    (ridgeSupport164_suffix_002, ridgeSupport164_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 557
    ridgeSupport164_rest_002 ridgeSupport164_rest_003 ridgeSupport164_rest_021
    ridgeSupport164_002 ridgeSupport164_suffix_003 ridgeSupport164_002_decode ridgeSupport164_suffix_decode_003
theorem ridgeSupport164_suffix_decode_001 : PackedRawNatGrowth.readList 14 621 ridgeSupport164_rest_001 =
    (ridgeSupport164_suffix_001, ridgeSupport164_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 589
    ridgeSupport164_rest_001 ridgeSupport164_rest_002 ridgeSupport164_rest_021
    ridgeSupport164_001 ridgeSupport164_suffix_002 ridgeSupport164_001_decode ridgeSupport164_suffix_decode_002
theorem ridgeSupport164_suffix_decode_000 : PackedRawNatGrowth.readList 14 653 ridgeSupport164_rest_000 =
    (ridgeSupport164_suffix_000, ridgeSupport164_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 621
    ridgeSupport164_rest_000 ridgeSupport164_rest_001 ridgeSupport164_rest_021
    ridgeSupport164_000 ridgeSupport164_suffix_001 ridgeSupport164_000_decode ridgeSupport164_suffix_decode_001
theorem ridgeSupport164_eq : candidateRows 164 = ridgeSupport164_suffix_000 := by
  rw [ridgeSupport164_source]
  exact congrArg Prod.fst ridgeSupport164_suffix_decode_000
theorem ridgeTest_large_164 : ridgeTest 164 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport164_eq]
    simp only [ridgeSupport164_suffix_000, ridgeSupport164_suffix_001, ridgeSupport164_suffix_002, ridgeSupport164_suffix_003, ridgeSupport164_suffix_004, ridgeSupport164_suffix_005, ridgeSupport164_suffix_006, ridgeSupport164_suffix_007, ridgeSupport164_suffix_008, ridgeSupport164_suffix_009, ridgeSupport164_suffix_010, ridgeSupport164_suffix_011, ridgeSupport164_suffix_012, ridgeSupport164_suffix_013, ridgeSupport164_suffix_014, ridgeSupport164_suffix_015, ridgeSupport164_suffix_016, ridgeSupport164_suffix_017, ridgeSupport164_suffix_018, ridgeSupport164_suffix_019, ridgeSupport164_suffix_020, ridgeSupport164_suffix_021, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport164_000_mask, ridgeSupport164_001_mask, ridgeSupport164_002_mask, ridgeSupport164_003_mask, ridgeSupport164_004_mask, ridgeSupport164_005_mask, ridgeSupport164_006_mask, ridgeSupport164_007_mask, ridgeSupport164_008_mask, ridgeSupport164_009_mask, ridgeSupport164_010_mask, ridgeSupport164_011_mask, ridgeSupport164_012_mask, ridgeSupport164_013_mask, ridgeSupport164_014_mask, ridgeSupport164_015_mask, ridgeSupport164_016_mask, ridgeSupport164_017_mask, ridgeSupport164_018_mask, ridgeSupport164_019_mask, ridgeSupport164_020_mask]
    decide +kernel
  · rw [ridgeSupport164_eq]
    simp only [ridgeSupport164_suffix_000, ridgeSupport164_suffix_001, ridgeSupport164_suffix_002, ridgeSupport164_suffix_003, ridgeSupport164_suffix_004, ridgeSupport164_suffix_005, ridgeSupport164_suffix_006, ridgeSupport164_suffix_007, ridgeSupport164_suffix_008, ridgeSupport164_suffix_009, ridgeSupport164_suffix_010, ridgeSupport164_suffix_011, ridgeSupport164_suffix_012, ridgeSupport164_suffix_013, ridgeSupport164_suffix_014, ridgeSupport164_suffix_015, ridgeSupport164_suffix_016, ridgeSupport164_suffix_017, ridgeSupport164_suffix_018, ridgeSupport164_suffix_019, ridgeSupport164_suffix_020, ridgeSupport164_suffix_021, List.all_append, List.all_nil, ridgeSupport164_000_checked, ridgeSupport164_001_checked, ridgeSupport164_002_checked, ridgeSupport164_003_checked, ridgeSupport164_004_checked, ridgeSupport164_005_checked, ridgeSupport164_006_checked, ridgeSupport164_007_checked, ridgeSupport164_008_checked, ridgeSupport164_009_checked, ridgeSupport164_010_checked, ridgeSupport164_011_checked, ridgeSupport164_012_checked, ridgeSupport164_013_checked, ridgeSupport164_014_checked, ridgeSupport164_015_checked, ridgeSupport164_016_checked, ridgeSupport164_017_checked, ridgeSupport164_018_checked, ridgeSupport164_019_checked, ridgeSupport164_020_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase01
