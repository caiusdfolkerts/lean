module
prelude
public import RootedSixBase01GrowthCacheRidgeSupport148Part000
public import RootedSixBase01GrowthCacheRidgeSupport148Part001
public import RootedSixBase01GrowthCacheRidgeSupport148Part002
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport148_suffix_decode_021 : PackedRawNatGrowth.readList 14 0 ridgeSupport148_rest_021 =
    (ridgeSupport148_suffix_021, ridgeSupport148_rest_021) := by rfl
theorem ridgeSupport148_suffix_decode_020 : PackedRawNatGrowth.readList 14 13 ridgeSupport148_rest_020 =
    (ridgeSupport148_suffix_020, ridgeSupport148_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 13 0
    ridgeSupport148_rest_020 ridgeSupport148_rest_021 ridgeSupport148_rest_021
    ridgeSupport148_020 ridgeSupport148_suffix_021 ridgeSupport148_020_decode ridgeSupport148_suffix_decode_021
theorem ridgeSupport148_suffix_decode_019 : PackedRawNatGrowth.readList 14 45 ridgeSupport148_rest_019 =
    (ridgeSupport148_suffix_019, ridgeSupport148_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 13
    ridgeSupport148_rest_019 ridgeSupport148_rest_020 ridgeSupport148_rest_021
    ridgeSupport148_019 ridgeSupport148_suffix_020 ridgeSupport148_019_decode ridgeSupport148_suffix_decode_020
theorem ridgeSupport148_suffix_decode_018 : PackedRawNatGrowth.readList 14 77 ridgeSupport148_rest_018 =
    (ridgeSupport148_suffix_018, ridgeSupport148_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 45
    ridgeSupport148_rest_018 ridgeSupport148_rest_019 ridgeSupport148_rest_021
    ridgeSupport148_018 ridgeSupport148_suffix_019 ridgeSupport148_018_decode ridgeSupport148_suffix_decode_019
theorem ridgeSupport148_suffix_decode_017 : PackedRawNatGrowth.readList 14 109 ridgeSupport148_rest_017 =
    (ridgeSupport148_suffix_017, ridgeSupport148_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 77
    ridgeSupport148_rest_017 ridgeSupport148_rest_018 ridgeSupport148_rest_021
    ridgeSupport148_017 ridgeSupport148_suffix_018 ridgeSupport148_017_decode ridgeSupport148_suffix_decode_018
theorem ridgeSupport148_suffix_decode_016 : PackedRawNatGrowth.readList 14 141 ridgeSupport148_rest_016 =
    (ridgeSupport148_suffix_016, ridgeSupport148_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 109
    ridgeSupport148_rest_016 ridgeSupport148_rest_017 ridgeSupport148_rest_021
    ridgeSupport148_016 ridgeSupport148_suffix_017 ridgeSupport148_016_decode ridgeSupport148_suffix_decode_017
theorem ridgeSupport148_suffix_decode_015 : PackedRawNatGrowth.readList 14 173 ridgeSupport148_rest_015 =
    (ridgeSupport148_suffix_015, ridgeSupport148_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 141
    ridgeSupport148_rest_015 ridgeSupport148_rest_016 ridgeSupport148_rest_021
    ridgeSupport148_015 ridgeSupport148_suffix_016 ridgeSupport148_015_decode ridgeSupport148_suffix_decode_016
theorem ridgeSupport148_suffix_decode_014 : PackedRawNatGrowth.readList 14 205 ridgeSupport148_rest_014 =
    (ridgeSupport148_suffix_014, ridgeSupport148_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 173
    ridgeSupport148_rest_014 ridgeSupport148_rest_015 ridgeSupport148_rest_021
    ridgeSupport148_014 ridgeSupport148_suffix_015 ridgeSupport148_014_decode ridgeSupport148_suffix_decode_015
theorem ridgeSupport148_suffix_decode_013 : PackedRawNatGrowth.readList 14 237 ridgeSupport148_rest_013 =
    (ridgeSupport148_suffix_013, ridgeSupport148_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 205
    ridgeSupport148_rest_013 ridgeSupport148_rest_014 ridgeSupport148_rest_021
    ridgeSupport148_013 ridgeSupport148_suffix_014 ridgeSupport148_013_decode ridgeSupport148_suffix_decode_014
theorem ridgeSupport148_suffix_decode_012 : PackedRawNatGrowth.readList 14 269 ridgeSupport148_rest_012 =
    (ridgeSupport148_suffix_012, ridgeSupport148_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 237
    ridgeSupport148_rest_012 ridgeSupport148_rest_013 ridgeSupport148_rest_021
    ridgeSupport148_012 ridgeSupport148_suffix_013 ridgeSupport148_012_decode ridgeSupport148_suffix_decode_013
theorem ridgeSupport148_suffix_decode_011 : PackedRawNatGrowth.readList 14 301 ridgeSupport148_rest_011 =
    (ridgeSupport148_suffix_011, ridgeSupport148_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 269
    ridgeSupport148_rest_011 ridgeSupport148_rest_012 ridgeSupport148_rest_021
    ridgeSupport148_011 ridgeSupport148_suffix_012 ridgeSupport148_011_decode ridgeSupport148_suffix_decode_012
theorem ridgeSupport148_suffix_decode_010 : PackedRawNatGrowth.readList 14 333 ridgeSupport148_rest_010 =
    (ridgeSupport148_suffix_010, ridgeSupport148_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 301
    ridgeSupport148_rest_010 ridgeSupport148_rest_011 ridgeSupport148_rest_021
    ridgeSupport148_010 ridgeSupport148_suffix_011 ridgeSupport148_010_decode ridgeSupport148_suffix_decode_011
theorem ridgeSupport148_suffix_decode_009 : PackedRawNatGrowth.readList 14 365 ridgeSupport148_rest_009 =
    (ridgeSupport148_suffix_009, ridgeSupport148_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 333
    ridgeSupport148_rest_009 ridgeSupport148_rest_010 ridgeSupport148_rest_021
    ridgeSupport148_009 ridgeSupport148_suffix_010 ridgeSupport148_009_decode ridgeSupport148_suffix_decode_010
theorem ridgeSupport148_suffix_decode_008 : PackedRawNatGrowth.readList 14 397 ridgeSupport148_rest_008 =
    (ridgeSupport148_suffix_008, ridgeSupport148_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 365
    ridgeSupport148_rest_008 ridgeSupport148_rest_009 ridgeSupport148_rest_021
    ridgeSupport148_008 ridgeSupport148_suffix_009 ridgeSupport148_008_decode ridgeSupport148_suffix_decode_009
theorem ridgeSupport148_suffix_decode_007 : PackedRawNatGrowth.readList 14 429 ridgeSupport148_rest_007 =
    (ridgeSupport148_suffix_007, ridgeSupport148_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 397
    ridgeSupport148_rest_007 ridgeSupport148_rest_008 ridgeSupport148_rest_021
    ridgeSupport148_007 ridgeSupport148_suffix_008 ridgeSupport148_007_decode ridgeSupport148_suffix_decode_008
theorem ridgeSupport148_suffix_decode_006 : PackedRawNatGrowth.readList 14 461 ridgeSupport148_rest_006 =
    (ridgeSupport148_suffix_006, ridgeSupport148_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 429
    ridgeSupport148_rest_006 ridgeSupport148_rest_007 ridgeSupport148_rest_021
    ridgeSupport148_006 ridgeSupport148_suffix_007 ridgeSupport148_006_decode ridgeSupport148_suffix_decode_007
theorem ridgeSupport148_suffix_decode_005 : PackedRawNatGrowth.readList 14 493 ridgeSupport148_rest_005 =
    (ridgeSupport148_suffix_005, ridgeSupport148_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 461
    ridgeSupport148_rest_005 ridgeSupport148_rest_006 ridgeSupport148_rest_021
    ridgeSupport148_005 ridgeSupport148_suffix_006 ridgeSupport148_005_decode ridgeSupport148_suffix_decode_006
theorem ridgeSupport148_suffix_decode_004 : PackedRawNatGrowth.readList 14 525 ridgeSupport148_rest_004 =
    (ridgeSupport148_suffix_004, ridgeSupport148_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 493
    ridgeSupport148_rest_004 ridgeSupport148_rest_005 ridgeSupport148_rest_021
    ridgeSupport148_004 ridgeSupport148_suffix_005 ridgeSupport148_004_decode ridgeSupport148_suffix_decode_005
theorem ridgeSupport148_suffix_decode_003 : PackedRawNatGrowth.readList 14 557 ridgeSupport148_rest_003 =
    (ridgeSupport148_suffix_003, ridgeSupport148_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 525
    ridgeSupport148_rest_003 ridgeSupport148_rest_004 ridgeSupport148_rest_021
    ridgeSupport148_003 ridgeSupport148_suffix_004 ridgeSupport148_003_decode ridgeSupport148_suffix_decode_004
theorem ridgeSupport148_suffix_decode_002 : PackedRawNatGrowth.readList 14 589 ridgeSupport148_rest_002 =
    (ridgeSupport148_suffix_002, ridgeSupport148_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 557
    ridgeSupport148_rest_002 ridgeSupport148_rest_003 ridgeSupport148_rest_021
    ridgeSupport148_002 ridgeSupport148_suffix_003 ridgeSupport148_002_decode ridgeSupport148_suffix_decode_003
theorem ridgeSupport148_suffix_decode_001 : PackedRawNatGrowth.readList 14 621 ridgeSupport148_rest_001 =
    (ridgeSupport148_suffix_001, ridgeSupport148_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 589
    ridgeSupport148_rest_001 ridgeSupport148_rest_002 ridgeSupport148_rest_021
    ridgeSupport148_001 ridgeSupport148_suffix_002 ridgeSupport148_001_decode ridgeSupport148_suffix_decode_002
theorem ridgeSupport148_suffix_decode_000 : PackedRawNatGrowth.readList 14 653 ridgeSupport148_rest_000 =
    (ridgeSupport148_suffix_000, ridgeSupport148_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 621
    ridgeSupport148_rest_000 ridgeSupport148_rest_001 ridgeSupport148_rest_021
    ridgeSupport148_000 ridgeSupport148_suffix_001 ridgeSupport148_000_decode ridgeSupport148_suffix_decode_001
theorem ridgeSupport148_eq : candidateRows 148 = ridgeSupport148_suffix_000 := by
  rw [ridgeSupport148_source]
  exact congrArg Prod.fst ridgeSupport148_suffix_decode_000
theorem ridgeTest_large_148 : ridgeTest 148 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport148_eq]
    simp only [ridgeSupport148_suffix_000, ridgeSupport148_suffix_001, ridgeSupport148_suffix_002, ridgeSupport148_suffix_003, ridgeSupport148_suffix_004, ridgeSupport148_suffix_005, ridgeSupport148_suffix_006, ridgeSupport148_suffix_007, ridgeSupport148_suffix_008, ridgeSupport148_suffix_009, ridgeSupport148_suffix_010, ridgeSupport148_suffix_011, ridgeSupport148_suffix_012, ridgeSupport148_suffix_013, ridgeSupport148_suffix_014, ridgeSupport148_suffix_015, ridgeSupport148_suffix_016, ridgeSupport148_suffix_017, ridgeSupport148_suffix_018, ridgeSupport148_suffix_019, ridgeSupport148_suffix_020, ridgeSupport148_suffix_021, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport148_000_mask, ridgeSupport148_001_mask, ridgeSupport148_002_mask, ridgeSupport148_003_mask, ridgeSupport148_004_mask, ridgeSupport148_005_mask, ridgeSupport148_006_mask, ridgeSupport148_007_mask, ridgeSupport148_008_mask, ridgeSupport148_009_mask, ridgeSupport148_010_mask, ridgeSupport148_011_mask, ridgeSupport148_012_mask, ridgeSupport148_013_mask, ridgeSupport148_014_mask, ridgeSupport148_015_mask, ridgeSupport148_016_mask, ridgeSupport148_017_mask, ridgeSupport148_018_mask, ridgeSupport148_019_mask, ridgeSupport148_020_mask]
    decide +kernel
  · rw [ridgeSupport148_eq]
    simp only [ridgeSupport148_suffix_000, ridgeSupport148_suffix_001, ridgeSupport148_suffix_002, ridgeSupport148_suffix_003, ridgeSupport148_suffix_004, ridgeSupport148_suffix_005, ridgeSupport148_suffix_006, ridgeSupport148_suffix_007, ridgeSupport148_suffix_008, ridgeSupport148_suffix_009, ridgeSupport148_suffix_010, ridgeSupport148_suffix_011, ridgeSupport148_suffix_012, ridgeSupport148_suffix_013, ridgeSupport148_suffix_014, ridgeSupport148_suffix_015, ridgeSupport148_suffix_016, ridgeSupport148_suffix_017, ridgeSupport148_suffix_018, ridgeSupport148_suffix_019, ridgeSupport148_suffix_020, ridgeSupport148_suffix_021, List.all_append, List.all_nil, ridgeSupport148_000_checked, ridgeSupport148_001_checked, ridgeSupport148_002_checked, ridgeSupport148_003_checked, ridgeSupport148_004_checked, ridgeSupport148_005_checked, ridgeSupport148_006_checked, ridgeSupport148_007_checked, ridgeSupport148_008_checked, ridgeSupport148_009_checked, ridgeSupport148_010_checked, ridgeSupport148_011_checked, ridgeSupport148_012_checked, ridgeSupport148_013_checked, ridgeSupport148_014_checked, ridgeSupport148_015_checked, ridgeSupport148_016_checked, ridgeSupport148_017_checked, ridgeSupport148_018_checked, ridgeSupport148_019_checked, ridgeSupport148_020_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase01
