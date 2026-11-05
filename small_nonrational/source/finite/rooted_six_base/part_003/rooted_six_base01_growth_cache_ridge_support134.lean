module
prelude
public import RootedSixBase01GrowthCacheRidgeSupport134Part000
public import RootedSixBase01GrowthCacheRidgeSupport134Part001
public import RootedSixBase01GrowthCacheRidgeSupport134Part002
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport134_suffix_decode_021 : PackedRawNatGrowth.readList 14 0 ridgeSupport134_rest_021 =
    (ridgeSupport134_suffix_021, ridgeSupport134_rest_021) := by rfl
theorem ridgeSupport134_suffix_decode_020 : PackedRawNatGrowth.readList 14 13 ridgeSupport134_rest_020 =
    (ridgeSupport134_suffix_020, ridgeSupport134_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 13 0
    ridgeSupport134_rest_020 ridgeSupport134_rest_021 ridgeSupport134_rest_021
    ridgeSupport134_020 ridgeSupport134_suffix_021 ridgeSupport134_020_decode ridgeSupport134_suffix_decode_021
theorem ridgeSupport134_suffix_decode_019 : PackedRawNatGrowth.readList 14 45 ridgeSupport134_rest_019 =
    (ridgeSupport134_suffix_019, ridgeSupport134_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 13
    ridgeSupport134_rest_019 ridgeSupport134_rest_020 ridgeSupport134_rest_021
    ridgeSupport134_019 ridgeSupport134_suffix_020 ridgeSupport134_019_decode ridgeSupport134_suffix_decode_020
theorem ridgeSupport134_suffix_decode_018 : PackedRawNatGrowth.readList 14 77 ridgeSupport134_rest_018 =
    (ridgeSupport134_suffix_018, ridgeSupport134_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 45
    ridgeSupport134_rest_018 ridgeSupport134_rest_019 ridgeSupport134_rest_021
    ridgeSupport134_018 ridgeSupport134_suffix_019 ridgeSupport134_018_decode ridgeSupport134_suffix_decode_019
theorem ridgeSupport134_suffix_decode_017 : PackedRawNatGrowth.readList 14 109 ridgeSupport134_rest_017 =
    (ridgeSupport134_suffix_017, ridgeSupport134_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 77
    ridgeSupport134_rest_017 ridgeSupport134_rest_018 ridgeSupport134_rest_021
    ridgeSupport134_017 ridgeSupport134_suffix_018 ridgeSupport134_017_decode ridgeSupport134_suffix_decode_018
theorem ridgeSupport134_suffix_decode_016 : PackedRawNatGrowth.readList 14 141 ridgeSupport134_rest_016 =
    (ridgeSupport134_suffix_016, ridgeSupport134_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 109
    ridgeSupport134_rest_016 ridgeSupport134_rest_017 ridgeSupport134_rest_021
    ridgeSupport134_016 ridgeSupport134_suffix_017 ridgeSupport134_016_decode ridgeSupport134_suffix_decode_017
theorem ridgeSupport134_suffix_decode_015 : PackedRawNatGrowth.readList 14 173 ridgeSupport134_rest_015 =
    (ridgeSupport134_suffix_015, ridgeSupport134_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 141
    ridgeSupport134_rest_015 ridgeSupport134_rest_016 ridgeSupport134_rest_021
    ridgeSupport134_015 ridgeSupport134_suffix_016 ridgeSupport134_015_decode ridgeSupport134_suffix_decode_016
theorem ridgeSupport134_suffix_decode_014 : PackedRawNatGrowth.readList 14 205 ridgeSupport134_rest_014 =
    (ridgeSupport134_suffix_014, ridgeSupport134_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 173
    ridgeSupport134_rest_014 ridgeSupport134_rest_015 ridgeSupport134_rest_021
    ridgeSupport134_014 ridgeSupport134_suffix_015 ridgeSupport134_014_decode ridgeSupport134_suffix_decode_015
theorem ridgeSupport134_suffix_decode_013 : PackedRawNatGrowth.readList 14 237 ridgeSupport134_rest_013 =
    (ridgeSupport134_suffix_013, ridgeSupport134_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 205
    ridgeSupport134_rest_013 ridgeSupport134_rest_014 ridgeSupport134_rest_021
    ridgeSupport134_013 ridgeSupport134_suffix_014 ridgeSupport134_013_decode ridgeSupport134_suffix_decode_014
theorem ridgeSupport134_suffix_decode_012 : PackedRawNatGrowth.readList 14 269 ridgeSupport134_rest_012 =
    (ridgeSupport134_suffix_012, ridgeSupport134_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 237
    ridgeSupport134_rest_012 ridgeSupport134_rest_013 ridgeSupport134_rest_021
    ridgeSupport134_012 ridgeSupport134_suffix_013 ridgeSupport134_012_decode ridgeSupport134_suffix_decode_013
theorem ridgeSupport134_suffix_decode_011 : PackedRawNatGrowth.readList 14 301 ridgeSupport134_rest_011 =
    (ridgeSupport134_suffix_011, ridgeSupport134_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 269
    ridgeSupport134_rest_011 ridgeSupport134_rest_012 ridgeSupport134_rest_021
    ridgeSupport134_011 ridgeSupport134_suffix_012 ridgeSupport134_011_decode ridgeSupport134_suffix_decode_012
theorem ridgeSupport134_suffix_decode_010 : PackedRawNatGrowth.readList 14 333 ridgeSupport134_rest_010 =
    (ridgeSupport134_suffix_010, ridgeSupport134_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 301
    ridgeSupport134_rest_010 ridgeSupport134_rest_011 ridgeSupport134_rest_021
    ridgeSupport134_010 ridgeSupport134_suffix_011 ridgeSupport134_010_decode ridgeSupport134_suffix_decode_011
theorem ridgeSupport134_suffix_decode_009 : PackedRawNatGrowth.readList 14 365 ridgeSupport134_rest_009 =
    (ridgeSupport134_suffix_009, ridgeSupport134_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 333
    ridgeSupport134_rest_009 ridgeSupport134_rest_010 ridgeSupport134_rest_021
    ridgeSupport134_009 ridgeSupport134_suffix_010 ridgeSupport134_009_decode ridgeSupport134_suffix_decode_010
theorem ridgeSupport134_suffix_decode_008 : PackedRawNatGrowth.readList 14 397 ridgeSupport134_rest_008 =
    (ridgeSupport134_suffix_008, ridgeSupport134_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 365
    ridgeSupport134_rest_008 ridgeSupport134_rest_009 ridgeSupport134_rest_021
    ridgeSupport134_008 ridgeSupport134_suffix_009 ridgeSupport134_008_decode ridgeSupport134_suffix_decode_009
theorem ridgeSupport134_suffix_decode_007 : PackedRawNatGrowth.readList 14 429 ridgeSupport134_rest_007 =
    (ridgeSupport134_suffix_007, ridgeSupport134_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 397
    ridgeSupport134_rest_007 ridgeSupport134_rest_008 ridgeSupport134_rest_021
    ridgeSupport134_007 ridgeSupport134_suffix_008 ridgeSupport134_007_decode ridgeSupport134_suffix_decode_008
theorem ridgeSupport134_suffix_decode_006 : PackedRawNatGrowth.readList 14 461 ridgeSupport134_rest_006 =
    (ridgeSupport134_suffix_006, ridgeSupport134_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 429
    ridgeSupport134_rest_006 ridgeSupport134_rest_007 ridgeSupport134_rest_021
    ridgeSupport134_006 ridgeSupport134_suffix_007 ridgeSupport134_006_decode ridgeSupport134_suffix_decode_007
theorem ridgeSupport134_suffix_decode_005 : PackedRawNatGrowth.readList 14 493 ridgeSupport134_rest_005 =
    (ridgeSupport134_suffix_005, ridgeSupport134_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 461
    ridgeSupport134_rest_005 ridgeSupport134_rest_006 ridgeSupport134_rest_021
    ridgeSupport134_005 ridgeSupport134_suffix_006 ridgeSupport134_005_decode ridgeSupport134_suffix_decode_006
theorem ridgeSupport134_suffix_decode_004 : PackedRawNatGrowth.readList 14 525 ridgeSupport134_rest_004 =
    (ridgeSupport134_suffix_004, ridgeSupport134_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 493
    ridgeSupport134_rest_004 ridgeSupport134_rest_005 ridgeSupport134_rest_021
    ridgeSupport134_004 ridgeSupport134_suffix_005 ridgeSupport134_004_decode ridgeSupport134_suffix_decode_005
theorem ridgeSupport134_suffix_decode_003 : PackedRawNatGrowth.readList 14 557 ridgeSupport134_rest_003 =
    (ridgeSupport134_suffix_003, ridgeSupport134_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 525
    ridgeSupport134_rest_003 ridgeSupport134_rest_004 ridgeSupport134_rest_021
    ridgeSupport134_003 ridgeSupport134_suffix_004 ridgeSupport134_003_decode ridgeSupport134_suffix_decode_004
theorem ridgeSupport134_suffix_decode_002 : PackedRawNatGrowth.readList 14 589 ridgeSupport134_rest_002 =
    (ridgeSupport134_suffix_002, ridgeSupport134_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 557
    ridgeSupport134_rest_002 ridgeSupport134_rest_003 ridgeSupport134_rest_021
    ridgeSupport134_002 ridgeSupport134_suffix_003 ridgeSupport134_002_decode ridgeSupport134_suffix_decode_003
theorem ridgeSupport134_suffix_decode_001 : PackedRawNatGrowth.readList 14 621 ridgeSupport134_rest_001 =
    (ridgeSupport134_suffix_001, ridgeSupport134_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 589
    ridgeSupport134_rest_001 ridgeSupport134_rest_002 ridgeSupport134_rest_021
    ridgeSupport134_001 ridgeSupport134_suffix_002 ridgeSupport134_001_decode ridgeSupport134_suffix_decode_002
theorem ridgeSupport134_suffix_decode_000 : PackedRawNatGrowth.readList 14 653 ridgeSupport134_rest_000 =
    (ridgeSupport134_suffix_000, ridgeSupport134_rest_021) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 621
    ridgeSupport134_rest_000 ridgeSupport134_rest_001 ridgeSupport134_rest_021
    ridgeSupport134_000 ridgeSupport134_suffix_001 ridgeSupport134_000_decode ridgeSupport134_suffix_decode_001
theorem ridgeSupport134_eq : candidateRows 134 = ridgeSupport134_suffix_000 := by
  rw [ridgeSupport134_source]
  exact congrArg Prod.fst ridgeSupport134_suffix_decode_000
theorem ridgeTest_large_134 : ridgeTest 134 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport134_eq]
    simp only [ridgeSupport134_suffix_000, ridgeSupport134_suffix_001, ridgeSupport134_suffix_002, ridgeSupport134_suffix_003, ridgeSupport134_suffix_004, ridgeSupport134_suffix_005, ridgeSupport134_suffix_006, ridgeSupport134_suffix_007, ridgeSupport134_suffix_008, ridgeSupport134_suffix_009, ridgeSupport134_suffix_010, ridgeSupport134_suffix_011, ridgeSupport134_suffix_012, ridgeSupport134_suffix_013, ridgeSupport134_suffix_014, ridgeSupport134_suffix_015, ridgeSupport134_suffix_016, ridgeSupport134_suffix_017, ridgeSupport134_suffix_018, ridgeSupport134_suffix_019, ridgeSupport134_suffix_020, ridgeSupport134_suffix_021, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport134_000_mask, ridgeSupport134_001_mask, ridgeSupport134_002_mask, ridgeSupport134_003_mask, ridgeSupport134_004_mask, ridgeSupport134_005_mask, ridgeSupport134_006_mask, ridgeSupport134_007_mask, ridgeSupport134_008_mask, ridgeSupport134_009_mask, ridgeSupport134_010_mask, ridgeSupport134_011_mask, ridgeSupport134_012_mask, ridgeSupport134_013_mask, ridgeSupport134_014_mask, ridgeSupport134_015_mask, ridgeSupport134_016_mask, ridgeSupport134_017_mask, ridgeSupport134_018_mask, ridgeSupport134_019_mask, ridgeSupport134_020_mask]
    decide +kernel
  · rw [ridgeSupport134_eq]
    simp only [ridgeSupport134_suffix_000, ridgeSupport134_suffix_001, ridgeSupport134_suffix_002, ridgeSupport134_suffix_003, ridgeSupport134_suffix_004, ridgeSupport134_suffix_005, ridgeSupport134_suffix_006, ridgeSupport134_suffix_007, ridgeSupport134_suffix_008, ridgeSupport134_suffix_009, ridgeSupport134_suffix_010, ridgeSupport134_suffix_011, ridgeSupport134_suffix_012, ridgeSupport134_suffix_013, ridgeSupport134_suffix_014, ridgeSupport134_suffix_015, ridgeSupport134_suffix_016, ridgeSupport134_suffix_017, ridgeSupport134_suffix_018, ridgeSupport134_suffix_019, ridgeSupport134_suffix_020, ridgeSupport134_suffix_021, List.all_append, List.all_nil, ridgeSupport134_000_checked, ridgeSupport134_001_checked, ridgeSupport134_002_checked, ridgeSupport134_003_checked, ridgeSupport134_004_checked, ridgeSupport134_005_checked, ridgeSupport134_006_checked, ridgeSupport134_007_checked, ridgeSupport134_008_checked, ridgeSupport134_009_checked, ridgeSupport134_010_checked, ridgeSupport134_011_checked, ridgeSupport134_012_checked, ridgeSupport134_013_checked, ridgeSupport134_014_checked, ridgeSupport134_015_checked, ridgeSupport134_016_checked, ridgeSupport134_017_checked, ridgeSupport134_018_checked, ridgeSupport134_019_checked, ridgeSupport134_020_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase01
