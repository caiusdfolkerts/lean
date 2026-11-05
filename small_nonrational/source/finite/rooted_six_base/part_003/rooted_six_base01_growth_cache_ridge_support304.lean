module
prelude
public import RootedSixBase01GrowthCacheRidgeSupport304Part000
public import RootedSixBase01GrowthCacheRidgeSupport304Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport304_suffix_decode_016 : PackedRawNatGrowth.readList 14 0 ridgeSupport304_rest_016 =
    (ridgeSupport304_suffix_016, ridgeSupport304_rest_016) := by rfl
theorem ridgeSupport304_suffix_decode_015 : PackedRawNatGrowth.readList 14 29 ridgeSupport304_rest_015 =
    (ridgeSupport304_suffix_015, ridgeSupport304_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 29 0
    ridgeSupport304_rest_015 ridgeSupport304_rest_016 ridgeSupport304_rest_016
    ridgeSupport304_015 ridgeSupport304_suffix_016 ridgeSupport304_015_decode ridgeSupport304_suffix_decode_016
theorem ridgeSupport304_suffix_decode_014 : PackedRawNatGrowth.readList 14 61 ridgeSupport304_rest_014 =
    (ridgeSupport304_suffix_014, ridgeSupport304_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 29
    ridgeSupport304_rest_014 ridgeSupport304_rest_015 ridgeSupport304_rest_016
    ridgeSupport304_014 ridgeSupport304_suffix_015 ridgeSupport304_014_decode ridgeSupport304_suffix_decode_015
theorem ridgeSupport304_suffix_decode_013 : PackedRawNatGrowth.readList 14 93 ridgeSupport304_rest_013 =
    (ridgeSupport304_suffix_013, ridgeSupport304_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 61
    ridgeSupport304_rest_013 ridgeSupport304_rest_014 ridgeSupport304_rest_016
    ridgeSupport304_013 ridgeSupport304_suffix_014 ridgeSupport304_013_decode ridgeSupport304_suffix_decode_014
theorem ridgeSupport304_suffix_decode_012 : PackedRawNatGrowth.readList 14 125 ridgeSupport304_rest_012 =
    (ridgeSupport304_suffix_012, ridgeSupport304_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 93
    ridgeSupport304_rest_012 ridgeSupport304_rest_013 ridgeSupport304_rest_016
    ridgeSupport304_012 ridgeSupport304_suffix_013 ridgeSupport304_012_decode ridgeSupport304_suffix_decode_013
theorem ridgeSupport304_suffix_decode_011 : PackedRawNatGrowth.readList 14 157 ridgeSupport304_rest_011 =
    (ridgeSupport304_suffix_011, ridgeSupport304_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 125
    ridgeSupport304_rest_011 ridgeSupport304_rest_012 ridgeSupport304_rest_016
    ridgeSupport304_011 ridgeSupport304_suffix_012 ridgeSupport304_011_decode ridgeSupport304_suffix_decode_012
theorem ridgeSupport304_suffix_decode_010 : PackedRawNatGrowth.readList 14 189 ridgeSupport304_rest_010 =
    (ridgeSupport304_suffix_010, ridgeSupport304_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 157
    ridgeSupport304_rest_010 ridgeSupport304_rest_011 ridgeSupport304_rest_016
    ridgeSupport304_010 ridgeSupport304_suffix_011 ridgeSupport304_010_decode ridgeSupport304_suffix_decode_011
theorem ridgeSupport304_suffix_decode_009 : PackedRawNatGrowth.readList 14 221 ridgeSupport304_rest_009 =
    (ridgeSupport304_suffix_009, ridgeSupport304_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 189
    ridgeSupport304_rest_009 ridgeSupport304_rest_010 ridgeSupport304_rest_016
    ridgeSupport304_009 ridgeSupport304_suffix_010 ridgeSupport304_009_decode ridgeSupport304_suffix_decode_010
theorem ridgeSupport304_suffix_decode_008 : PackedRawNatGrowth.readList 14 253 ridgeSupport304_rest_008 =
    (ridgeSupport304_suffix_008, ridgeSupport304_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 221
    ridgeSupport304_rest_008 ridgeSupport304_rest_009 ridgeSupport304_rest_016
    ridgeSupport304_008 ridgeSupport304_suffix_009 ridgeSupport304_008_decode ridgeSupport304_suffix_decode_009
theorem ridgeSupport304_suffix_decode_007 : PackedRawNatGrowth.readList 14 285 ridgeSupport304_rest_007 =
    (ridgeSupport304_suffix_007, ridgeSupport304_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 253
    ridgeSupport304_rest_007 ridgeSupport304_rest_008 ridgeSupport304_rest_016
    ridgeSupport304_007 ridgeSupport304_suffix_008 ridgeSupport304_007_decode ridgeSupport304_suffix_decode_008
theorem ridgeSupport304_suffix_decode_006 : PackedRawNatGrowth.readList 14 317 ridgeSupport304_rest_006 =
    (ridgeSupport304_suffix_006, ridgeSupport304_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 285
    ridgeSupport304_rest_006 ridgeSupport304_rest_007 ridgeSupport304_rest_016
    ridgeSupport304_006 ridgeSupport304_suffix_007 ridgeSupport304_006_decode ridgeSupport304_suffix_decode_007
theorem ridgeSupport304_suffix_decode_005 : PackedRawNatGrowth.readList 14 349 ridgeSupport304_rest_005 =
    (ridgeSupport304_suffix_005, ridgeSupport304_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 317
    ridgeSupport304_rest_005 ridgeSupport304_rest_006 ridgeSupport304_rest_016
    ridgeSupport304_005 ridgeSupport304_suffix_006 ridgeSupport304_005_decode ridgeSupport304_suffix_decode_006
theorem ridgeSupport304_suffix_decode_004 : PackedRawNatGrowth.readList 14 381 ridgeSupport304_rest_004 =
    (ridgeSupport304_suffix_004, ridgeSupport304_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 349
    ridgeSupport304_rest_004 ridgeSupport304_rest_005 ridgeSupport304_rest_016
    ridgeSupport304_004 ridgeSupport304_suffix_005 ridgeSupport304_004_decode ridgeSupport304_suffix_decode_005
theorem ridgeSupport304_suffix_decode_003 : PackedRawNatGrowth.readList 14 413 ridgeSupport304_rest_003 =
    (ridgeSupport304_suffix_003, ridgeSupport304_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 381
    ridgeSupport304_rest_003 ridgeSupport304_rest_004 ridgeSupport304_rest_016
    ridgeSupport304_003 ridgeSupport304_suffix_004 ridgeSupport304_003_decode ridgeSupport304_suffix_decode_004
theorem ridgeSupport304_suffix_decode_002 : PackedRawNatGrowth.readList 14 445 ridgeSupport304_rest_002 =
    (ridgeSupport304_suffix_002, ridgeSupport304_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 413
    ridgeSupport304_rest_002 ridgeSupport304_rest_003 ridgeSupport304_rest_016
    ridgeSupport304_002 ridgeSupport304_suffix_003 ridgeSupport304_002_decode ridgeSupport304_suffix_decode_003
theorem ridgeSupport304_suffix_decode_001 : PackedRawNatGrowth.readList 14 477 ridgeSupport304_rest_001 =
    (ridgeSupport304_suffix_001, ridgeSupport304_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 445
    ridgeSupport304_rest_001 ridgeSupport304_rest_002 ridgeSupport304_rest_016
    ridgeSupport304_001 ridgeSupport304_suffix_002 ridgeSupport304_001_decode ridgeSupport304_suffix_decode_002
theorem ridgeSupport304_suffix_decode_000 : PackedRawNatGrowth.readList 14 509 ridgeSupport304_rest_000 =
    (ridgeSupport304_suffix_000, ridgeSupport304_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 477
    ridgeSupport304_rest_000 ridgeSupport304_rest_001 ridgeSupport304_rest_016
    ridgeSupport304_000 ridgeSupport304_suffix_001 ridgeSupport304_000_decode ridgeSupport304_suffix_decode_001
theorem ridgeSupport304_eq : candidateRows 304 = ridgeSupport304_suffix_000 := by
  rw [ridgeSupport304_source]
  exact congrArg Prod.fst ridgeSupport304_suffix_decode_000
theorem ridgeTest_large_304 : ridgeTest 304 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport304_eq]
    simp only [ridgeSupport304_suffix_000, ridgeSupport304_suffix_001, ridgeSupport304_suffix_002, ridgeSupport304_suffix_003, ridgeSupport304_suffix_004, ridgeSupport304_suffix_005, ridgeSupport304_suffix_006, ridgeSupport304_suffix_007, ridgeSupport304_suffix_008, ridgeSupport304_suffix_009, ridgeSupport304_suffix_010, ridgeSupport304_suffix_011, ridgeSupport304_suffix_012, ridgeSupport304_suffix_013, ridgeSupport304_suffix_014, ridgeSupport304_suffix_015, ridgeSupport304_suffix_016, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport304_000_mask, ridgeSupport304_001_mask, ridgeSupport304_002_mask, ridgeSupport304_003_mask, ridgeSupport304_004_mask, ridgeSupport304_005_mask, ridgeSupport304_006_mask, ridgeSupport304_007_mask, ridgeSupport304_008_mask, ridgeSupport304_009_mask, ridgeSupport304_010_mask, ridgeSupport304_011_mask, ridgeSupport304_012_mask, ridgeSupport304_013_mask, ridgeSupport304_014_mask, ridgeSupport304_015_mask]
    decide +kernel
  · rw [ridgeSupport304_eq]
    simp only [ridgeSupport304_suffix_000, ridgeSupport304_suffix_001, ridgeSupport304_suffix_002, ridgeSupport304_suffix_003, ridgeSupport304_suffix_004, ridgeSupport304_suffix_005, ridgeSupport304_suffix_006, ridgeSupport304_suffix_007, ridgeSupport304_suffix_008, ridgeSupport304_suffix_009, ridgeSupport304_suffix_010, ridgeSupport304_suffix_011, ridgeSupport304_suffix_012, ridgeSupport304_suffix_013, ridgeSupport304_suffix_014, ridgeSupport304_suffix_015, ridgeSupport304_suffix_016, List.all_append, List.all_nil, ridgeSupport304_000_checked, ridgeSupport304_001_checked, ridgeSupport304_002_checked, ridgeSupport304_003_checked, ridgeSupport304_004_checked, ridgeSupport304_005_checked, ridgeSupport304_006_checked, ridgeSupport304_007_checked, ridgeSupport304_008_checked, ridgeSupport304_009_checked, ridgeSupport304_010_checked, ridgeSupport304_011_checked, ridgeSupport304_012_checked, ridgeSupport304_013_checked, ridgeSupport304_014_checked, ridgeSupport304_015_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase01
