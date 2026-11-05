module
prelude
public import RootedSixBase01GrowthCacheRidgeSupport296Part000
public import RootedSixBase01GrowthCacheRidgeSupport296Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport296_suffix_decode_016 : PackedRawNatGrowth.readList 14 0 ridgeSupport296_rest_016 =
    (ridgeSupport296_suffix_016, ridgeSupport296_rest_016) := by rfl
theorem ridgeSupport296_suffix_decode_015 : PackedRawNatGrowth.readList 14 29 ridgeSupport296_rest_015 =
    (ridgeSupport296_suffix_015, ridgeSupport296_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 29 0
    ridgeSupport296_rest_015 ridgeSupport296_rest_016 ridgeSupport296_rest_016
    ridgeSupport296_015 ridgeSupport296_suffix_016 ridgeSupport296_015_decode ridgeSupport296_suffix_decode_016
theorem ridgeSupport296_suffix_decode_014 : PackedRawNatGrowth.readList 14 61 ridgeSupport296_rest_014 =
    (ridgeSupport296_suffix_014, ridgeSupport296_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 29
    ridgeSupport296_rest_014 ridgeSupport296_rest_015 ridgeSupport296_rest_016
    ridgeSupport296_014 ridgeSupport296_suffix_015 ridgeSupport296_014_decode ridgeSupport296_suffix_decode_015
theorem ridgeSupport296_suffix_decode_013 : PackedRawNatGrowth.readList 14 93 ridgeSupport296_rest_013 =
    (ridgeSupport296_suffix_013, ridgeSupport296_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 61
    ridgeSupport296_rest_013 ridgeSupport296_rest_014 ridgeSupport296_rest_016
    ridgeSupport296_013 ridgeSupport296_suffix_014 ridgeSupport296_013_decode ridgeSupport296_suffix_decode_014
theorem ridgeSupport296_suffix_decode_012 : PackedRawNatGrowth.readList 14 125 ridgeSupport296_rest_012 =
    (ridgeSupport296_suffix_012, ridgeSupport296_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 93
    ridgeSupport296_rest_012 ridgeSupport296_rest_013 ridgeSupport296_rest_016
    ridgeSupport296_012 ridgeSupport296_suffix_013 ridgeSupport296_012_decode ridgeSupport296_suffix_decode_013
theorem ridgeSupport296_suffix_decode_011 : PackedRawNatGrowth.readList 14 157 ridgeSupport296_rest_011 =
    (ridgeSupport296_suffix_011, ridgeSupport296_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 125
    ridgeSupport296_rest_011 ridgeSupport296_rest_012 ridgeSupport296_rest_016
    ridgeSupport296_011 ridgeSupport296_suffix_012 ridgeSupport296_011_decode ridgeSupport296_suffix_decode_012
theorem ridgeSupport296_suffix_decode_010 : PackedRawNatGrowth.readList 14 189 ridgeSupport296_rest_010 =
    (ridgeSupport296_suffix_010, ridgeSupport296_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 157
    ridgeSupport296_rest_010 ridgeSupport296_rest_011 ridgeSupport296_rest_016
    ridgeSupport296_010 ridgeSupport296_suffix_011 ridgeSupport296_010_decode ridgeSupport296_suffix_decode_011
theorem ridgeSupport296_suffix_decode_009 : PackedRawNatGrowth.readList 14 221 ridgeSupport296_rest_009 =
    (ridgeSupport296_suffix_009, ridgeSupport296_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 189
    ridgeSupport296_rest_009 ridgeSupport296_rest_010 ridgeSupport296_rest_016
    ridgeSupport296_009 ridgeSupport296_suffix_010 ridgeSupport296_009_decode ridgeSupport296_suffix_decode_010
theorem ridgeSupport296_suffix_decode_008 : PackedRawNatGrowth.readList 14 253 ridgeSupport296_rest_008 =
    (ridgeSupport296_suffix_008, ridgeSupport296_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 221
    ridgeSupport296_rest_008 ridgeSupport296_rest_009 ridgeSupport296_rest_016
    ridgeSupport296_008 ridgeSupport296_suffix_009 ridgeSupport296_008_decode ridgeSupport296_suffix_decode_009
theorem ridgeSupport296_suffix_decode_007 : PackedRawNatGrowth.readList 14 285 ridgeSupport296_rest_007 =
    (ridgeSupport296_suffix_007, ridgeSupport296_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 253
    ridgeSupport296_rest_007 ridgeSupport296_rest_008 ridgeSupport296_rest_016
    ridgeSupport296_007 ridgeSupport296_suffix_008 ridgeSupport296_007_decode ridgeSupport296_suffix_decode_008
theorem ridgeSupport296_suffix_decode_006 : PackedRawNatGrowth.readList 14 317 ridgeSupport296_rest_006 =
    (ridgeSupport296_suffix_006, ridgeSupport296_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 285
    ridgeSupport296_rest_006 ridgeSupport296_rest_007 ridgeSupport296_rest_016
    ridgeSupport296_006 ridgeSupport296_suffix_007 ridgeSupport296_006_decode ridgeSupport296_suffix_decode_007
theorem ridgeSupport296_suffix_decode_005 : PackedRawNatGrowth.readList 14 349 ridgeSupport296_rest_005 =
    (ridgeSupport296_suffix_005, ridgeSupport296_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 317
    ridgeSupport296_rest_005 ridgeSupport296_rest_006 ridgeSupport296_rest_016
    ridgeSupport296_005 ridgeSupport296_suffix_006 ridgeSupport296_005_decode ridgeSupport296_suffix_decode_006
theorem ridgeSupport296_suffix_decode_004 : PackedRawNatGrowth.readList 14 381 ridgeSupport296_rest_004 =
    (ridgeSupport296_suffix_004, ridgeSupport296_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 349
    ridgeSupport296_rest_004 ridgeSupport296_rest_005 ridgeSupport296_rest_016
    ridgeSupport296_004 ridgeSupport296_suffix_005 ridgeSupport296_004_decode ridgeSupport296_suffix_decode_005
theorem ridgeSupport296_suffix_decode_003 : PackedRawNatGrowth.readList 14 413 ridgeSupport296_rest_003 =
    (ridgeSupport296_suffix_003, ridgeSupport296_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 381
    ridgeSupport296_rest_003 ridgeSupport296_rest_004 ridgeSupport296_rest_016
    ridgeSupport296_003 ridgeSupport296_suffix_004 ridgeSupport296_003_decode ridgeSupport296_suffix_decode_004
theorem ridgeSupport296_suffix_decode_002 : PackedRawNatGrowth.readList 14 445 ridgeSupport296_rest_002 =
    (ridgeSupport296_suffix_002, ridgeSupport296_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 413
    ridgeSupport296_rest_002 ridgeSupport296_rest_003 ridgeSupport296_rest_016
    ridgeSupport296_002 ridgeSupport296_suffix_003 ridgeSupport296_002_decode ridgeSupport296_suffix_decode_003
theorem ridgeSupport296_suffix_decode_001 : PackedRawNatGrowth.readList 14 477 ridgeSupport296_rest_001 =
    (ridgeSupport296_suffix_001, ridgeSupport296_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 445
    ridgeSupport296_rest_001 ridgeSupport296_rest_002 ridgeSupport296_rest_016
    ridgeSupport296_001 ridgeSupport296_suffix_002 ridgeSupport296_001_decode ridgeSupport296_suffix_decode_002
theorem ridgeSupport296_suffix_decode_000 : PackedRawNatGrowth.readList 14 509 ridgeSupport296_rest_000 =
    (ridgeSupport296_suffix_000, ridgeSupport296_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 477
    ridgeSupport296_rest_000 ridgeSupport296_rest_001 ridgeSupport296_rest_016
    ridgeSupport296_000 ridgeSupport296_suffix_001 ridgeSupport296_000_decode ridgeSupport296_suffix_decode_001
theorem ridgeSupport296_eq : candidateRows 296 = ridgeSupport296_suffix_000 := by
  rw [ridgeSupport296_source]
  exact congrArg Prod.fst ridgeSupport296_suffix_decode_000
theorem ridgeTest_large_296 : ridgeTest 296 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport296_eq]
    simp only [ridgeSupport296_suffix_000, ridgeSupport296_suffix_001, ridgeSupport296_suffix_002, ridgeSupport296_suffix_003, ridgeSupport296_suffix_004, ridgeSupport296_suffix_005, ridgeSupport296_suffix_006, ridgeSupport296_suffix_007, ridgeSupport296_suffix_008, ridgeSupport296_suffix_009, ridgeSupport296_suffix_010, ridgeSupport296_suffix_011, ridgeSupport296_suffix_012, ridgeSupport296_suffix_013, ridgeSupport296_suffix_014, ridgeSupport296_suffix_015, ridgeSupport296_suffix_016, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport296_000_mask, ridgeSupport296_001_mask, ridgeSupport296_002_mask, ridgeSupport296_003_mask, ridgeSupport296_004_mask, ridgeSupport296_005_mask, ridgeSupport296_006_mask, ridgeSupport296_007_mask, ridgeSupport296_008_mask, ridgeSupport296_009_mask, ridgeSupport296_010_mask, ridgeSupport296_011_mask, ridgeSupport296_012_mask, ridgeSupport296_013_mask, ridgeSupport296_014_mask, ridgeSupport296_015_mask]
    decide +kernel
  · rw [ridgeSupport296_eq]
    simp only [ridgeSupport296_suffix_000, ridgeSupport296_suffix_001, ridgeSupport296_suffix_002, ridgeSupport296_suffix_003, ridgeSupport296_suffix_004, ridgeSupport296_suffix_005, ridgeSupport296_suffix_006, ridgeSupport296_suffix_007, ridgeSupport296_suffix_008, ridgeSupport296_suffix_009, ridgeSupport296_suffix_010, ridgeSupport296_suffix_011, ridgeSupport296_suffix_012, ridgeSupport296_suffix_013, ridgeSupport296_suffix_014, ridgeSupport296_suffix_015, ridgeSupport296_suffix_016, List.all_append, List.all_nil, ridgeSupport296_000_checked, ridgeSupport296_001_checked, ridgeSupport296_002_checked, ridgeSupport296_003_checked, ridgeSupport296_004_checked, ridgeSupport296_005_checked, ridgeSupport296_006_checked, ridgeSupport296_007_checked, ridgeSupport296_008_checked, ridgeSupport296_009_checked, ridgeSupport296_010_checked, ridgeSupport296_011_checked, ridgeSupport296_012_checked, ridgeSupport296_013_checked, ridgeSupport296_014_checked, ridgeSupport296_015_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase01
