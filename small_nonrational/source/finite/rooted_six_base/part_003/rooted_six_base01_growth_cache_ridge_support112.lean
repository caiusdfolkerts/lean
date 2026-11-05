module
prelude
public import RootedSixBase01GrowthCacheRidgeSupport112Part000
public import RootedSixBase01GrowthCacheRidgeSupport112Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport112_suffix_decode_016 : PackedRawNatGrowth.readList 14 0 ridgeSupport112_rest_016 =
    (ridgeSupport112_suffix_016, ridgeSupport112_rest_016) := by rfl
theorem ridgeSupport112_suffix_decode_015 : PackedRawNatGrowth.readList 14 29 ridgeSupport112_rest_015 =
    (ridgeSupport112_suffix_015, ridgeSupport112_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 29 0
    ridgeSupport112_rest_015 ridgeSupport112_rest_016 ridgeSupport112_rest_016
    ridgeSupport112_015 ridgeSupport112_suffix_016 ridgeSupport112_015_decode ridgeSupport112_suffix_decode_016
theorem ridgeSupport112_suffix_decode_014 : PackedRawNatGrowth.readList 14 61 ridgeSupport112_rest_014 =
    (ridgeSupport112_suffix_014, ridgeSupport112_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 29
    ridgeSupport112_rest_014 ridgeSupport112_rest_015 ridgeSupport112_rest_016
    ridgeSupport112_014 ridgeSupport112_suffix_015 ridgeSupport112_014_decode ridgeSupport112_suffix_decode_015
theorem ridgeSupport112_suffix_decode_013 : PackedRawNatGrowth.readList 14 93 ridgeSupport112_rest_013 =
    (ridgeSupport112_suffix_013, ridgeSupport112_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 61
    ridgeSupport112_rest_013 ridgeSupport112_rest_014 ridgeSupport112_rest_016
    ridgeSupport112_013 ridgeSupport112_suffix_014 ridgeSupport112_013_decode ridgeSupport112_suffix_decode_014
theorem ridgeSupport112_suffix_decode_012 : PackedRawNatGrowth.readList 14 125 ridgeSupport112_rest_012 =
    (ridgeSupport112_suffix_012, ridgeSupport112_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 93
    ridgeSupport112_rest_012 ridgeSupport112_rest_013 ridgeSupport112_rest_016
    ridgeSupport112_012 ridgeSupport112_suffix_013 ridgeSupport112_012_decode ridgeSupport112_suffix_decode_013
theorem ridgeSupport112_suffix_decode_011 : PackedRawNatGrowth.readList 14 157 ridgeSupport112_rest_011 =
    (ridgeSupport112_suffix_011, ridgeSupport112_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 125
    ridgeSupport112_rest_011 ridgeSupport112_rest_012 ridgeSupport112_rest_016
    ridgeSupport112_011 ridgeSupport112_suffix_012 ridgeSupport112_011_decode ridgeSupport112_suffix_decode_012
theorem ridgeSupport112_suffix_decode_010 : PackedRawNatGrowth.readList 14 189 ridgeSupport112_rest_010 =
    (ridgeSupport112_suffix_010, ridgeSupport112_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 157
    ridgeSupport112_rest_010 ridgeSupport112_rest_011 ridgeSupport112_rest_016
    ridgeSupport112_010 ridgeSupport112_suffix_011 ridgeSupport112_010_decode ridgeSupport112_suffix_decode_011
theorem ridgeSupport112_suffix_decode_009 : PackedRawNatGrowth.readList 14 221 ridgeSupport112_rest_009 =
    (ridgeSupport112_suffix_009, ridgeSupport112_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 189
    ridgeSupport112_rest_009 ridgeSupport112_rest_010 ridgeSupport112_rest_016
    ridgeSupport112_009 ridgeSupport112_suffix_010 ridgeSupport112_009_decode ridgeSupport112_suffix_decode_010
theorem ridgeSupport112_suffix_decode_008 : PackedRawNatGrowth.readList 14 253 ridgeSupport112_rest_008 =
    (ridgeSupport112_suffix_008, ridgeSupport112_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 221
    ridgeSupport112_rest_008 ridgeSupport112_rest_009 ridgeSupport112_rest_016
    ridgeSupport112_008 ridgeSupport112_suffix_009 ridgeSupport112_008_decode ridgeSupport112_suffix_decode_009
theorem ridgeSupport112_suffix_decode_007 : PackedRawNatGrowth.readList 14 285 ridgeSupport112_rest_007 =
    (ridgeSupport112_suffix_007, ridgeSupport112_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 253
    ridgeSupport112_rest_007 ridgeSupport112_rest_008 ridgeSupport112_rest_016
    ridgeSupport112_007 ridgeSupport112_suffix_008 ridgeSupport112_007_decode ridgeSupport112_suffix_decode_008
theorem ridgeSupport112_suffix_decode_006 : PackedRawNatGrowth.readList 14 317 ridgeSupport112_rest_006 =
    (ridgeSupport112_suffix_006, ridgeSupport112_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 285
    ridgeSupport112_rest_006 ridgeSupport112_rest_007 ridgeSupport112_rest_016
    ridgeSupport112_006 ridgeSupport112_suffix_007 ridgeSupport112_006_decode ridgeSupport112_suffix_decode_007
theorem ridgeSupport112_suffix_decode_005 : PackedRawNatGrowth.readList 14 349 ridgeSupport112_rest_005 =
    (ridgeSupport112_suffix_005, ridgeSupport112_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 317
    ridgeSupport112_rest_005 ridgeSupport112_rest_006 ridgeSupport112_rest_016
    ridgeSupport112_005 ridgeSupport112_suffix_006 ridgeSupport112_005_decode ridgeSupport112_suffix_decode_006
theorem ridgeSupport112_suffix_decode_004 : PackedRawNatGrowth.readList 14 381 ridgeSupport112_rest_004 =
    (ridgeSupport112_suffix_004, ridgeSupport112_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 349
    ridgeSupport112_rest_004 ridgeSupport112_rest_005 ridgeSupport112_rest_016
    ridgeSupport112_004 ridgeSupport112_suffix_005 ridgeSupport112_004_decode ridgeSupport112_suffix_decode_005
theorem ridgeSupport112_suffix_decode_003 : PackedRawNatGrowth.readList 14 413 ridgeSupport112_rest_003 =
    (ridgeSupport112_suffix_003, ridgeSupport112_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 381
    ridgeSupport112_rest_003 ridgeSupport112_rest_004 ridgeSupport112_rest_016
    ridgeSupport112_003 ridgeSupport112_suffix_004 ridgeSupport112_003_decode ridgeSupport112_suffix_decode_004
theorem ridgeSupport112_suffix_decode_002 : PackedRawNatGrowth.readList 14 445 ridgeSupport112_rest_002 =
    (ridgeSupport112_suffix_002, ridgeSupport112_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 413
    ridgeSupport112_rest_002 ridgeSupport112_rest_003 ridgeSupport112_rest_016
    ridgeSupport112_002 ridgeSupport112_suffix_003 ridgeSupport112_002_decode ridgeSupport112_suffix_decode_003
theorem ridgeSupport112_suffix_decode_001 : PackedRawNatGrowth.readList 14 477 ridgeSupport112_rest_001 =
    (ridgeSupport112_suffix_001, ridgeSupport112_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 445
    ridgeSupport112_rest_001 ridgeSupport112_rest_002 ridgeSupport112_rest_016
    ridgeSupport112_001 ridgeSupport112_suffix_002 ridgeSupport112_001_decode ridgeSupport112_suffix_decode_002
theorem ridgeSupport112_suffix_decode_000 : PackedRawNatGrowth.readList 14 509 ridgeSupport112_rest_000 =
    (ridgeSupport112_suffix_000, ridgeSupport112_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 477
    ridgeSupport112_rest_000 ridgeSupport112_rest_001 ridgeSupport112_rest_016
    ridgeSupport112_000 ridgeSupport112_suffix_001 ridgeSupport112_000_decode ridgeSupport112_suffix_decode_001
theorem ridgeSupport112_eq : candidateRows 112 = ridgeSupport112_suffix_000 := by
  rw [ridgeSupport112_source]
  exact congrArg Prod.fst ridgeSupport112_suffix_decode_000
theorem ridgeTest_large_112 : ridgeTest 112 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport112_eq]
    simp only [ridgeSupport112_suffix_000, ridgeSupport112_suffix_001, ridgeSupport112_suffix_002, ridgeSupport112_suffix_003, ridgeSupport112_suffix_004, ridgeSupport112_suffix_005, ridgeSupport112_suffix_006, ridgeSupport112_suffix_007, ridgeSupport112_suffix_008, ridgeSupport112_suffix_009, ridgeSupport112_suffix_010, ridgeSupport112_suffix_011, ridgeSupport112_suffix_012, ridgeSupport112_suffix_013, ridgeSupport112_suffix_014, ridgeSupport112_suffix_015, ridgeSupport112_suffix_016, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport112_000_mask, ridgeSupport112_001_mask, ridgeSupport112_002_mask, ridgeSupport112_003_mask, ridgeSupport112_004_mask, ridgeSupport112_005_mask, ridgeSupport112_006_mask, ridgeSupport112_007_mask, ridgeSupport112_008_mask, ridgeSupport112_009_mask, ridgeSupport112_010_mask, ridgeSupport112_011_mask, ridgeSupport112_012_mask, ridgeSupport112_013_mask, ridgeSupport112_014_mask, ridgeSupport112_015_mask]
    decide +kernel
  · rw [ridgeSupport112_eq]
    simp only [ridgeSupport112_suffix_000, ridgeSupport112_suffix_001, ridgeSupport112_suffix_002, ridgeSupport112_suffix_003, ridgeSupport112_suffix_004, ridgeSupport112_suffix_005, ridgeSupport112_suffix_006, ridgeSupport112_suffix_007, ridgeSupport112_suffix_008, ridgeSupport112_suffix_009, ridgeSupport112_suffix_010, ridgeSupport112_suffix_011, ridgeSupport112_suffix_012, ridgeSupport112_suffix_013, ridgeSupport112_suffix_014, ridgeSupport112_suffix_015, ridgeSupport112_suffix_016, List.all_append, List.all_nil, ridgeSupport112_000_checked, ridgeSupport112_001_checked, ridgeSupport112_002_checked, ridgeSupport112_003_checked, ridgeSupport112_004_checked, ridgeSupport112_005_checked, ridgeSupport112_006_checked, ridgeSupport112_007_checked, ridgeSupport112_008_checked, ridgeSupport112_009_checked, ridgeSupport112_010_checked, ridgeSupport112_011_checked, ridgeSupport112_012_checked, ridgeSupport112_013_checked, ridgeSupport112_014_checked, ridgeSupport112_015_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase01
