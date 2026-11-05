module
prelude
public import RootedSixBase01GrowthCacheRidgeSupport74Part000
public import RootedSixBase01GrowthCacheRidgeSupport74Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport74_suffix_decode_016 : PackedRawNatGrowth.readList 14 0 ridgeSupport74_rest_016 =
    (ridgeSupport74_suffix_016, ridgeSupport74_rest_016) := by rfl
theorem ridgeSupport74_suffix_decode_015 : PackedRawNatGrowth.readList 14 29 ridgeSupport74_rest_015 =
    (ridgeSupport74_suffix_015, ridgeSupport74_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 29 0
    ridgeSupport74_rest_015 ridgeSupport74_rest_016 ridgeSupport74_rest_016
    ridgeSupport74_015 ridgeSupport74_suffix_016 ridgeSupport74_015_decode ridgeSupport74_suffix_decode_016
theorem ridgeSupport74_suffix_decode_014 : PackedRawNatGrowth.readList 14 61 ridgeSupport74_rest_014 =
    (ridgeSupport74_suffix_014, ridgeSupport74_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 29
    ridgeSupport74_rest_014 ridgeSupport74_rest_015 ridgeSupport74_rest_016
    ridgeSupport74_014 ridgeSupport74_suffix_015 ridgeSupport74_014_decode ridgeSupport74_suffix_decode_015
theorem ridgeSupport74_suffix_decode_013 : PackedRawNatGrowth.readList 14 93 ridgeSupport74_rest_013 =
    (ridgeSupport74_suffix_013, ridgeSupport74_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 61
    ridgeSupport74_rest_013 ridgeSupport74_rest_014 ridgeSupport74_rest_016
    ridgeSupport74_013 ridgeSupport74_suffix_014 ridgeSupport74_013_decode ridgeSupport74_suffix_decode_014
theorem ridgeSupport74_suffix_decode_012 : PackedRawNatGrowth.readList 14 125 ridgeSupport74_rest_012 =
    (ridgeSupport74_suffix_012, ridgeSupport74_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 93
    ridgeSupport74_rest_012 ridgeSupport74_rest_013 ridgeSupport74_rest_016
    ridgeSupport74_012 ridgeSupport74_suffix_013 ridgeSupport74_012_decode ridgeSupport74_suffix_decode_013
theorem ridgeSupport74_suffix_decode_011 : PackedRawNatGrowth.readList 14 157 ridgeSupport74_rest_011 =
    (ridgeSupport74_suffix_011, ridgeSupport74_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 125
    ridgeSupport74_rest_011 ridgeSupport74_rest_012 ridgeSupport74_rest_016
    ridgeSupport74_011 ridgeSupport74_suffix_012 ridgeSupport74_011_decode ridgeSupport74_suffix_decode_012
theorem ridgeSupport74_suffix_decode_010 : PackedRawNatGrowth.readList 14 189 ridgeSupport74_rest_010 =
    (ridgeSupport74_suffix_010, ridgeSupport74_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 157
    ridgeSupport74_rest_010 ridgeSupport74_rest_011 ridgeSupport74_rest_016
    ridgeSupport74_010 ridgeSupport74_suffix_011 ridgeSupport74_010_decode ridgeSupport74_suffix_decode_011
theorem ridgeSupport74_suffix_decode_009 : PackedRawNatGrowth.readList 14 221 ridgeSupport74_rest_009 =
    (ridgeSupport74_suffix_009, ridgeSupport74_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 189
    ridgeSupport74_rest_009 ridgeSupport74_rest_010 ridgeSupport74_rest_016
    ridgeSupport74_009 ridgeSupport74_suffix_010 ridgeSupport74_009_decode ridgeSupport74_suffix_decode_010
theorem ridgeSupport74_suffix_decode_008 : PackedRawNatGrowth.readList 14 253 ridgeSupport74_rest_008 =
    (ridgeSupport74_suffix_008, ridgeSupport74_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 221
    ridgeSupport74_rest_008 ridgeSupport74_rest_009 ridgeSupport74_rest_016
    ridgeSupport74_008 ridgeSupport74_suffix_009 ridgeSupport74_008_decode ridgeSupport74_suffix_decode_009
theorem ridgeSupport74_suffix_decode_007 : PackedRawNatGrowth.readList 14 285 ridgeSupport74_rest_007 =
    (ridgeSupport74_suffix_007, ridgeSupport74_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 253
    ridgeSupport74_rest_007 ridgeSupport74_rest_008 ridgeSupport74_rest_016
    ridgeSupport74_007 ridgeSupport74_suffix_008 ridgeSupport74_007_decode ridgeSupport74_suffix_decode_008
theorem ridgeSupport74_suffix_decode_006 : PackedRawNatGrowth.readList 14 317 ridgeSupport74_rest_006 =
    (ridgeSupport74_suffix_006, ridgeSupport74_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 285
    ridgeSupport74_rest_006 ridgeSupport74_rest_007 ridgeSupport74_rest_016
    ridgeSupport74_006 ridgeSupport74_suffix_007 ridgeSupport74_006_decode ridgeSupport74_suffix_decode_007
theorem ridgeSupport74_suffix_decode_005 : PackedRawNatGrowth.readList 14 349 ridgeSupport74_rest_005 =
    (ridgeSupport74_suffix_005, ridgeSupport74_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 317
    ridgeSupport74_rest_005 ridgeSupport74_rest_006 ridgeSupport74_rest_016
    ridgeSupport74_005 ridgeSupport74_suffix_006 ridgeSupport74_005_decode ridgeSupport74_suffix_decode_006
theorem ridgeSupport74_suffix_decode_004 : PackedRawNatGrowth.readList 14 381 ridgeSupport74_rest_004 =
    (ridgeSupport74_suffix_004, ridgeSupport74_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 349
    ridgeSupport74_rest_004 ridgeSupport74_rest_005 ridgeSupport74_rest_016
    ridgeSupport74_004 ridgeSupport74_suffix_005 ridgeSupport74_004_decode ridgeSupport74_suffix_decode_005
theorem ridgeSupport74_suffix_decode_003 : PackedRawNatGrowth.readList 14 413 ridgeSupport74_rest_003 =
    (ridgeSupport74_suffix_003, ridgeSupport74_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 381
    ridgeSupport74_rest_003 ridgeSupport74_rest_004 ridgeSupport74_rest_016
    ridgeSupport74_003 ridgeSupport74_suffix_004 ridgeSupport74_003_decode ridgeSupport74_suffix_decode_004
theorem ridgeSupport74_suffix_decode_002 : PackedRawNatGrowth.readList 14 445 ridgeSupport74_rest_002 =
    (ridgeSupport74_suffix_002, ridgeSupport74_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 413
    ridgeSupport74_rest_002 ridgeSupport74_rest_003 ridgeSupport74_rest_016
    ridgeSupport74_002 ridgeSupport74_suffix_003 ridgeSupport74_002_decode ridgeSupport74_suffix_decode_003
theorem ridgeSupport74_suffix_decode_001 : PackedRawNatGrowth.readList 14 477 ridgeSupport74_rest_001 =
    (ridgeSupport74_suffix_001, ridgeSupport74_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 445
    ridgeSupport74_rest_001 ridgeSupport74_rest_002 ridgeSupport74_rest_016
    ridgeSupport74_001 ridgeSupport74_suffix_002 ridgeSupport74_001_decode ridgeSupport74_suffix_decode_002
theorem ridgeSupport74_suffix_decode_000 : PackedRawNatGrowth.readList 14 509 ridgeSupport74_rest_000 =
    (ridgeSupport74_suffix_000, ridgeSupport74_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 477
    ridgeSupport74_rest_000 ridgeSupport74_rest_001 ridgeSupport74_rest_016
    ridgeSupport74_000 ridgeSupport74_suffix_001 ridgeSupport74_000_decode ridgeSupport74_suffix_decode_001
theorem ridgeSupport74_eq : candidateRows 74 = ridgeSupport74_suffix_000 := by
  rw [ridgeSupport74_source]
  exact congrArg Prod.fst ridgeSupport74_suffix_decode_000
theorem ridgeTest_large_74 : ridgeTest 74 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport74_eq]
    simp only [ridgeSupport74_suffix_000, ridgeSupport74_suffix_001, ridgeSupport74_suffix_002, ridgeSupport74_suffix_003, ridgeSupport74_suffix_004, ridgeSupport74_suffix_005, ridgeSupport74_suffix_006, ridgeSupport74_suffix_007, ridgeSupport74_suffix_008, ridgeSupport74_suffix_009, ridgeSupport74_suffix_010, ridgeSupport74_suffix_011, ridgeSupport74_suffix_012, ridgeSupport74_suffix_013, ridgeSupport74_suffix_014, ridgeSupport74_suffix_015, ridgeSupport74_suffix_016, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport74_000_mask, ridgeSupport74_001_mask, ridgeSupport74_002_mask, ridgeSupport74_003_mask, ridgeSupport74_004_mask, ridgeSupport74_005_mask, ridgeSupport74_006_mask, ridgeSupport74_007_mask, ridgeSupport74_008_mask, ridgeSupport74_009_mask, ridgeSupport74_010_mask, ridgeSupport74_011_mask, ridgeSupport74_012_mask, ridgeSupport74_013_mask, ridgeSupport74_014_mask, ridgeSupport74_015_mask]
    decide +kernel
  · rw [ridgeSupport74_eq]
    simp only [ridgeSupport74_suffix_000, ridgeSupport74_suffix_001, ridgeSupport74_suffix_002, ridgeSupport74_suffix_003, ridgeSupport74_suffix_004, ridgeSupport74_suffix_005, ridgeSupport74_suffix_006, ridgeSupport74_suffix_007, ridgeSupport74_suffix_008, ridgeSupport74_suffix_009, ridgeSupport74_suffix_010, ridgeSupport74_suffix_011, ridgeSupport74_suffix_012, ridgeSupport74_suffix_013, ridgeSupport74_suffix_014, ridgeSupport74_suffix_015, ridgeSupport74_suffix_016, List.all_append, List.all_nil, ridgeSupport74_000_checked, ridgeSupport74_001_checked, ridgeSupport74_002_checked, ridgeSupport74_003_checked, ridgeSupport74_004_checked, ridgeSupport74_005_checked, ridgeSupport74_006_checked, ridgeSupport74_007_checked, ridgeSupport74_008_checked, ridgeSupport74_009_checked, ridgeSupport74_010_checked, ridgeSupport74_011_checked, ridgeSupport74_012_checked, ridgeSupport74_013_checked, ridgeSupport74_014_checked, ridgeSupport74_015_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase01
