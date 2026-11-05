module
prelude
public import RootedSixBase01GrowthCacheRidgeSupport168Part000
public import RootedSixBase01GrowthCacheRidgeSupport168Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport168_suffix_decode_016 : PackedRawNatGrowth.readList 14 0 ridgeSupport168_rest_016 =
    (ridgeSupport168_suffix_016, ridgeSupport168_rest_016) := by rfl
theorem ridgeSupport168_suffix_decode_015 : PackedRawNatGrowth.readList 14 29 ridgeSupport168_rest_015 =
    (ridgeSupport168_suffix_015, ridgeSupport168_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 29 0
    ridgeSupport168_rest_015 ridgeSupport168_rest_016 ridgeSupport168_rest_016
    ridgeSupport168_015 ridgeSupport168_suffix_016 ridgeSupport168_015_decode ridgeSupport168_suffix_decode_016
theorem ridgeSupport168_suffix_decode_014 : PackedRawNatGrowth.readList 14 61 ridgeSupport168_rest_014 =
    (ridgeSupport168_suffix_014, ridgeSupport168_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 29
    ridgeSupport168_rest_014 ridgeSupport168_rest_015 ridgeSupport168_rest_016
    ridgeSupport168_014 ridgeSupport168_suffix_015 ridgeSupport168_014_decode ridgeSupport168_suffix_decode_015
theorem ridgeSupport168_suffix_decode_013 : PackedRawNatGrowth.readList 14 93 ridgeSupport168_rest_013 =
    (ridgeSupport168_suffix_013, ridgeSupport168_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 61
    ridgeSupport168_rest_013 ridgeSupport168_rest_014 ridgeSupport168_rest_016
    ridgeSupport168_013 ridgeSupport168_suffix_014 ridgeSupport168_013_decode ridgeSupport168_suffix_decode_014
theorem ridgeSupport168_suffix_decode_012 : PackedRawNatGrowth.readList 14 125 ridgeSupport168_rest_012 =
    (ridgeSupport168_suffix_012, ridgeSupport168_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 93
    ridgeSupport168_rest_012 ridgeSupport168_rest_013 ridgeSupport168_rest_016
    ridgeSupport168_012 ridgeSupport168_suffix_013 ridgeSupport168_012_decode ridgeSupport168_suffix_decode_013
theorem ridgeSupport168_suffix_decode_011 : PackedRawNatGrowth.readList 14 157 ridgeSupport168_rest_011 =
    (ridgeSupport168_suffix_011, ridgeSupport168_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 125
    ridgeSupport168_rest_011 ridgeSupport168_rest_012 ridgeSupport168_rest_016
    ridgeSupport168_011 ridgeSupport168_suffix_012 ridgeSupport168_011_decode ridgeSupport168_suffix_decode_012
theorem ridgeSupport168_suffix_decode_010 : PackedRawNatGrowth.readList 14 189 ridgeSupport168_rest_010 =
    (ridgeSupport168_suffix_010, ridgeSupport168_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 157
    ridgeSupport168_rest_010 ridgeSupport168_rest_011 ridgeSupport168_rest_016
    ridgeSupport168_010 ridgeSupport168_suffix_011 ridgeSupport168_010_decode ridgeSupport168_suffix_decode_011
theorem ridgeSupport168_suffix_decode_009 : PackedRawNatGrowth.readList 14 221 ridgeSupport168_rest_009 =
    (ridgeSupport168_suffix_009, ridgeSupport168_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 189
    ridgeSupport168_rest_009 ridgeSupport168_rest_010 ridgeSupport168_rest_016
    ridgeSupport168_009 ridgeSupport168_suffix_010 ridgeSupport168_009_decode ridgeSupport168_suffix_decode_010
theorem ridgeSupport168_suffix_decode_008 : PackedRawNatGrowth.readList 14 253 ridgeSupport168_rest_008 =
    (ridgeSupport168_suffix_008, ridgeSupport168_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 221
    ridgeSupport168_rest_008 ridgeSupport168_rest_009 ridgeSupport168_rest_016
    ridgeSupport168_008 ridgeSupport168_suffix_009 ridgeSupport168_008_decode ridgeSupport168_suffix_decode_009
theorem ridgeSupport168_suffix_decode_007 : PackedRawNatGrowth.readList 14 285 ridgeSupport168_rest_007 =
    (ridgeSupport168_suffix_007, ridgeSupport168_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 253
    ridgeSupport168_rest_007 ridgeSupport168_rest_008 ridgeSupport168_rest_016
    ridgeSupport168_007 ridgeSupport168_suffix_008 ridgeSupport168_007_decode ridgeSupport168_suffix_decode_008
theorem ridgeSupport168_suffix_decode_006 : PackedRawNatGrowth.readList 14 317 ridgeSupport168_rest_006 =
    (ridgeSupport168_suffix_006, ridgeSupport168_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 285
    ridgeSupport168_rest_006 ridgeSupport168_rest_007 ridgeSupport168_rest_016
    ridgeSupport168_006 ridgeSupport168_suffix_007 ridgeSupport168_006_decode ridgeSupport168_suffix_decode_007
theorem ridgeSupport168_suffix_decode_005 : PackedRawNatGrowth.readList 14 349 ridgeSupport168_rest_005 =
    (ridgeSupport168_suffix_005, ridgeSupport168_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 317
    ridgeSupport168_rest_005 ridgeSupport168_rest_006 ridgeSupport168_rest_016
    ridgeSupport168_005 ridgeSupport168_suffix_006 ridgeSupport168_005_decode ridgeSupport168_suffix_decode_006
theorem ridgeSupport168_suffix_decode_004 : PackedRawNatGrowth.readList 14 381 ridgeSupport168_rest_004 =
    (ridgeSupport168_suffix_004, ridgeSupport168_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 349
    ridgeSupport168_rest_004 ridgeSupport168_rest_005 ridgeSupport168_rest_016
    ridgeSupport168_004 ridgeSupport168_suffix_005 ridgeSupport168_004_decode ridgeSupport168_suffix_decode_005
theorem ridgeSupport168_suffix_decode_003 : PackedRawNatGrowth.readList 14 413 ridgeSupport168_rest_003 =
    (ridgeSupport168_suffix_003, ridgeSupport168_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 381
    ridgeSupport168_rest_003 ridgeSupport168_rest_004 ridgeSupport168_rest_016
    ridgeSupport168_003 ridgeSupport168_suffix_004 ridgeSupport168_003_decode ridgeSupport168_suffix_decode_004
theorem ridgeSupport168_suffix_decode_002 : PackedRawNatGrowth.readList 14 445 ridgeSupport168_rest_002 =
    (ridgeSupport168_suffix_002, ridgeSupport168_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 413
    ridgeSupport168_rest_002 ridgeSupport168_rest_003 ridgeSupport168_rest_016
    ridgeSupport168_002 ridgeSupport168_suffix_003 ridgeSupport168_002_decode ridgeSupport168_suffix_decode_003
theorem ridgeSupport168_suffix_decode_001 : PackedRawNatGrowth.readList 14 477 ridgeSupport168_rest_001 =
    (ridgeSupport168_suffix_001, ridgeSupport168_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 445
    ridgeSupport168_rest_001 ridgeSupport168_rest_002 ridgeSupport168_rest_016
    ridgeSupport168_001 ridgeSupport168_suffix_002 ridgeSupport168_001_decode ridgeSupport168_suffix_decode_002
theorem ridgeSupport168_suffix_decode_000 : PackedRawNatGrowth.readList 14 509 ridgeSupport168_rest_000 =
    (ridgeSupport168_suffix_000, ridgeSupport168_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 477
    ridgeSupport168_rest_000 ridgeSupport168_rest_001 ridgeSupport168_rest_016
    ridgeSupport168_000 ridgeSupport168_suffix_001 ridgeSupport168_000_decode ridgeSupport168_suffix_decode_001
theorem ridgeSupport168_eq : candidateRows 168 = ridgeSupport168_suffix_000 := by
  rw [ridgeSupport168_source]
  exact congrArg Prod.fst ridgeSupport168_suffix_decode_000
theorem ridgeTest_large_168 : ridgeTest 168 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport168_eq]
    simp only [ridgeSupport168_suffix_000, ridgeSupport168_suffix_001, ridgeSupport168_suffix_002, ridgeSupport168_suffix_003, ridgeSupport168_suffix_004, ridgeSupport168_suffix_005, ridgeSupport168_suffix_006, ridgeSupport168_suffix_007, ridgeSupport168_suffix_008, ridgeSupport168_suffix_009, ridgeSupport168_suffix_010, ridgeSupport168_suffix_011, ridgeSupport168_suffix_012, ridgeSupport168_suffix_013, ridgeSupport168_suffix_014, ridgeSupport168_suffix_015, ridgeSupport168_suffix_016, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport168_000_mask, ridgeSupport168_001_mask, ridgeSupport168_002_mask, ridgeSupport168_003_mask, ridgeSupport168_004_mask, ridgeSupport168_005_mask, ridgeSupport168_006_mask, ridgeSupport168_007_mask, ridgeSupport168_008_mask, ridgeSupport168_009_mask, ridgeSupport168_010_mask, ridgeSupport168_011_mask, ridgeSupport168_012_mask, ridgeSupport168_013_mask, ridgeSupport168_014_mask, ridgeSupport168_015_mask]
    decide +kernel
  · rw [ridgeSupport168_eq]
    simp only [ridgeSupport168_suffix_000, ridgeSupport168_suffix_001, ridgeSupport168_suffix_002, ridgeSupport168_suffix_003, ridgeSupport168_suffix_004, ridgeSupport168_suffix_005, ridgeSupport168_suffix_006, ridgeSupport168_suffix_007, ridgeSupport168_suffix_008, ridgeSupport168_suffix_009, ridgeSupport168_suffix_010, ridgeSupport168_suffix_011, ridgeSupport168_suffix_012, ridgeSupport168_suffix_013, ridgeSupport168_suffix_014, ridgeSupport168_suffix_015, ridgeSupport168_suffix_016, List.all_append, List.all_nil, ridgeSupport168_000_checked, ridgeSupport168_001_checked, ridgeSupport168_002_checked, ridgeSupport168_003_checked, ridgeSupport168_004_checked, ridgeSupport168_005_checked, ridgeSupport168_006_checked, ridgeSupport168_007_checked, ridgeSupport168_008_checked, ridgeSupport168_009_checked, ridgeSupport168_010_checked, ridgeSupport168_011_checked, ridgeSupport168_012_checked, ridgeSupport168_013_checked, ridgeSupport168_014_checked, ridgeSupport168_015_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase01
