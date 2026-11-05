module
prelude
public import RootedSixBase01GrowthCacheRidgeSupport146Part000
public import RootedSixBase01GrowthCacheRidgeSupport146Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport146_suffix_decode_016 : PackedRawNatGrowth.readList 14 0 ridgeSupport146_rest_016 =
    (ridgeSupport146_suffix_016, ridgeSupport146_rest_016) := by rfl
theorem ridgeSupport146_suffix_decode_015 : PackedRawNatGrowth.readList 14 29 ridgeSupport146_rest_015 =
    (ridgeSupport146_suffix_015, ridgeSupport146_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 29 0
    ridgeSupport146_rest_015 ridgeSupport146_rest_016 ridgeSupport146_rest_016
    ridgeSupport146_015 ridgeSupport146_suffix_016 ridgeSupport146_015_decode ridgeSupport146_suffix_decode_016
theorem ridgeSupport146_suffix_decode_014 : PackedRawNatGrowth.readList 14 61 ridgeSupport146_rest_014 =
    (ridgeSupport146_suffix_014, ridgeSupport146_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 29
    ridgeSupport146_rest_014 ridgeSupport146_rest_015 ridgeSupport146_rest_016
    ridgeSupport146_014 ridgeSupport146_suffix_015 ridgeSupport146_014_decode ridgeSupport146_suffix_decode_015
theorem ridgeSupport146_suffix_decode_013 : PackedRawNatGrowth.readList 14 93 ridgeSupport146_rest_013 =
    (ridgeSupport146_suffix_013, ridgeSupport146_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 61
    ridgeSupport146_rest_013 ridgeSupport146_rest_014 ridgeSupport146_rest_016
    ridgeSupport146_013 ridgeSupport146_suffix_014 ridgeSupport146_013_decode ridgeSupport146_suffix_decode_014
theorem ridgeSupport146_suffix_decode_012 : PackedRawNatGrowth.readList 14 125 ridgeSupport146_rest_012 =
    (ridgeSupport146_suffix_012, ridgeSupport146_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 93
    ridgeSupport146_rest_012 ridgeSupport146_rest_013 ridgeSupport146_rest_016
    ridgeSupport146_012 ridgeSupport146_suffix_013 ridgeSupport146_012_decode ridgeSupport146_suffix_decode_013
theorem ridgeSupport146_suffix_decode_011 : PackedRawNatGrowth.readList 14 157 ridgeSupport146_rest_011 =
    (ridgeSupport146_suffix_011, ridgeSupport146_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 125
    ridgeSupport146_rest_011 ridgeSupport146_rest_012 ridgeSupport146_rest_016
    ridgeSupport146_011 ridgeSupport146_suffix_012 ridgeSupport146_011_decode ridgeSupport146_suffix_decode_012
theorem ridgeSupport146_suffix_decode_010 : PackedRawNatGrowth.readList 14 189 ridgeSupport146_rest_010 =
    (ridgeSupport146_suffix_010, ridgeSupport146_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 157
    ridgeSupport146_rest_010 ridgeSupport146_rest_011 ridgeSupport146_rest_016
    ridgeSupport146_010 ridgeSupport146_suffix_011 ridgeSupport146_010_decode ridgeSupport146_suffix_decode_011
theorem ridgeSupport146_suffix_decode_009 : PackedRawNatGrowth.readList 14 221 ridgeSupport146_rest_009 =
    (ridgeSupport146_suffix_009, ridgeSupport146_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 189
    ridgeSupport146_rest_009 ridgeSupport146_rest_010 ridgeSupport146_rest_016
    ridgeSupport146_009 ridgeSupport146_suffix_010 ridgeSupport146_009_decode ridgeSupport146_suffix_decode_010
theorem ridgeSupport146_suffix_decode_008 : PackedRawNatGrowth.readList 14 253 ridgeSupport146_rest_008 =
    (ridgeSupport146_suffix_008, ridgeSupport146_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 221
    ridgeSupport146_rest_008 ridgeSupport146_rest_009 ridgeSupport146_rest_016
    ridgeSupport146_008 ridgeSupport146_suffix_009 ridgeSupport146_008_decode ridgeSupport146_suffix_decode_009
theorem ridgeSupport146_suffix_decode_007 : PackedRawNatGrowth.readList 14 285 ridgeSupport146_rest_007 =
    (ridgeSupport146_suffix_007, ridgeSupport146_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 253
    ridgeSupport146_rest_007 ridgeSupport146_rest_008 ridgeSupport146_rest_016
    ridgeSupport146_007 ridgeSupport146_suffix_008 ridgeSupport146_007_decode ridgeSupport146_suffix_decode_008
theorem ridgeSupport146_suffix_decode_006 : PackedRawNatGrowth.readList 14 317 ridgeSupport146_rest_006 =
    (ridgeSupport146_suffix_006, ridgeSupport146_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 285
    ridgeSupport146_rest_006 ridgeSupport146_rest_007 ridgeSupport146_rest_016
    ridgeSupport146_006 ridgeSupport146_suffix_007 ridgeSupport146_006_decode ridgeSupport146_suffix_decode_007
theorem ridgeSupport146_suffix_decode_005 : PackedRawNatGrowth.readList 14 349 ridgeSupport146_rest_005 =
    (ridgeSupport146_suffix_005, ridgeSupport146_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 317
    ridgeSupport146_rest_005 ridgeSupport146_rest_006 ridgeSupport146_rest_016
    ridgeSupport146_005 ridgeSupport146_suffix_006 ridgeSupport146_005_decode ridgeSupport146_suffix_decode_006
theorem ridgeSupport146_suffix_decode_004 : PackedRawNatGrowth.readList 14 381 ridgeSupport146_rest_004 =
    (ridgeSupport146_suffix_004, ridgeSupport146_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 349
    ridgeSupport146_rest_004 ridgeSupport146_rest_005 ridgeSupport146_rest_016
    ridgeSupport146_004 ridgeSupport146_suffix_005 ridgeSupport146_004_decode ridgeSupport146_suffix_decode_005
theorem ridgeSupport146_suffix_decode_003 : PackedRawNatGrowth.readList 14 413 ridgeSupport146_rest_003 =
    (ridgeSupport146_suffix_003, ridgeSupport146_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 381
    ridgeSupport146_rest_003 ridgeSupport146_rest_004 ridgeSupport146_rest_016
    ridgeSupport146_003 ridgeSupport146_suffix_004 ridgeSupport146_003_decode ridgeSupport146_suffix_decode_004
theorem ridgeSupport146_suffix_decode_002 : PackedRawNatGrowth.readList 14 445 ridgeSupport146_rest_002 =
    (ridgeSupport146_suffix_002, ridgeSupport146_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 413
    ridgeSupport146_rest_002 ridgeSupport146_rest_003 ridgeSupport146_rest_016
    ridgeSupport146_002 ridgeSupport146_suffix_003 ridgeSupport146_002_decode ridgeSupport146_suffix_decode_003
theorem ridgeSupport146_suffix_decode_001 : PackedRawNatGrowth.readList 14 477 ridgeSupport146_rest_001 =
    (ridgeSupport146_suffix_001, ridgeSupport146_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 445
    ridgeSupport146_rest_001 ridgeSupport146_rest_002 ridgeSupport146_rest_016
    ridgeSupport146_001 ridgeSupport146_suffix_002 ridgeSupport146_001_decode ridgeSupport146_suffix_decode_002
theorem ridgeSupport146_suffix_decode_000 : PackedRawNatGrowth.readList 14 509 ridgeSupport146_rest_000 =
    (ridgeSupport146_suffix_000, ridgeSupport146_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 477
    ridgeSupport146_rest_000 ridgeSupport146_rest_001 ridgeSupport146_rest_016
    ridgeSupport146_000 ridgeSupport146_suffix_001 ridgeSupport146_000_decode ridgeSupport146_suffix_decode_001
theorem ridgeSupport146_eq : candidateRows 146 = ridgeSupport146_suffix_000 := by
  rw [ridgeSupport146_source]
  exact congrArg Prod.fst ridgeSupport146_suffix_decode_000
theorem ridgeTest_large_146 : ridgeTest 146 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport146_eq]
    simp only [ridgeSupport146_suffix_000, ridgeSupport146_suffix_001, ridgeSupport146_suffix_002, ridgeSupport146_suffix_003, ridgeSupport146_suffix_004, ridgeSupport146_suffix_005, ridgeSupport146_suffix_006, ridgeSupport146_suffix_007, ridgeSupport146_suffix_008, ridgeSupport146_suffix_009, ridgeSupport146_suffix_010, ridgeSupport146_suffix_011, ridgeSupport146_suffix_012, ridgeSupport146_suffix_013, ridgeSupport146_suffix_014, ridgeSupport146_suffix_015, ridgeSupport146_suffix_016, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport146_000_mask, ridgeSupport146_001_mask, ridgeSupport146_002_mask, ridgeSupport146_003_mask, ridgeSupport146_004_mask, ridgeSupport146_005_mask, ridgeSupport146_006_mask, ridgeSupport146_007_mask, ridgeSupport146_008_mask, ridgeSupport146_009_mask, ridgeSupport146_010_mask, ridgeSupport146_011_mask, ridgeSupport146_012_mask, ridgeSupport146_013_mask, ridgeSupport146_014_mask, ridgeSupport146_015_mask]
    decide +kernel
  · rw [ridgeSupport146_eq]
    simp only [ridgeSupport146_suffix_000, ridgeSupport146_suffix_001, ridgeSupport146_suffix_002, ridgeSupport146_suffix_003, ridgeSupport146_suffix_004, ridgeSupport146_suffix_005, ridgeSupport146_suffix_006, ridgeSupport146_suffix_007, ridgeSupport146_suffix_008, ridgeSupport146_suffix_009, ridgeSupport146_suffix_010, ridgeSupport146_suffix_011, ridgeSupport146_suffix_012, ridgeSupport146_suffix_013, ridgeSupport146_suffix_014, ridgeSupport146_suffix_015, ridgeSupport146_suffix_016, List.all_append, List.all_nil, ridgeSupport146_000_checked, ridgeSupport146_001_checked, ridgeSupport146_002_checked, ridgeSupport146_003_checked, ridgeSupport146_004_checked, ridgeSupport146_005_checked, ridgeSupport146_006_checked, ridgeSupport146_007_checked, ridgeSupport146_008_checked, ridgeSupport146_009_checked, ridgeSupport146_010_checked, ridgeSupport146_011_checked, ridgeSupport146_012_checked, ridgeSupport146_013_checked, ridgeSupport146_014_checked, ridgeSupport146_015_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase01
