module
prelude
public import RootedSixBase01GrowthCacheRidgeSupport560Part000
public import RootedSixBase01GrowthCacheRidgeSupport560Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport560_suffix_decode_016 : PackedRawNatGrowth.readList 14 0 ridgeSupport560_rest_016 =
    (ridgeSupport560_suffix_016, ridgeSupport560_rest_016) := by rfl
theorem ridgeSupport560_suffix_decode_015 : PackedRawNatGrowth.readList 14 29 ridgeSupport560_rest_015 =
    (ridgeSupport560_suffix_015, ridgeSupport560_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 29 0
    ridgeSupport560_rest_015 ridgeSupport560_rest_016 ridgeSupport560_rest_016
    ridgeSupport560_015 ridgeSupport560_suffix_016 ridgeSupport560_015_decode ridgeSupport560_suffix_decode_016
theorem ridgeSupport560_suffix_decode_014 : PackedRawNatGrowth.readList 14 61 ridgeSupport560_rest_014 =
    (ridgeSupport560_suffix_014, ridgeSupport560_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 29
    ridgeSupport560_rest_014 ridgeSupport560_rest_015 ridgeSupport560_rest_016
    ridgeSupport560_014 ridgeSupport560_suffix_015 ridgeSupport560_014_decode ridgeSupport560_suffix_decode_015
theorem ridgeSupport560_suffix_decode_013 : PackedRawNatGrowth.readList 14 93 ridgeSupport560_rest_013 =
    (ridgeSupport560_suffix_013, ridgeSupport560_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 61
    ridgeSupport560_rest_013 ridgeSupport560_rest_014 ridgeSupport560_rest_016
    ridgeSupport560_013 ridgeSupport560_suffix_014 ridgeSupport560_013_decode ridgeSupport560_suffix_decode_014
theorem ridgeSupport560_suffix_decode_012 : PackedRawNatGrowth.readList 14 125 ridgeSupport560_rest_012 =
    (ridgeSupport560_suffix_012, ridgeSupport560_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 93
    ridgeSupport560_rest_012 ridgeSupport560_rest_013 ridgeSupport560_rest_016
    ridgeSupport560_012 ridgeSupport560_suffix_013 ridgeSupport560_012_decode ridgeSupport560_suffix_decode_013
theorem ridgeSupport560_suffix_decode_011 : PackedRawNatGrowth.readList 14 157 ridgeSupport560_rest_011 =
    (ridgeSupport560_suffix_011, ridgeSupport560_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 125
    ridgeSupport560_rest_011 ridgeSupport560_rest_012 ridgeSupport560_rest_016
    ridgeSupport560_011 ridgeSupport560_suffix_012 ridgeSupport560_011_decode ridgeSupport560_suffix_decode_012
theorem ridgeSupport560_suffix_decode_010 : PackedRawNatGrowth.readList 14 189 ridgeSupport560_rest_010 =
    (ridgeSupport560_suffix_010, ridgeSupport560_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 157
    ridgeSupport560_rest_010 ridgeSupport560_rest_011 ridgeSupport560_rest_016
    ridgeSupport560_010 ridgeSupport560_suffix_011 ridgeSupport560_010_decode ridgeSupport560_suffix_decode_011
theorem ridgeSupport560_suffix_decode_009 : PackedRawNatGrowth.readList 14 221 ridgeSupport560_rest_009 =
    (ridgeSupport560_suffix_009, ridgeSupport560_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 189
    ridgeSupport560_rest_009 ridgeSupport560_rest_010 ridgeSupport560_rest_016
    ridgeSupport560_009 ridgeSupport560_suffix_010 ridgeSupport560_009_decode ridgeSupport560_suffix_decode_010
theorem ridgeSupport560_suffix_decode_008 : PackedRawNatGrowth.readList 14 253 ridgeSupport560_rest_008 =
    (ridgeSupport560_suffix_008, ridgeSupport560_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 221
    ridgeSupport560_rest_008 ridgeSupport560_rest_009 ridgeSupport560_rest_016
    ridgeSupport560_008 ridgeSupport560_suffix_009 ridgeSupport560_008_decode ridgeSupport560_suffix_decode_009
theorem ridgeSupport560_suffix_decode_007 : PackedRawNatGrowth.readList 14 285 ridgeSupport560_rest_007 =
    (ridgeSupport560_suffix_007, ridgeSupport560_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 253
    ridgeSupport560_rest_007 ridgeSupport560_rest_008 ridgeSupport560_rest_016
    ridgeSupport560_007 ridgeSupport560_suffix_008 ridgeSupport560_007_decode ridgeSupport560_suffix_decode_008
theorem ridgeSupport560_suffix_decode_006 : PackedRawNatGrowth.readList 14 317 ridgeSupport560_rest_006 =
    (ridgeSupport560_suffix_006, ridgeSupport560_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 285
    ridgeSupport560_rest_006 ridgeSupport560_rest_007 ridgeSupport560_rest_016
    ridgeSupport560_006 ridgeSupport560_suffix_007 ridgeSupport560_006_decode ridgeSupport560_suffix_decode_007
theorem ridgeSupport560_suffix_decode_005 : PackedRawNatGrowth.readList 14 349 ridgeSupport560_rest_005 =
    (ridgeSupport560_suffix_005, ridgeSupport560_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 317
    ridgeSupport560_rest_005 ridgeSupport560_rest_006 ridgeSupport560_rest_016
    ridgeSupport560_005 ridgeSupport560_suffix_006 ridgeSupport560_005_decode ridgeSupport560_suffix_decode_006
theorem ridgeSupport560_suffix_decode_004 : PackedRawNatGrowth.readList 14 381 ridgeSupport560_rest_004 =
    (ridgeSupport560_suffix_004, ridgeSupport560_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 349
    ridgeSupport560_rest_004 ridgeSupport560_rest_005 ridgeSupport560_rest_016
    ridgeSupport560_004 ridgeSupport560_suffix_005 ridgeSupport560_004_decode ridgeSupport560_suffix_decode_005
theorem ridgeSupport560_suffix_decode_003 : PackedRawNatGrowth.readList 14 413 ridgeSupport560_rest_003 =
    (ridgeSupport560_suffix_003, ridgeSupport560_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 381
    ridgeSupport560_rest_003 ridgeSupport560_rest_004 ridgeSupport560_rest_016
    ridgeSupport560_003 ridgeSupport560_suffix_004 ridgeSupport560_003_decode ridgeSupport560_suffix_decode_004
theorem ridgeSupport560_suffix_decode_002 : PackedRawNatGrowth.readList 14 445 ridgeSupport560_rest_002 =
    (ridgeSupport560_suffix_002, ridgeSupport560_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 413
    ridgeSupport560_rest_002 ridgeSupport560_rest_003 ridgeSupport560_rest_016
    ridgeSupport560_002 ridgeSupport560_suffix_003 ridgeSupport560_002_decode ridgeSupport560_suffix_decode_003
theorem ridgeSupport560_suffix_decode_001 : PackedRawNatGrowth.readList 14 477 ridgeSupport560_rest_001 =
    (ridgeSupport560_suffix_001, ridgeSupport560_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 445
    ridgeSupport560_rest_001 ridgeSupport560_rest_002 ridgeSupport560_rest_016
    ridgeSupport560_001 ridgeSupport560_suffix_002 ridgeSupport560_001_decode ridgeSupport560_suffix_decode_002
theorem ridgeSupport560_suffix_decode_000 : PackedRawNatGrowth.readList 14 509 ridgeSupport560_rest_000 =
    (ridgeSupport560_suffix_000, ridgeSupport560_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 477
    ridgeSupport560_rest_000 ridgeSupport560_rest_001 ridgeSupport560_rest_016
    ridgeSupport560_000 ridgeSupport560_suffix_001 ridgeSupport560_000_decode ridgeSupport560_suffix_decode_001
theorem ridgeSupport560_eq : candidateRows 560 = ridgeSupport560_suffix_000 := by
  rw [ridgeSupport560_source]
  exact congrArg Prod.fst ridgeSupport560_suffix_decode_000
theorem ridgeTest_large_560 : ridgeTest 560 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport560_eq]
    simp only [ridgeSupport560_suffix_000, ridgeSupport560_suffix_001, ridgeSupport560_suffix_002, ridgeSupport560_suffix_003, ridgeSupport560_suffix_004, ridgeSupport560_suffix_005, ridgeSupport560_suffix_006, ridgeSupport560_suffix_007, ridgeSupport560_suffix_008, ridgeSupport560_suffix_009, ridgeSupport560_suffix_010, ridgeSupport560_suffix_011, ridgeSupport560_suffix_012, ridgeSupport560_suffix_013, ridgeSupport560_suffix_014, ridgeSupport560_suffix_015, ridgeSupport560_suffix_016, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport560_000_mask, ridgeSupport560_001_mask, ridgeSupport560_002_mask, ridgeSupport560_003_mask, ridgeSupport560_004_mask, ridgeSupport560_005_mask, ridgeSupport560_006_mask, ridgeSupport560_007_mask, ridgeSupport560_008_mask, ridgeSupport560_009_mask, ridgeSupport560_010_mask, ridgeSupport560_011_mask, ridgeSupport560_012_mask, ridgeSupport560_013_mask, ridgeSupport560_014_mask, ridgeSupport560_015_mask]
    decide +kernel
  · rw [ridgeSupport560_eq]
    simp only [ridgeSupport560_suffix_000, ridgeSupport560_suffix_001, ridgeSupport560_suffix_002, ridgeSupport560_suffix_003, ridgeSupport560_suffix_004, ridgeSupport560_suffix_005, ridgeSupport560_suffix_006, ridgeSupport560_suffix_007, ridgeSupport560_suffix_008, ridgeSupport560_suffix_009, ridgeSupport560_suffix_010, ridgeSupport560_suffix_011, ridgeSupport560_suffix_012, ridgeSupport560_suffix_013, ridgeSupport560_suffix_014, ridgeSupport560_suffix_015, ridgeSupport560_suffix_016, List.all_append, List.all_nil, ridgeSupport560_000_checked, ridgeSupport560_001_checked, ridgeSupport560_002_checked, ridgeSupport560_003_checked, ridgeSupport560_004_checked, ridgeSupport560_005_checked, ridgeSupport560_006_checked, ridgeSupport560_007_checked, ridgeSupport560_008_checked, ridgeSupport560_009_checked, ridgeSupport560_010_checked, ridgeSupport560_011_checked, ridgeSupport560_012_checked, ridgeSupport560_013_checked, ridgeSupport560_014_checked, ridgeSupport560_015_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase01
