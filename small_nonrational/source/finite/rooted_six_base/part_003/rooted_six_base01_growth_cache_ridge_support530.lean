module
prelude
public import RootedSixBase01GrowthCacheRidgeSupport530Part000
public import RootedSixBase01GrowthCacheRidgeSupport530Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport530_suffix_decode_016 : PackedRawNatGrowth.readList 14 0 ridgeSupport530_rest_016 =
    (ridgeSupport530_suffix_016, ridgeSupport530_rest_016) := by rfl
theorem ridgeSupport530_suffix_decode_015 : PackedRawNatGrowth.readList 14 29 ridgeSupport530_rest_015 =
    (ridgeSupport530_suffix_015, ridgeSupport530_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 29 0
    ridgeSupport530_rest_015 ridgeSupport530_rest_016 ridgeSupport530_rest_016
    ridgeSupport530_015 ridgeSupport530_suffix_016 ridgeSupport530_015_decode ridgeSupport530_suffix_decode_016
theorem ridgeSupport530_suffix_decode_014 : PackedRawNatGrowth.readList 14 61 ridgeSupport530_rest_014 =
    (ridgeSupport530_suffix_014, ridgeSupport530_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 29
    ridgeSupport530_rest_014 ridgeSupport530_rest_015 ridgeSupport530_rest_016
    ridgeSupport530_014 ridgeSupport530_suffix_015 ridgeSupport530_014_decode ridgeSupport530_suffix_decode_015
theorem ridgeSupport530_suffix_decode_013 : PackedRawNatGrowth.readList 14 93 ridgeSupport530_rest_013 =
    (ridgeSupport530_suffix_013, ridgeSupport530_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 61
    ridgeSupport530_rest_013 ridgeSupport530_rest_014 ridgeSupport530_rest_016
    ridgeSupport530_013 ridgeSupport530_suffix_014 ridgeSupport530_013_decode ridgeSupport530_suffix_decode_014
theorem ridgeSupport530_suffix_decode_012 : PackedRawNatGrowth.readList 14 125 ridgeSupport530_rest_012 =
    (ridgeSupport530_suffix_012, ridgeSupport530_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 93
    ridgeSupport530_rest_012 ridgeSupport530_rest_013 ridgeSupport530_rest_016
    ridgeSupport530_012 ridgeSupport530_suffix_013 ridgeSupport530_012_decode ridgeSupport530_suffix_decode_013
theorem ridgeSupport530_suffix_decode_011 : PackedRawNatGrowth.readList 14 157 ridgeSupport530_rest_011 =
    (ridgeSupport530_suffix_011, ridgeSupport530_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 125
    ridgeSupport530_rest_011 ridgeSupport530_rest_012 ridgeSupport530_rest_016
    ridgeSupport530_011 ridgeSupport530_suffix_012 ridgeSupport530_011_decode ridgeSupport530_suffix_decode_012
theorem ridgeSupport530_suffix_decode_010 : PackedRawNatGrowth.readList 14 189 ridgeSupport530_rest_010 =
    (ridgeSupport530_suffix_010, ridgeSupport530_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 157
    ridgeSupport530_rest_010 ridgeSupport530_rest_011 ridgeSupport530_rest_016
    ridgeSupport530_010 ridgeSupport530_suffix_011 ridgeSupport530_010_decode ridgeSupport530_suffix_decode_011
theorem ridgeSupport530_suffix_decode_009 : PackedRawNatGrowth.readList 14 221 ridgeSupport530_rest_009 =
    (ridgeSupport530_suffix_009, ridgeSupport530_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 189
    ridgeSupport530_rest_009 ridgeSupport530_rest_010 ridgeSupport530_rest_016
    ridgeSupport530_009 ridgeSupport530_suffix_010 ridgeSupport530_009_decode ridgeSupport530_suffix_decode_010
theorem ridgeSupport530_suffix_decode_008 : PackedRawNatGrowth.readList 14 253 ridgeSupport530_rest_008 =
    (ridgeSupport530_suffix_008, ridgeSupport530_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 221
    ridgeSupport530_rest_008 ridgeSupport530_rest_009 ridgeSupport530_rest_016
    ridgeSupport530_008 ridgeSupport530_suffix_009 ridgeSupport530_008_decode ridgeSupport530_suffix_decode_009
theorem ridgeSupport530_suffix_decode_007 : PackedRawNatGrowth.readList 14 285 ridgeSupport530_rest_007 =
    (ridgeSupport530_suffix_007, ridgeSupport530_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 253
    ridgeSupport530_rest_007 ridgeSupport530_rest_008 ridgeSupport530_rest_016
    ridgeSupport530_007 ridgeSupport530_suffix_008 ridgeSupport530_007_decode ridgeSupport530_suffix_decode_008
theorem ridgeSupport530_suffix_decode_006 : PackedRawNatGrowth.readList 14 317 ridgeSupport530_rest_006 =
    (ridgeSupport530_suffix_006, ridgeSupport530_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 285
    ridgeSupport530_rest_006 ridgeSupport530_rest_007 ridgeSupport530_rest_016
    ridgeSupport530_006 ridgeSupport530_suffix_007 ridgeSupport530_006_decode ridgeSupport530_suffix_decode_007
theorem ridgeSupport530_suffix_decode_005 : PackedRawNatGrowth.readList 14 349 ridgeSupport530_rest_005 =
    (ridgeSupport530_suffix_005, ridgeSupport530_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 317
    ridgeSupport530_rest_005 ridgeSupport530_rest_006 ridgeSupport530_rest_016
    ridgeSupport530_005 ridgeSupport530_suffix_006 ridgeSupport530_005_decode ridgeSupport530_suffix_decode_006
theorem ridgeSupport530_suffix_decode_004 : PackedRawNatGrowth.readList 14 381 ridgeSupport530_rest_004 =
    (ridgeSupport530_suffix_004, ridgeSupport530_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 349
    ridgeSupport530_rest_004 ridgeSupport530_rest_005 ridgeSupport530_rest_016
    ridgeSupport530_004 ridgeSupport530_suffix_005 ridgeSupport530_004_decode ridgeSupport530_suffix_decode_005
theorem ridgeSupport530_suffix_decode_003 : PackedRawNatGrowth.readList 14 413 ridgeSupport530_rest_003 =
    (ridgeSupport530_suffix_003, ridgeSupport530_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 381
    ridgeSupport530_rest_003 ridgeSupport530_rest_004 ridgeSupport530_rest_016
    ridgeSupport530_003 ridgeSupport530_suffix_004 ridgeSupport530_003_decode ridgeSupport530_suffix_decode_004
theorem ridgeSupport530_suffix_decode_002 : PackedRawNatGrowth.readList 14 445 ridgeSupport530_rest_002 =
    (ridgeSupport530_suffix_002, ridgeSupport530_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 413
    ridgeSupport530_rest_002 ridgeSupport530_rest_003 ridgeSupport530_rest_016
    ridgeSupport530_002 ridgeSupport530_suffix_003 ridgeSupport530_002_decode ridgeSupport530_suffix_decode_003
theorem ridgeSupport530_suffix_decode_001 : PackedRawNatGrowth.readList 14 477 ridgeSupport530_rest_001 =
    (ridgeSupport530_suffix_001, ridgeSupport530_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 445
    ridgeSupport530_rest_001 ridgeSupport530_rest_002 ridgeSupport530_rest_016
    ridgeSupport530_001 ridgeSupport530_suffix_002 ridgeSupport530_001_decode ridgeSupport530_suffix_decode_002
theorem ridgeSupport530_suffix_decode_000 : PackedRawNatGrowth.readList 14 509 ridgeSupport530_rest_000 =
    (ridgeSupport530_suffix_000, ridgeSupport530_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 477
    ridgeSupport530_rest_000 ridgeSupport530_rest_001 ridgeSupport530_rest_016
    ridgeSupport530_000 ridgeSupport530_suffix_001 ridgeSupport530_000_decode ridgeSupport530_suffix_decode_001
theorem ridgeSupport530_eq : candidateRows 530 = ridgeSupport530_suffix_000 := by
  rw [ridgeSupport530_source]
  exact congrArg Prod.fst ridgeSupport530_suffix_decode_000
theorem ridgeTest_large_530 : ridgeTest 530 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport530_eq]
    simp only [ridgeSupport530_suffix_000, ridgeSupport530_suffix_001, ridgeSupport530_suffix_002, ridgeSupport530_suffix_003, ridgeSupport530_suffix_004, ridgeSupport530_suffix_005, ridgeSupport530_suffix_006, ridgeSupport530_suffix_007, ridgeSupport530_suffix_008, ridgeSupport530_suffix_009, ridgeSupport530_suffix_010, ridgeSupport530_suffix_011, ridgeSupport530_suffix_012, ridgeSupport530_suffix_013, ridgeSupport530_suffix_014, ridgeSupport530_suffix_015, ridgeSupport530_suffix_016, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport530_000_mask, ridgeSupport530_001_mask, ridgeSupport530_002_mask, ridgeSupport530_003_mask, ridgeSupport530_004_mask, ridgeSupport530_005_mask, ridgeSupport530_006_mask, ridgeSupport530_007_mask, ridgeSupport530_008_mask, ridgeSupport530_009_mask, ridgeSupport530_010_mask, ridgeSupport530_011_mask, ridgeSupport530_012_mask, ridgeSupport530_013_mask, ridgeSupport530_014_mask, ridgeSupport530_015_mask]
    decide +kernel
  · rw [ridgeSupport530_eq]
    simp only [ridgeSupport530_suffix_000, ridgeSupport530_suffix_001, ridgeSupport530_suffix_002, ridgeSupport530_suffix_003, ridgeSupport530_suffix_004, ridgeSupport530_suffix_005, ridgeSupport530_suffix_006, ridgeSupport530_suffix_007, ridgeSupport530_suffix_008, ridgeSupport530_suffix_009, ridgeSupport530_suffix_010, ridgeSupport530_suffix_011, ridgeSupport530_suffix_012, ridgeSupport530_suffix_013, ridgeSupport530_suffix_014, ridgeSupport530_suffix_015, ridgeSupport530_suffix_016, List.all_append, List.all_nil, ridgeSupport530_000_checked, ridgeSupport530_001_checked, ridgeSupport530_002_checked, ridgeSupport530_003_checked, ridgeSupport530_004_checked, ridgeSupport530_005_checked, ridgeSupport530_006_checked, ridgeSupport530_007_checked, ridgeSupport530_008_checked, ridgeSupport530_009_checked, ridgeSupport530_010_checked, ridgeSupport530_011_checked, ridgeSupport530_012_checked, ridgeSupport530_013_checked, ridgeSupport530_014_checked, ridgeSupport530_015_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase01
