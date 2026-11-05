module
prelude
public import RootedSixBase01GrowthCacheRidgeSupport176Part000
public import RootedSixBase01GrowthCacheRidgeSupport176Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport176_suffix_decode_016 : PackedRawNatGrowth.readList 14 0 ridgeSupport176_rest_016 =
    (ridgeSupport176_suffix_016, ridgeSupport176_rest_016) := by rfl
theorem ridgeSupport176_suffix_decode_015 : PackedRawNatGrowth.readList 14 29 ridgeSupport176_rest_015 =
    (ridgeSupport176_suffix_015, ridgeSupport176_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 29 0
    ridgeSupport176_rest_015 ridgeSupport176_rest_016 ridgeSupport176_rest_016
    ridgeSupport176_015 ridgeSupport176_suffix_016 ridgeSupport176_015_decode ridgeSupport176_suffix_decode_016
theorem ridgeSupport176_suffix_decode_014 : PackedRawNatGrowth.readList 14 61 ridgeSupport176_rest_014 =
    (ridgeSupport176_suffix_014, ridgeSupport176_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 29
    ridgeSupport176_rest_014 ridgeSupport176_rest_015 ridgeSupport176_rest_016
    ridgeSupport176_014 ridgeSupport176_suffix_015 ridgeSupport176_014_decode ridgeSupport176_suffix_decode_015
theorem ridgeSupport176_suffix_decode_013 : PackedRawNatGrowth.readList 14 93 ridgeSupport176_rest_013 =
    (ridgeSupport176_suffix_013, ridgeSupport176_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 61
    ridgeSupport176_rest_013 ridgeSupport176_rest_014 ridgeSupport176_rest_016
    ridgeSupport176_013 ridgeSupport176_suffix_014 ridgeSupport176_013_decode ridgeSupport176_suffix_decode_014
theorem ridgeSupport176_suffix_decode_012 : PackedRawNatGrowth.readList 14 125 ridgeSupport176_rest_012 =
    (ridgeSupport176_suffix_012, ridgeSupport176_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 93
    ridgeSupport176_rest_012 ridgeSupport176_rest_013 ridgeSupport176_rest_016
    ridgeSupport176_012 ridgeSupport176_suffix_013 ridgeSupport176_012_decode ridgeSupport176_suffix_decode_013
theorem ridgeSupport176_suffix_decode_011 : PackedRawNatGrowth.readList 14 157 ridgeSupport176_rest_011 =
    (ridgeSupport176_suffix_011, ridgeSupport176_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 125
    ridgeSupport176_rest_011 ridgeSupport176_rest_012 ridgeSupport176_rest_016
    ridgeSupport176_011 ridgeSupport176_suffix_012 ridgeSupport176_011_decode ridgeSupport176_suffix_decode_012
theorem ridgeSupport176_suffix_decode_010 : PackedRawNatGrowth.readList 14 189 ridgeSupport176_rest_010 =
    (ridgeSupport176_suffix_010, ridgeSupport176_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 157
    ridgeSupport176_rest_010 ridgeSupport176_rest_011 ridgeSupport176_rest_016
    ridgeSupport176_010 ridgeSupport176_suffix_011 ridgeSupport176_010_decode ridgeSupport176_suffix_decode_011
theorem ridgeSupport176_suffix_decode_009 : PackedRawNatGrowth.readList 14 221 ridgeSupport176_rest_009 =
    (ridgeSupport176_suffix_009, ridgeSupport176_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 189
    ridgeSupport176_rest_009 ridgeSupport176_rest_010 ridgeSupport176_rest_016
    ridgeSupport176_009 ridgeSupport176_suffix_010 ridgeSupport176_009_decode ridgeSupport176_suffix_decode_010
theorem ridgeSupport176_suffix_decode_008 : PackedRawNatGrowth.readList 14 253 ridgeSupport176_rest_008 =
    (ridgeSupport176_suffix_008, ridgeSupport176_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 221
    ridgeSupport176_rest_008 ridgeSupport176_rest_009 ridgeSupport176_rest_016
    ridgeSupport176_008 ridgeSupport176_suffix_009 ridgeSupport176_008_decode ridgeSupport176_suffix_decode_009
theorem ridgeSupport176_suffix_decode_007 : PackedRawNatGrowth.readList 14 285 ridgeSupport176_rest_007 =
    (ridgeSupport176_suffix_007, ridgeSupport176_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 253
    ridgeSupport176_rest_007 ridgeSupport176_rest_008 ridgeSupport176_rest_016
    ridgeSupport176_007 ridgeSupport176_suffix_008 ridgeSupport176_007_decode ridgeSupport176_suffix_decode_008
theorem ridgeSupport176_suffix_decode_006 : PackedRawNatGrowth.readList 14 317 ridgeSupport176_rest_006 =
    (ridgeSupport176_suffix_006, ridgeSupport176_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 285
    ridgeSupport176_rest_006 ridgeSupport176_rest_007 ridgeSupport176_rest_016
    ridgeSupport176_006 ridgeSupport176_suffix_007 ridgeSupport176_006_decode ridgeSupport176_suffix_decode_007
theorem ridgeSupport176_suffix_decode_005 : PackedRawNatGrowth.readList 14 349 ridgeSupport176_rest_005 =
    (ridgeSupport176_suffix_005, ridgeSupport176_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 317
    ridgeSupport176_rest_005 ridgeSupport176_rest_006 ridgeSupport176_rest_016
    ridgeSupport176_005 ridgeSupport176_suffix_006 ridgeSupport176_005_decode ridgeSupport176_suffix_decode_006
theorem ridgeSupport176_suffix_decode_004 : PackedRawNatGrowth.readList 14 381 ridgeSupport176_rest_004 =
    (ridgeSupport176_suffix_004, ridgeSupport176_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 349
    ridgeSupport176_rest_004 ridgeSupport176_rest_005 ridgeSupport176_rest_016
    ridgeSupport176_004 ridgeSupport176_suffix_005 ridgeSupport176_004_decode ridgeSupport176_suffix_decode_005
theorem ridgeSupport176_suffix_decode_003 : PackedRawNatGrowth.readList 14 413 ridgeSupport176_rest_003 =
    (ridgeSupport176_suffix_003, ridgeSupport176_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 381
    ridgeSupport176_rest_003 ridgeSupport176_rest_004 ridgeSupport176_rest_016
    ridgeSupport176_003 ridgeSupport176_suffix_004 ridgeSupport176_003_decode ridgeSupport176_suffix_decode_004
theorem ridgeSupport176_suffix_decode_002 : PackedRawNatGrowth.readList 14 445 ridgeSupport176_rest_002 =
    (ridgeSupport176_suffix_002, ridgeSupport176_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 413
    ridgeSupport176_rest_002 ridgeSupport176_rest_003 ridgeSupport176_rest_016
    ridgeSupport176_002 ridgeSupport176_suffix_003 ridgeSupport176_002_decode ridgeSupport176_suffix_decode_003
theorem ridgeSupport176_suffix_decode_001 : PackedRawNatGrowth.readList 14 477 ridgeSupport176_rest_001 =
    (ridgeSupport176_suffix_001, ridgeSupport176_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 445
    ridgeSupport176_rest_001 ridgeSupport176_rest_002 ridgeSupport176_rest_016
    ridgeSupport176_001 ridgeSupport176_suffix_002 ridgeSupport176_001_decode ridgeSupport176_suffix_decode_002
theorem ridgeSupport176_suffix_decode_000 : PackedRawNatGrowth.readList 14 509 ridgeSupport176_rest_000 =
    (ridgeSupport176_suffix_000, ridgeSupport176_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 477
    ridgeSupport176_rest_000 ridgeSupport176_rest_001 ridgeSupport176_rest_016
    ridgeSupport176_000 ridgeSupport176_suffix_001 ridgeSupport176_000_decode ridgeSupport176_suffix_decode_001
theorem ridgeSupport176_eq : candidateRows 176 = ridgeSupport176_suffix_000 := by
  rw [ridgeSupport176_source]
  exact congrArg Prod.fst ridgeSupport176_suffix_decode_000
theorem ridgeTest_large_176 : ridgeTest 176 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport176_eq]
    simp only [ridgeSupport176_suffix_000, ridgeSupport176_suffix_001, ridgeSupport176_suffix_002, ridgeSupport176_suffix_003, ridgeSupport176_suffix_004, ridgeSupport176_suffix_005, ridgeSupport176_suffix_006, ridgeSupport176_suffix_007, ridgeSupport176_suffix_008, ridgeSupport176_suffix_009, ridgeSupport176_suffix_010, ridgeSupport176_suffix_011, ridgeSupport176_suffix_012, ridgeSupport176_suffix_013, ridgeSupport176_suffix_014, ridgeSupport176_suffix_015, ridgeSupport176_suffix_016, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport176_000_mask, ridgeSupport176_001_mask, ridgeSupport176_002_mask, ridgeSupport176_003_mask, ridgeSupport176_004_mask, ridgeSupport176_005_mask, ridgeSupport176_006_mask, ridgeSupport176_007_mask, ridgeSupport176_008_mask, ridgeSupport176_009_mask, ridgeSupport176_010_mask, ridgeSupport176_011_mask, ridgeSupport176_012_mask, ridgeSupport176_013_mask, ridgeSupport176_014_mask, ridgeSupport176_015_mask]
    decide +kernel
  · rw [ridgeSupport176_eq]
    simp only [ridgeSupport176_suffix_000, ridgeSupport176_suffix_001, ridgeSupport176_suffix_002, ridgeSupport176_suffix_003, ridgeSupport176_suffix_004, ridgeSupport176_suffix_005, ridgeSupport176_suffix_006, ridgeSupport176_suffix_007, ridgeSupport176_suffix_008, ridgeSupport176_suffix_009, ridgeSupport176_suffix_010, ridgeSupport176_suffix_011, ridgeSupport176_suffix_012, ridgeSupport176_suffix_013, ridgeSupport176_suffix_014, ridgeSupport176_suffix_015, ridgeSupport176_suffix_016, List.all_append, List.all_nil, ridgeSupport176_000_checked, ridgeSupport176_001_checked, ridgeSupport176_002_checked, ridgeSupport176_003_checked, ridgeSupport176_004_checked, ridgeSupport176_005_checked, ridgeSupport176_006_checked, ridgeSupport176_007_checked, ridgeSupport176_008_checked, ridgeSupport176_009_checked, ridgeSupport176_010_checked, ridgeSupport176_011_checked, ridgeSupport176_012_checked, ridgeSupport176_013_checked, ridgeSupport176_014_checked, ridgeSupport176_015_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase01
