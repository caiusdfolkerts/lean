module
prelude
public import RootedSixBase01GrowthCacheRidgeSupport274Part000
public import RootedSixBase01GrowthCacheRidgeSupport274Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport274_suffix_decode_016 : PackedRawNatGrowth.readList 14 0 ridgeSupport274_rest_016 =
    (ridgeSupport274_suffix_016, ridgeSupport274_rest_016) := by rfl
theorem ridgeSupport274_suffix_decode_015 : PackedRawNatGrowth.readList 14 29 ridgeSupport274_rest_015 =
    (ridgeSupport274_suffix_015, ridgeSupport274_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 29 0
    ridgeSupport274_rest_015 ridgeSupport274_rest_016 ridgeSupport274_rest_016
    ridgeSupport274_015 ridgeSupport274_suffix_016 ridgeSupport274_015_decode ridgeSupport274_suffix_decode_016
theorem ridgeSupport274_suffix_decode_014 : PackedRawNatGrowth.readList 14 61 ridgeSupport274_rest_014 =
    (ridgeSupport274_suffix_014, ridgeSupport274_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 29
    ridgeSupport274_rest_014 ridgeSupport274_rest_015 ridgeSupport274_rest_016
    ridgeSupport274_014 ridgeSupport274_suffix_015 ridgeSupport274_014_decode ridgeSupport274_suffix_decode_015
theorem ridgeSupport274_suffix_decode_013 : PackedRawNatGrowth.readList 14 93 ridgeSupport274_rest_013 =
    (ridgeSupport274_suffix_013, ridgeSupport274_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 61
    ridgeSupport274_rest_013 ridgeSupport274_rest_014 ridgeSupport274_rest_016
    ridgeSupport274_013 ridgeSupport274_suffix_014 ridgeSupport274_013_decode ridgeSupport274_suffix_decode_014
theorem ridgeSupport274_suffix_decode_012 : PackedRawNatGrowth.readList 14 125 ridgeSupport274_rest_012 =
    (ridgeSupport274_suffix_012, ridgeSupport274_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 93
    ridgeSupport274_rest_012 ridgeSupport274_rest_013 ridgeSupport274_rest_016
    ridgeSupport274_012 ridgeSupport274_suffix_013 ridgeSupport274_012_decode ridgeSupport274_suffix_decode_013
theorem ridgeSupport274_suffix_decode_011 : PackedRawNatGrowth.readList 14 157 ridgeSupport274_rest_011 =
    (ridgeSupport274_suffix_011, ridgeSupport274_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 125
    ridgeSupport274_rest_011 ridgeSupport274_rest_012 ridgeSupport274_rest_016
    ridgeSupport274_011 ridgeSupport274_suffix_012 ridgeSupport274_011_decode ridgeSupport274_suffix_decode_012
theorem ridgeSupport274_suffix_decode_010 : PackedRawNatGrowth.readList 14 189 ridgeSupport274_rest_010 =
    (ridgeSupport274_suffix_010, ridgeSupport274_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 157
    ridgeSupport274_rest_010 ridgeSupport274_rest_011 ridgeSupport274_rest_016
    ridgeSupport274_010 ridgeSupport274_suffix_011 ridgeSupport274_010_decode ridgeSupport274_suffix_decode_011
theorem ridgeSupport274_suffix_decode_009 : PackedRawNatGrowth.readList 14 221 ridgeSupport274_rest_009 =
    (ridgeSupport274_suffix_009, ridgeSupport274_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 189
    ridgeSupport274_rest_009 ridgeSupport274_rest_010 ridgeSupport274_rest_016
    ridgeSupport274_009 ridgeSupport274_suffix_010 ridgeSupport274_009_decode ridgeSupport274_suffix_decode_010
theorem ridgeSupport274_suffix_decode_008 : PackedRawNatGrowth.readList 14 253 ridgeSupport274_rest_008 =
    (ridgeSupport274_suffix_008, ridgeSupport274_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 221
    ridgeSupport274_rest_008 ridgeSupport274_rest_009 ridgeSupport274_rest_016
    ridgeSupport274_008 ridgeSupport274_suffix_009 ridgeSupport274_008_decode ridgeSupport274_suffix_decode_009
theorem ridgeSupport274_suffix_decode_007 : PackedRawNatGrowth.readList 14 285 ridgeSupport274_rest_007 =
    (ridgeSupport274_suffix_007, ridgeSupport274_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 253
    ridgeSupport274_rest_007 ridgeSupport274_rest_008 ridgeSupport274_rest_016
    ridgeSupport274_007 ridgeSupport274_suffix_008 ridgeSupport274_007_decode ridgeSupport274_suffix_decode_008
theorem ridgeSupport274_suffix_decode_006 : PackedRawNatGrowth.readList 14 317 ridgeSupport274_rest_006 =
    (ridgeSupport274_suffix_006, ridgeSupport274_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 285
    ridgeSupport274_rest_006 ridgeSupport274_rest_007 ridgeSupport274_rest_016
    ridgeSupport274_006 ridgeSupport274_suffix_007 ridgeSupport274_006_decode ridgeSupport274_suffix_decode_007
theorem ridgeSupport274_suffix_decode_005 : PackedRawNatGrowth.readList 14 349 ridgeSupport274_rest_005 =
    (ridgeSupport274_suffix_005, ridgeSupport274_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 317
    ridgeSupport274_rest_005 ridgeSupport274_rest_006 ridgeSupport274_rest_016
    ridgeSupport274_005 ridgeSupport274_suffix_006 ridgeSupport274_005_decode ridgeSupport274_suffix_decode_006
theorem ridgeSupport274_suffix_decode_004 : PackedRawNatGrowth.readList 14 381 ridgeSupport274_rest_004 =
    (ridgeSupport274_suffix_004, ridgeSupport274_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 349
    ridgeSupport274_rest_004 ridgeSupport274_rest_005 ridgeSupport274_rest_016
    ridgeSupport274_004 ridgeSupport274_suffix_005 ridgeSupport274_004_decode ridgeSupport274_suffix_decode_005
theorem ridgeSupport274_suffix_decode_003 : PackedRawNatGrowth.readList 14 413 ridgeSupport274_rest_003 =
    (ridgeSupport274_suffix_003, ridgeSupport274_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 381
    ridgeSupport274_rest_003 ridgeSupport274_rest_004 ridgeSupport274_rest_016
    ridgeSupport274_003 ridgeSupport274_suffix_004 ridgeSupport274_003_decode ridgeSupport274_suffix_decode_004
theorem ridgeSupport274_suffix_decode_002 : PackedRawNatGrowth.readList 14 445 ridgeSupport274_rest_002 =
    (ridgeSupport274_suffix_002, ridgeSupport274_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 413
    ridgeSupport274_rest_002 ridgeSupport274_rest_003 ridgeSupport274_rest_016
    ridgeSupport274_002 ridgeSupport274_suffix_003 ridgeSupport274_002_decode ridgeSupport274_suffix_decode_003
theorem ridgeSupport274_suffix_decode_001 : PackedRawNatGrowth.readList 14 477 ridgeSupport274_rest_001 =
    (ridgeSupport274_suffix_001, ridgeSupport274_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 445
    ridgeSupport274_rest_001 ridgeSupport274_rest_002 ridgeSupport274_rest_016
    ridgeSupport274_001 ridgeSupport274_suffix_002 ridgeSupport274_001_decode ridgeSupport274_suffix_decode_002
theorem ridgeSupport274_suffix_decode_000 : PackedRawNatGrowth.readList 14 509 ridgeSupport274_rest_000 =
    (ridgeSupport274_suffix_000, ridgeSupport274_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 477
    ridgeSupport274_rest_000 ridgeSupport274_rest_001 ridgeSupport274_rest_016
    ridgeSupport274_000 ridgeSupport274_suffix_001 ridgeSupport274_000_decode ridgeSupport274_suffix_decode_001
theorem ridgeSupport274_eq : candidateRows 274 = ridgeSupport274_suffix_000 := by
  rw [ridgeSupport274_source]
  exact congrArg Prod.fst ridgeSupport274_suffix_decode_000
theorem ridgeTest_large_274 : ridgeTest 274 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport274_eq]
    simp only [ridgeSupport274_suffix_000, ridgeSupport274_suffix_001, ridgeSupport274_suffix_002, ridgeSupport274_suffix_003, ridgeSupport274_suffix_004, ridgeSupport274_suffix_005, ridgeSupport274_suffix_006, ridgeSupport274_suffix_007, ridgeSupport274_suffix_008, ridgeSupport274_suffix_009, ridgeSupport274_suffix_010, ridgeSupport274_suffix_011, ridgeSupport274_suffix_012, ridgeSupport274_suffix_013, ridgeSupport274_suffix_014, ridgeSupport274_suffix_015, ridgeSupport274_suffix_016, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport274_000_mask, ridgeSupport274_001_mask, ridgeSupport274_002_mask, ridgeSupport274_003_mask, ridgeSupport274_004_mask, ridgeSupport274_005_mask, ridgeSupport274_006_mask, ridgeSupport274_007_mask, ridgeSupport274_008_mask, ridgeSupport274_009_mask, ridgeSupport274_010_mask, ridgeSupport274_011_mask, ridgeSupport274_012_mask, ridgeSupport274_013_mask, ridgeSupport274_014_mask, ridgeSupport274_015_mask]
    decide +kernel
  · rw [ridgeSupport274_eq]
    simp only [ridgeSupport274_suffix_000, ridgeSupport274_suffix_001, ridgeSupport274_suffix_002, ridgeSupport274_suffix_003, ridgeSupport274_suffix_004, ridgeSupport274_suffix_005, ridgeSupport274_suffix_006, ridgeSupport274_suffix_007, ridgeSupport274_suffix_008, ridgeSupport274_suffix_009, ridgeSupport274_suffix_010, ridgeSupport274_suffix_011, ridgeSupport274_suffix_012, ridgeSupport274_suffix_013, ridgeSupport274_suffix_014, ridgeSupport274_suffix_015, ridgeSupport274_suffix_016, List.all_append, List.all_nil, ridgeSupport274_000_checked, ridgeSupport274_001_checked, ridgeSupport274_002_checked, ridgeSupport274_003_checked, ridgeSupport274_004_checked, ridgeSupport274_005_checked, ridgeSupport274_006_checked, ridgeSupport274_007_checked, ridgeSupport274_008_checked, ridgeSupport274_009_checked, ridgeSupport274_010_checked, ridgeSupport274_011_checked, ridgeSupport274_012_checked, ridgeSupport274_013_checked, ridgeSupport274_014_checked, ridgeSupport274_015_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase01
