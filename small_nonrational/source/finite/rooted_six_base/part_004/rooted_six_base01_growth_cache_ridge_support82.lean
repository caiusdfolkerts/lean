module
prelude
public import RootedSixBase01GrowthCacheRidgeSupport82Part000
public import RootedSixBase01GrowthCacheRidgeSupport82Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport82_suffix_decode_016 : PackedRawNatGrowth.readList 14 0 ridgeSupport82_rest_016 =
    (ridgeSupport82_suffix_016, ridgeSupport82_rest_016) := by rfl
theorem ridgeSupport82_suffix_decode_015 : PackedRawNatGrowth.readList 14 29 ridgeSupport82_rest_015 =
    (ridgeSupport82_suffix_015, ridgeSupport82_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 29 0
    ridgeSupport82_rest_015 ridgeSupport82_rest_016 ridgeSupport82_rest_016
    ridgeSupport82_015 ridgeSupport82_suffix_016 ridgeSupport82_015_decode ridgeSupport82_suffix_decode_016
theorem ridgeSupport82_suffix_decode_014 : PackedRawNatGrowth.readList 14 61 ridgeSupport82_rest_014 =
    (ridgeSupport82_suffix_014, ridgeSupport82_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 29
    ridgeSupport82_rest_014 ridgeSupport82_rest_015 ridgeSupport82_rest_016
    ridgeSupport82_014 ridgeSupport82_suffix_015 ridgeSupport82_014_decode ridgeSupport82_suffix_decode_015
theorem ridgeSupport82_suffix_decode_013 : PackedRawNatGrowth.readList 14 93 ridgeSupport82_rest_013 =
    (ridgeSupport82_suffix_013, ridgeSupport82_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 61
    ridgeSupport82_rest_013 ridgeSupport82_rest_014 ridgeSupport82_rest_016
    ridgeSupport82_013 ridgeSupport82_suffix_014 ridgeSupport82_013_decode ridgeSupport82_suffix_decode_014
theorem ridgeSupport82_suffix_decode_012 : PackedRawNatGrowth.readList 14 125 ridgeSupport82_rest_012 =
    (ridgeSupport82_suffix_012, ridgeSupport82_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 93
    ridgeSupport82_rest_012 ridgeSupport82_rest_013 ridgeSupport82_rest_016
    ridgeSupport82_012 ridgeSupport82_suffix_013 ridgeSupport82_012_decode ridgeSupport82_suffix_decode_013
theorem ridgeSupport82_suffix_decode_011 : PackedRawNatGrowth.readList 14 157 ridgeSupport82_rest_011 =
    (ridgeSupport82_suffix_011, ridgeSupport82_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 125
    ridgeSupport82_rest_011 ridgeSupport82_rest_012 ridgeSupport82_rest_016
    ridgeSupport82_011 ridgeSupport82_suffix_012 ridgeSupport82_011_decode ridgeSupport82_suffix_decode_012
theorem ridgeSupport82_suffix_decode_010 : PackedRawNatGrowth.readList 14 189 ridgeSupport82_rest_010 =
    (ridgeSupport82_suffix_010, ridgeSupport82_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 157
    ridgeSupport82_rest_010 ridgeSupport82_rest_011 ridgeSupport82_rest_016
    ridgeSupport82_010 ridgeSupport82_suffix_011 ridgeSupport82_010_decode ridgeSupport82_suffix_decode_011
theorem ridgeSupport82_suffix_decode_009 : PackedRawNatGrowth.readList 14 221 ridgeSupport82_rest_009 =
    (ridgeSupport82_suffix_009, ridgeSupport82_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 189
    ridgeSupport82_rest_009 ridgeSupport82_rest_010 ridgeSupport82_rest_016
    ridgeSupport82_009 ridgeSupport82_suffix_010 ridgeSupport82_009_decode ridgeSupport82_suffix_decode_010
theorem ridgeSupport82_suffix_decode_008 : PackedRawNatGrowth.readList 14 253 ridgeSupport82_rest_008 =
    (ridgeSupport82_suffix_008, ridgeSupport82_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 221
    ridgeSupport82_rest_008 ridgeSupport82_rest_009 ridgeSupport82_rest_016
    ridgeSupport82_008 ridgeSupport82_suffix_009 ridgeSupport82_008_decode ridgeSupport82_suffix_decode_009
theorem ridgeSupport82_suffix_decode_007 : PackedRawNatGrowth.readList 14 285 ridgeSupport82_rest_007 =
    (ridgeSupport82_suffix_007, ridgeSupport82_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 253
    ridgeSupport82_rest_007 ridgeSupport82_rest_008 ridgeSupport82_rest_016
    ridgeSupport82_007 ridgeSupport82_suffix_008 ridgeSupport82_007_decode ridgeSupport82_suffix_decode_008
theorem ridgeSupport82_suffix_decode_006 : PackedRawNatGrowth.readList 14 317 ridgeSupport82_rest_006 =
    (ridgeSupport82_suffix_006, ridgeSupport82_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 285
    ridgeSupport82_rest_006 ridgeSupport82_rest_007 ridgeSupport82_rest_016
    ridgeSupport82_006 ridgeSupport82_suffix_007 ridgeSupport82_006_decode ridgeSupport82_suffix_decode_007
theorem ridgeSupport82_suffix_decode_005 : PackedRawNatGrowth.readList 14 349 ridgeSupport82_rest_005 =
    (ridgeSupport82_suffix_005, ridgeSupport82_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 317
    ridgeSupport82_rest_005 ridgeSupport82_rest_006 ridgeSupport82_rest_016
    ridgeSupport82_005 ridgeSupport82_suffix_006 ridgeSupport82_005_decode ridgeSupport82_suffix_decode_006
theorem ridgeSupport82_suffix_decode_004 : PackedRawNatGrowth.readList 14 381 ridgeSupport82_rest_004 =
    (ridgeSupport82_suffix_004, ridgeSupport82_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 349
    ridgeSupport82_rest_004 ridgeSupport82_rest_005 ridgeSupport82_rest_016
    ridgeSupport82_004 ridgeSupport82_suffix_005 ridgeSupport82_004_decode ridgeSupport82_suffix_decode_005
theorem ridgeSupport82_suffix_decode_003 : PackedRawNatGrowth.readList 14 413 ridgeSupport82_rest_003 =
    (ridgeSupport82_suffix_003, ridgeSupport82_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 381
    ridgeSupport82_rest_003 ridgeSupport82_rest_004 ridgeSupport82_rest_016
    ridgeSupport82_003 ridgeSupport82_suffix_004 ridgeSupport82_003_decode ridgeSupport82_suffix_decode_004
theorem ridgeSupport82_suffix_decode_002 : PackedRawNatGrowth.readList 14 445 ridgeSupport82_rest_002 =
    (ridgeSupport82_suffix_002, ridgeSupport82_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 413
    ridgeSupport82_rest_002 ridgeSupport82_rest_003 ridgeSupport82_rest_016
    ridgeSupport82_002 ridgeSupport82_suffix_003 ridgeSupport82_002_decode ridgeSupport82_suffix_decode_003
theorem ridgeSupport82_suffix_decode_001 : PackedRawNatGrowth.readList 14 477 ridgeSupport82_rest_001 =
    (ridgeSupport82_suffix_001, ridgeSupport82_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 445
    ridgeSupport82_rest_001 ridgeSupport82_rest_002 ridgeSupport82_rest_016
    ridgeSupport82_001 ridgeSupport82_suffix_002 ridgeSupport82_001_decode ridgeSupport82_suffix_decode_002
theorem ridgeSupport82_suffix_decode_000 : PackedRawNatGrowth.readList 14 509 ridgeSupport82_rest_000 =
    (ridgeSupport82_suffix_000, ridgeSupport82_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 477
    ridgeSupport82_rest_000 ridgeSupport82_rest_001 ridgeSupport82_rest_016
    ridgeSupport82_000 ridgeSupport82_suffix_001 ridgeSupport82_000_decode ridgeSupport82_suffix_decode_001
theorem ridgeSupport82_eq : candidateRows 82 = ridgeSupport82_suffix_000 := by
  rw [ridgeSupport82_source]
  exact congrArg Prod.fst ridgeSupport82_suffix_decode_000
theorem ridgeTest_large_82 : ridgeTest 82 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport82_eq]
    simp only [ridgeSupport82_suffix_000, ridgeSupport82_suffix_001, ridgeSupport82_suffix_002, ridgeSupport82_suffix_003, ridgeSupport82_suffix_004, ridgeSupport82_suffix_005, ridgeSupport82_suffix_006, ridgeSupport82_suffix_007, ridgeSupport82_suffix_008, ridgeSupport82_suffix_009, ridgeSupport82_suffix_010, ridgeSupport82_suffix_011, ridgeSupport82_suffix_012, ridgeSupport82_suffix_013, ridgeSupport82_suffix_014, ridgeSupport82_suffix_015, ridgeSupport82_suffix_016, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport82_000_mask, ridgeSupport82_001_mask, ridgeSupport82_002_mask, ridgeSupport82_003_mask, ridgeSupport82_004_mask, ridgeSupport82_005_mask, ridgeSupport82_006_mask, ridgeSupport82_007_mask, ridgeSupport82_008_mask, ridgeSupport82_009_mask, ridgeSupport82_010_mask, ridgeSupport82_011_mask, ridgeSupport82_012_mask, ridgeSupport82_013_mask, ridgeSupport82_014_mask, ridgeSupport82_015_mask]
    decide +kernel
  · rw [ridgeSupport82_eq]
    simp only [ridgeSupport82_suffix_000, ridgeSupport82_suffix_001, ridgeSupport82_suffix_002, ridgeSupport82_suffix_003, ridgeSupport82_suffix_004, ridgeSupport82_suffix_005, ridgeSupport82_suffix_006, ridgeSupport82_suffix_007, ridgeSupport82_suffix_008, ridgeSupport82_suffix_009, ridgeSupport82_suffix_010, ridgeSupport82_suffix_011, ridgeSupport82_suffix_012, ridgeSupport82_suffix_013, ridgeSupport82_suffix_014, ridgeSupport82_suffix_015, ridgeSupport82_suffix_016, List.all_append, List.all_nil, ridgeSupport82_000_checked, ridgeSupport82_001_checked, ridgeSupport82_002_checked, ridgeSupport82_003_checked, ridgeSupport82_004_checked, ridgeSupport82_005_checked, ridgeSupport82_006_checked, ridgeSupport82_007_checked, ridgeSupport82_008_checked, ridgeSupport82_009_checked, ridgeSupport82_010_checked, ridgeSupport82_011_checked, ridgeSupport82_012_checked, ridgeSupport82_013_checked, ridgeSupport82_014_checked, ridgeSupport82_015_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase01
