module
prelude
public import RootedSixBase01GrowthCacheRidgeSupport266Part000
public import RootedSixBase01GrowthCacheRidgeSupport266Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport266_suffix_decode_016 : PackedRawNatGrowth.readList 14 0 ridgeSupport266_rest_016 =
    (ridgeSupport266_suffix_016, ridgeSupport266_rest_016) := by rfl
theorem ridgeSupport266_suffix_decode_015 : PackedRawNatGrowth.readList 14 29 ridgeSupport266_rest_015 =
    (ridgeSupport266_suffix_015, ridgeSupport266_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 29 0
    ridgeSupport266_rest_015 ridgeSupport266_rest_016 ridgeSupport266_rest_016
    ridgeSupport266_015 ridgeSupport266_suffix_016 ridgeSupport266_015_decode ridgeSupport266_suffix_decode_016
theorem ridgeSupport266_suffix_decode_014 : PackedRawNatGrowth.readList 14 61 ridgeSupport266_rest_014 =
    (ridgeSupport266_suffix_014, ridgeSupport266_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 29
    ridgeSupport266_rest_014 ridgeSupport266_rest_015 ridgeSupport266_rest_016
    ridgeSupport266_014 ridgeSupport266_suffix_015 ridgeSupport266_014_decode ridgeSupport266_suffix_decode_015
theorem ridgeSupport266_suffix_decode_013 : PackedRawNatGrowth.readList 14 93 ridgeSupport266_rest_013 =
    (ridgeSupport266_suffix_013, ridgeSupport266_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 61
    ridgeSupport266_rest_013 ridgeSupport266_rest_014 ridgeSupport266_rest_016
    ridgeSupport266_013 ridgeSupport266_suffix_014 ridgeSupport266_013_decode ridgeSupport266_suffix_decode_014
theorem ridgeSupport266_suffix_decode_012 : PackedRawNatGrowth.readList 14 125 ridgeSupport266_rest_012 =
    (ridgeSupport266_suffix_012, ridgeSupport266_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 93
    ridgeSupport266_rest_012 ridgeSupport266_rest_013 ridgeSupport266_rest_016
    ridgeSupport266_012 ridgeSupport266_suffix_013 ridgeSupport266_012_decode ridgeSupport266_suffix_decode_013
theorem ridgeSupport266_suffix_decode_011 : PackedRawNatGrowth.readList 14 157 ridgeSupport266_rest_011 =
    (ridgeSupport266_suffix_011, ridgeSupport266_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 125
    ridgeSupport266_rest_011 ridgeSupport266_rest_012 ridgeSupport266_rest_016
    ridgeSupport266_011 ridgeSupport266_suffix_012 ridgeSupport266_011_decode ridgeSupport266_suffix_decode_012
theorem ridgeSupport266_suffix_decode_010 : PackedRawNatGrowth.readList 14 189 ridgeSupport266_rest_010 =
    (ridgeSupport266_suffix_010, ridgeSupport266_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 157
    ridgeSupport266_rest_010 ridgeSupport266_rest_011 ridgeSupport266_rest_016
    ridgeSupport266_010 ridgeSupport266_suffix_011 ridgeSupport266_010_decode ridgeSupport266_suffix_decode_011
theorem ridgeSupport266_suffix_decode_009 : PackedRawNatGrowth.readList 14 221 ridgeSupport266_rest_009 =
    (ridgeSupport266_suffix_009, ridgeSupport266_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 189
    ridgeSupport266_rest_009 ridgeSupport266_rest_010 ridgeSupport266_rest_016
    ridgeSupport266_009 ridgeSupport266_suffix_010 ridgeSupport266_009_decode ridgeSupport266_suffix_decode_010
theorem ridgeSupport266_suffix_decode_008 : PackedRawNatGrowth.readList 14 253 ridgeSupport266_rest_008 =
    (ridgeSupport266_suffix_008, ridgeSupport266_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 221
    ridgeSupport266_rest_008 ridgeSupport266_rest_009 ridgeSupport266_rest_016
    ridgeSupport266_008 ridgeSupport266_suffix_009 ridgeSupport266_008_decode ridgeSupport266_suffix_decode_009
theorem ridgeSupport266_suffix_decode_007 : PackedRawNatGrowth.readList 14 285 ridgeSupport266_rest_007 =
    (ridgeSupport266_suffix_007, ridgeSupport266_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 253
    ridgeSupport266_rest_007 ridgeSupport266_rest_008 ridgeSupport266_rest_016
    ridgeSupport266_007 ridgeSupport266_suffix_008 ridgeSupport266_007_decode ridgeSupport266_suffix_decode_008
theorem ridgeSupport266_suffix_decode_006 : PackedRawNatGrowth.readList 14 317 ridgeSupport266_rest_006 =
    (ridgeSupport266_suffix_006, ridgeSupport266_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 285
    ridgeSupport266_rest_006 ridgeSupport266_rest_007 ridgeSupport266_rest_016
    ridgeSupport266_006 ridgeSupport266_suffix_007 ridgeSupport266_006_decode ridgeSupport266_suffix_decode_007
theorem ridgeSupport266_suffix_decode_005 : PackedRawNatGrowth.readList 14 349 ridgeSupport266_rest_005 =
    (ridgeSupport266_suffix_005, ridgeSupport266_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 317
    ridgeSupport266_rest_005 ridgeSupport266_rest_006 ridgeSupport266_rest_016
    ridgeSupport266_005 ridgeSupport266_suffix_006 ridgeSupport266_005_decode ridgeSupport266_suffix_decode_006
theorem ridgeSupport266_suffix_decode_004 : PackedRawNatGrowth.readList 14 381 ridgeSupport266_rest_004 =
    (ridgeSupport266_suffix_004, ridgeSupport266_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 349
    ridgeSupport266_rest_004 ridgeSupport266_rest_005 ridgeSupport266_rest_016
    ridgeSupport266_004 ridgeSupport266_suffix_005 ridgeSupport266_004_decode ridgeSupport266_suffix_decode_005
theorem ridgeSupport266_suffix_decode_003 : PackedRawNatGrowth.readList 14 413 ridgeSupport266_rest_003 =
    (ridgeSupport266_suffix_003, ridgeSupport266_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 381
    ridgeSupport266_rest_003 ridgeSupport266_rest_004 ridgeSupport266_rest_016
    ridgeSupport266_003 ridgeSupport266_suffix_004 ridgeSupport266_003_decode ridgeSupport266_suffix_decode_004
theorem ridgeSupport266_suffix_decode_002 : PackedRawNatGrowth.readList 14 445 ridgeSupport266_rest_002 =
    (ridgeSupport266_suffix_002, ridgeSupport266_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 413
    ridgeSupport266_rest_002 ridgeSupport266_rest_003 ridgeSupport266_rest_016
    ridgeSupport266_002 ridgeSupport266_suffix_003 ridgeSupport266_002_decode ridgeSupport266_suffix_decode_003
theorem ridgeSupport266_suffix_decode_001 : PackedRawNatGrowth.readList 14 477 ridgeSupport266_rest_001 =
    (ridgeSupport266_suffix_001, ridgeSupport266_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 445
    ridgeSupport266_rest_001 ridgeSupport266_rest_002 ridgeSupport266_rest_016
    ridgeSupport266_001 ridgeSupport266_suffix_002 ridgeSupport266_001_decode ridgeSupport266_suffix_decode_002
theorem ridgeSupport266_suffix_decode_000 : PackedRawNatGrowth.readList 14 509 ridgeSupport266_rest_000 =
    (ridgeSupport266_suffix_000, ridgeSupport266_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 477
    ridgeSupport266_rest_000 ridgeSupport266_rest_001 ridgeSupport266_rest_016
    ridgeSupport266_000 ridgeSupport266_suffix_001 ridgeSupport266_000_decode ridgeSupport266_suffix_decode_001
theorem ridgeSupport266_eq : candidateRows 266 = ridgeSupport266_suffix_000 := by
  rw [ridgeSupport266_source]
  exact congrArg Prod.fst ridgeSupport266_suffix_decode_000
theorem ridgeTest_large_266 : ridgeTest 266 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport266_eq]
    simp only [ridgeSupport266_suffix_000, ridgeSupport266_suffix_001, ridgeSupport266_suffix_002, ridgeSupport266_suffix_003, ridgeSupport266_suffix_004, ridgeSupport266_suffix_005, ridgeSupport266_suffix_006, ridgeSupport266_suffix_007, ridgeSupport266_suffix_008, ridgeSupport266_suffix_009, ridgeSupport266_suffix_010, ridgeSupport266_suffix_011, ridgeSupport266_suffix_012, ridgeSupport266_suffix_013, ridgeSupport266_suffix_014, ridgeSupport266_suffix_015, ridgeSupport266_suffix_016, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport266_000_mask, ridgeSupport266_001_mask, ridgeSupport266_002_mask, ridgeSupport266_003_mask, ridgeSupport266_004_mask, ridgeSupport266_005_mask, ridgeSupport266_006_mask, ridgeSupport266_007_mask, ridgeSupport266_008_mask, ridgeSupport266_009_mask, ridgeSupport266_010_mask, ridgeSupport266_011_mask, ridgeSupport266_012_mask, ridgeSupport266_013_mask, ridgeSupport266_014_mask, ridgeSupport266_015_mask]
    decide +kernel
  · rw [ridgeSupport266_eq]
    simp only [ridgeSupport266_suffix_000, ridgeSupport266_suffix_001, ridgeSupport266_suffix_002, ridgeSupport266_suffix_003, ridgeSupport266_suffix_004, ridgeSupport266_suffix_005, ridgeSupport266_suffix_006, ridgeSupport266_suffix_007, ridgeSupport266_suffix_008, ridgeSupport266_suffix_009, ridgeSupport266_suffix_010, ridgeSupport266_suffix_011, ridgeSupport266_suffix_012, ridgeSupport266_suffix_013, ridgeSupport266_suffix_014, ridgeSupport266_suffix_015, ridgeSupport266_suffix_016, List.all_append, List.all_nil, ridgeSupport266_000_checked, ridgeSupport266_001_checked, ridgeSupport266_002_checked, ridgeSupport266_003_checked, ridgeSupport266_004_checked, ridgeSupport266_005_checked, ridgeSupport266_006_checked, ridgeSupport266_007_checked, ridgeSupport266_008_checked, ridgeSupport266_009_checked, ridgeSupport266_010_checked, ridgeSupport266_011_checked, ridgeSupport266_012_checked, ridgeSupport266_013_checked, ridgeSupport266_014_checked, ridgeSupport266_015_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase01
