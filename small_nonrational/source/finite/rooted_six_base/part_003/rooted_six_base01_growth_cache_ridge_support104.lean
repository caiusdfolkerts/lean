module
prelude
public import RootedSixBase01GrowthCacheRidgeSupport104Part000
public import RootedSixBase01GrowthCacheRidgeSupport104Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport104_suffix_decode_016 : PackedRawNatGrowth.readList 14 0 ridgeSupport104_rest_016 =
    (ridgeSupport104_suffix_016, ridgeSupport104_rest_016) := by rfl
theorem ridgeSupport104_suffix_decode_015 : PackedRawNatGrowth.readList 14 29 ridgeSupport104_rest_015 =
    (ridgeSupport104_suffix_015, ridgeSupport104_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 29 0
    ridgeSupport104_rest_015 ridgeSupport104_rest_016 ridgeSupport104_rest_016
    ridgeSupport104_015 ridgeSupport104_suffix_016 ridgeSupport104_015_decode ridgeSupport104_suffix_decode_016
theorem ridgeSupport104_suffix_decode_014 : PackedRawNatGrowth.readList 14 61 ridgeSupport104_rest_014 =
    (ridgeSupport104_suffix_014, ridgeSupport104_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 29
    ridgeSupport104_rest_014 ridgeSupport104_rest_015 ridgeSupport104_rest_016
    ridgeSupport104_014 ridgeSupport104_suffix_015 ridgeSupport104_014_decode ridgeSupport104_suffix_decode_015
theorem ridgeSupport104_suffix_decode_013 : PackedRawNatGrowth.readList 14 93 ridgeSupport104_rest_013 =
    (ridgeSupport104_suffix_013, ridgeSupport104_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 61
    ridgeSupport104_rest_013 ridgeSupport104_rest_014 ridgeSupport104_rest_016
    ridgeSupport104_013 ridgeSupport104_suffix_014 ridgeSupport104_013_decode ridgeSupport104_suffix_decode_014
theorem ridgeSupport104_suffix_decode_012 : PackedRawNatGrowth.readList 14 125 ridgeSupport104_rest_012 =
    (ridgeSupport104_suffix_012, ridgeSupport104_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 93
    ridgeSupport104_rest_012 ridgeSupport104_rest_013 ridgeSupport104_rest_016
    ridgeSupport104_012 ridgeSupport104_suffix_013 ridgeSupport104_012_decode ridgeSupport104_suffix_decode_013
theorem ridgeSupport104_suffix_decode_011 : PackedRawNatGrowth.readList 14 157 ridgeSupport104_rest_011 =
    (ridgeSupport104_suffix_011, ridgeSupport104_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 125
    ridgeSupport104_rest_011 ridgeSupport104_rest_012 ridgeSupport104_rest_016
    ridgeSupport104_011 ridgeSupport104_suffix_012 ridgeSupport104_011_decode ridgeSupport104_suffix_decode_012
theorem ridgeSupport104_suffix_decode_010 : PackedRawNatGrowth.readList 14 189 ridgeSupport104_rest_010 =
    (ridgeSupport104_suffix_010, ridgeSupport104_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 157
    ridgeSupport104_rest_010 ridgeSupport104_rest_011 ridgeSupport104_rest_016
    ridgeSupport104_010 ridgeSupport104_suffix_011 ridgeSupport104_010_decode ridgeSupport104_suffix_decode_011
theorem ridgeSupport104_suffix_decode_009 : PackedRawNatGrowth.readList 14 221 ridgeSupport104_rest_009 =
    (ridgeSupport104_suffix_009, ridgeSupport104_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 189
    ridgeSupport104_rest_009 ridgeSupport104_rest_010 ridgeSupport104_rest_016
    ridgeSupport104_009 ridgeSupport104_suffix_010 ridgeSupport104_009_decode ridgeSupport104_suffix_decode_010
theorem ridgeSupport104_suffix_decode_008 : PackedRawNatGrowth.readList 14 253 ridgeSupport104_rest_008 =
    (ridgeSupport104_suffix_008, ridgeSupport104_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 221
    ridgeSupport104_rest_008 ridgeSupport104_rest_009 ridgeSupport104_rest_016
    ridgeSupport104_008 ridgeSupport104_suffix_009 ridgeSupport104_008_decode ridgeSupport104_suffix_decode_009
theorem ridgeSupport104_suffix_decode_007 : PackedRawNatGrowth.readList 14 285 ridgeSupport104_rest_007 =
    (ridgeSupport104_suffix_007, ridgeSupport104_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 253
    ridgeSupport104_rest_007 ridgeSupport104_rest_008 ridgeSupport104_rest_016
    ridgeSupport104_007 ridgeSupport104_suffix_008 ridgeSupport104_007_decode ridgeSupport104_suffix_decode_008
theorem ridgeSupport104_suffix_decode_006 : PackedRawNatGrowth.readList 14 317 ridgeSupport104_rest_006 =
    (ridgeSupport104_suffix_006, ridgeSupport104_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 285
    ridgeSupport104_rest_006 ridgeSupport104_rest_007 ridgeSupport104_rest_016
    ridgeSupport104_006 ridgeSupport104_suffix_007 ridgeSupport104_006_decode ridgeSupport104_suffix_decode_007
theorem ridgeSupport104_suffix_decode_005 : PackedRawNatGrowth.readList 14 349 ridgeSupport104_rest_005 =
    (ridgeSupport104_suffix_005, ridgeSupport104_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 317
    ridgeSupport104_rest_005 ridgeSupport104_rest_006 ridgeSupport104_rest_016
    ridgeSupport104_005 ridgeSupport104_suffix_006 ridgeSupport104_005_decode ridgeSupport104_suffix_decode_006
theorem ridgeSupport104_suffix_decode_004 : PackedRawNatGrowth.readList 14 381 ridgeSupport104_rest_004 =
    (ridgeSupport104_suffix_004, ridgeSupport104_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 349
    ridgeSupport104_rest_004 ridgeSupport104_rest_005 ridgeSupport104_rest_016
    ridgeSupport104_004 ridgeSupport104_suffix_005 ridgeSupport104_004_decode ridgeSupport104_suffix_decode_005
theorem ridgeSupport104_suffix_decode_003 : PackedRawNatGrowth.readList 14 413 ridgeSupport104_rest_003 =
    (ridgeSupport104_suffix_003, ridgeSupport104_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 381
    ridgeSupport104_rest_003 ridgeSupport104_rest_004 ridgeSupport104_rest_016
    ridgeSupport104_003 ridgeSupport104_suffix_004 ridgeSupport104_003_decode ridgeSupport104_suffix_decode_004
theorem ridgeSupport104_suffix_decode_002 : PackedRawNatGrowth.readList 14 445 ridgeSupport104_rest_002 =
    (ridgeSupport104_suffix_002, ridgeSupport104_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 413
    ridgeSupport104_rest_002 ridgeSupport104_rest_003 ridgeSupport104_rest_016
    ridgeSupport104_002 ridgeSupport104_suffix_003 ridgeSupport104_002_decode ridgeSupport104_suffix_decode_003
theorem ridgeSupport104_suffix_decode_001 : PackedRawNatGrowth.readList 14 477 ridgeSupport104_rest_001 =
    (ridgeSupport104_suffix_001, ridgeSupport104_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 445
    ridgeSupport104_rest_001 ridgeSupport104_rest_002 ridgeSupport104_rest_016
    ridgeSupport104_001 ridgeSupport104_suffix_002 ridgeSupport104_001_decode ridgeSupport104_suffix_decode_002
theorem ridgeSupport104_suffix_decode_000 : PackedRawNatGrowth.readList 14 509 ridgeSupport104_rest_000 =
    (ridgeSupport104_suffix_000, ridgeSupport104_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 477
    ridgeSupport104_rest_000 ridgeSupport104_rest_001 ridgeSupport104_rest_016
    ridgeSupport104_000 ridgeSupport104_suffix_001 ridgeSupport104_000_decode ridgeSupport104_suffix_decode_001
theorem ridgeSupport104_eq : candidateRows 104 = ridgeSupport104_suffix_000 := by
  rw [ridgeSupport104_source]
  exact congrArg Prod.fst ridgeSupport104_suffix_decode_000
theorem ridgeTest_large_104 : ridgeTest 104 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport104_eq]
    simp only [ridgeSupport104_suffix_000, ridgeSupport104_suffix_001, ridgeSupport104_suffix_002, ridgeSupport104_suffix_003, ridgeSupport104_suffix_004, ridgeSupport104_suffix_005, ridgeSupport104_suffix_006, ridgeSupport104_suffix_007, ridgeSupport104_suffix_008, ridgeSupport104_suffix_009, ridgeSupport104_suffix_010, ridgeSupport104_suffix_011, ridgeSupport104_suffix_012, ridgeSupport104_suffix_013, ridgeSupport104_suffix_014, ridgeSupport104_suffix_015, ridgeSupport104_suffix_016, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport104_000_mask, ridgeSupport104_001_mask, ridgeSupport104_002_mask, ridgeSupport104_003_mask, ridgeSupport104_004_mask, ridgeSupport104_005_mask, ridgeSupport104_006_mask, ridgeSupport104_007_mask, ridgeSupport104_008_mask, ridgeSupport104_009_mask, ridgeSupport104_010_mask, ridgeSupport104_011_mask, ridgeSupport104_012_mask, ridgeSupport104_013_mask, ridgeSupport104_014_mask, ridgeSupport104_015_mask]
    decide +kernel
  · rw [ridgeSupport104_eq]
    simp only [ridgeSupport104_suffix_000, ridgeSupport104_suffix_001, ridgeSupport104_suffix_002, ridgeSupport104_suffix_003, ridgeSupport104_suffix_004, ridgeSupport104_suffix_005, ridgeSupport104_suffix_006, ridgeSupport104_suffix_007, ridgeSupport104_suffix_008, ridgeSupport104_suffix_009, ridgeSupport104_suffix_010, ridgeSupport104_suffix_011, ridgeSupport104_suffix_012, ridgeSupport104_suffix_013, ridgeSupport104_suffix_014, ridgeSupport104_suffix_015, ridgeSupport104_suffix_016, List.all_append, List.all_nil, ridgeSupport104_000_checked, ridgeSupport104_001_checked, ridgeSupport104_002_checked, ridgeSupport104_003_checked, ridgeSupport104_004_checked, ridgeSupport104_005_checked, ridgeSupport104_006_checked, ridgeSupport104_007_checked, ridgeSupport104_008_checked, ridgeSupport104_009_checked, ridgeSupport104_010_checked, ridgeSupport104_011_checked, ridgeSupport104_012_checked, ridgeSupport104_013_checked, ridgeSupport104_014_checked, ridgeSupport104_015_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase01
