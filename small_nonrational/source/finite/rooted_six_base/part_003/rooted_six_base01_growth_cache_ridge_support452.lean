module
prelude
public import RootedSixBase01GrowthCacheRidgeSupport452Part000
public import RootedSixBase01GrowthCacheRidgeSupport452Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport452_suffix_decode_016 : PackedRawNatGrowth.readList 14 0 ridgeSupport452_rest_016 =
    (ridgeSupport452_suffix_016, ridgeSupport452_rest_016) := by rfl
theorem ridgeSupport452_suffix_decode_015 : PackedRawNatGrowth.readList 14 3 ridgeSupport452_rest_015 =
    (ridgeSupport452_suffix_015, ridgeSupport452_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 3 0
    ridgeSupport452_rest_015 ridgeSupport452_rest_016 ridgeSupport452_rest_016
    ridgeSupport452_015 ridgeSupport452_suffix_016 ridgeSupport452_015_decode ridgeSupport452_suffix_decode_016
theorem ridgeSupport452_suffix_decode_014 : PackedRawNatGrowth.readList 14 35 ridgeSupport452_rest_014 =
    (ridgeSupport452_suffix_014, ridgeSupport452_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 3
    ridgeSupport452_rest_014 ridgeSupport452_rest_015 ridgeSupport452_rest_016
    ridgeSupport452_014 ridgeSupport452_suffix_015 ridgeSupport452_014_decode ridgeSupport452_suffix_decode_015
theorem ridgeSupport452_suffix_decode_013 : PackedRawNatGrowth.readList 14 67 ridgeSupport452_rest_013 =
    (ridgeSupport452_suffix_013, ridgeSupport452_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 35
    ridgeSupport452_rest_013 ridgeSupport452_rest_014 ridgeSupport452_rest_016
    ridgeSupport452_013 ridgeSupport452_suffix_014 ridgeSupport452_013_decode ridgeSupport452_suffix_decode_014
theorem ridgeSupport452_suffix_decode_012 : PackedRawNatGrowth.readList 14 99 ridgeSupport452_rest_012 =
    (ridgeSupport452_suffix_012, ridgeSupport452_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 67
    ridgeSupport452_rest_012 ridgeSupport452_rest_013 ridgeSupport452_rest_016
    ridgeSupport452_012 ridgeSupport452_suffix_013 ridgeSupport452_012_decode ridgeSupport452_suffix_decode_013
theorem ridgeSupport452_suffix_decode_011 : PackedRawNatGrowth.readList 14 131 ridgeSupport452_rest_011 =
    (ridgeSupport452_suffix_011, ridgeSupport452_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 99
    ridgeSupport452_rest_011 ridgeSupport452_rest_012 ridgeSupport452_rest_016
    ridgeSupport452_011 ridgeSupport452_suffix_012 ridgeSupport452_011_decode ridgeSupport452_suffix_decode_012
theorem ridgeSupport452_suffix_decode_010 : PackedRawNatGrowth.readList 14 163 ridgeSupport452_rest_010 =
    (ridgeSupport452_suffix_010, ridgeSupport452_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 131
    ridgeSupport452_rest_010 ridgeSupport452_rest_011 ridgeSupport452_rest_016
    ridgeSupport452_010 ridgeSupport452_suffix_011 ridgeSupport452_010_decode ridgeSupport452_suffix_decode_011
theorem ridgeSupport452_suffix_decode_009 : PackedRawNatGrowth.readList 14 195 ridgeSupport452_rest_009 =
    (ridgeSupport452_suffix_009, ridgeSupport452_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 163
    ridgeSupport452_rest_009 ridgeSupport452_rest_010 ridgeSupport452_rest_016
    ridgeSupport452_009 ridgeSupport452_suffix_010 ridgeSupport452_009_decode ridgeSupport452_suffix_decode_010
theorem ridgeSupport452_suffix_decode_008 : PackedRawNatGrowth.readList 14 227 ridgeSupport452_rest_008 =
    (ridgeSupport452_suffix_008, ridgeSupport452_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 195
    ridgeSupport452_rest_008 ridgeSupport452_rest_009 ridgeSupport452_rest_016
    ridgeSupport452_008 ridgeSupport452_suffix_009 ridgeSupport452_008_decode ridgeSupport452_suffix_decode_009
theorem ridgeSupport452_suffix_decode_007 : PackedRawNatGrowth.readList 14 259 ridgeSupport452_rest_007 =
    (ridgeSupport452_suffix_007, ridgeSupport452_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 227
    ridgeSupport452_rest_007 ridgeSupport452_rest_008 ridgeSupport452_rest_016
    ridgeSupport452_007 ridgeSupport452_suffix_008 ridgeSupport452_007_decode ridgeSupport452_suffix_decode_008
theorem ridgeSupport452_suffix_decode_006 : PackedRawNatGrowth.readList 14 291 ridgeSupport452_rest_006 =
    (ridgeSupport452_suffix_006, ridgeSupport452_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 259
    ridgeSupport452_rest_006 ridgeSupport452_rest_007 ridgeSupport452_rest_016
    ridgeSupport452_006 ridgeSupport452_suffix_007 ridgeSupport452_006_decode ridgeSupport452_suffix_decode_007
theorem ridgeSupport452_suffix_decode_005 : PackedRawNatGrowth.readList 14 323 ridgeSupport452_rest_005 =
    (ridgeSupport452_suffix_005, ridgeSupport452_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 291
    ridgeSupport452_rest_005 ridgeSupport452_rest_006 ridgeSupport452_rest_016
    ridgeSupport452_005 ridgeSupport452_suffix_006 ridgeSupport452_005_decode ridgeSupport452_suffix_decode_006
theorem ridgeSupport452_suffix_decode_004 : PackedRawNatGrowth.readList 14 355 ridgeSupport452_rest_004 =
    (ridgeSupport452_suffix_004, ridgeSupport452_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 323
    ridgeSupport452_rest_004 ridgeSupport452_rest_005 ridgeSupport452_rest_016
    ridgeSupport452_004 ridgeSupport452_suffix_005 ridgeSupport452_004_decode ridgeSupport452_suffix_decode_005
theorem ridgeSupport452_suffix_decode_003 : PackedRawNatGrowth.readList 14 387 ridgeSupport452_rest_003 =
    (ridgeSupport452_suffix_003, ridgeSupport452_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 355
    ridgeSupport452_rest_003 ridgeSupport452_rest_004 ridgeSupport452_rest_016
    ridgeSupport452_003 ridgeSupport452_suffix_004 ridgeSupport452_003_decode ridgeSupport452_suffix_decode_004
theorem ridgeSupport452_suffix_decode_002 : PackedRawNatGrowth.readList 14 419 ridgeSupport452_rest_002 =
    (ridgeSupport452_suffix_002, ridgeSupport452_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 387
    ridgeSupport452_rest_002 ridgeSupport452_rest_003 ridgeSupport452_rest_016
    ridgeSupport452_002 ridgeSupport452_suffix_003 ridgeSupport452_002_decode ridgeSupport452_suffix_decode_003
theorem ridgeSupport452_suffix_decode_001 : PackedRawNatGrowth.readList 14 451 ridgeSupport452_rest_001 =
    (ridgeSupport452_suffix_001, ridgeSupport452_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 419
    ridgeSupport452_rest_001 ridgeSupport452_rest_002 ridgeSupport452_rest_016
    ridgeSupport452_001 ridgeSupport452_suffix_002 ridgeSupport452_001_decode ridgeSupport452_suffix_decode_002
theorem ridgeSupport452_suffix_decode_000 : PackedRawNatGrowth.readList 14 483 ridgeSupport452_rest_000 =
    (ridgeSupport452_suffix_000, ridgeSupport452_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 451
    ridgeSupport452_rest_000 ridgeSupport452_rest_001 ridgeSupport452_rest_016
    ridgeSupport452_000 ridgeSupport452_suffix_001 ridgeSupport452_000_decode ridgeSupport452_suffix_decode_001
theorem ridgeSupport452_eq : candidateRows 452 = ridgeSupport452_suffix_000 := by
  rw [ridgeSupport452_source]
  exact congrArg Prod.fst ridgeSupport452_suffix_decode_000
theorem ridgeTest_large_452 : ridgeTest 452 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport452_eq]
    simp only [ridgeSupport452_suffix_000, ridgeSupport452_suffix_001, ridgeSupport452_suffix_002, ridgeSupport452_suffix_003, ridgeSupport452_suffix_004, ridgeSupport452_suffix_005, ridgeSupport452_suffix_006, ridgeSupport452_suffix_007, ridgeSupport452_suffix_008, ridgeSupport452_suffix_009, ridgeSupport452_suffix_010, ridgeSupport452_suffix_011, ridgeSupport452_suffix_012, ridgeSupport452_suffix_013, ridgeSupport452_suffix_014, ridgeSupport452_suffix_015, ridgeSupport452_suffix_016, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport452_000_mask, ridgeSupport452_001_mask, ridgeSupport452_002_mask, ridgeSupport452_003_mask, ridgeSupport452_004_mask, ridgeSupport452_005_mask, ridgeSupport452_006_mask, ridgeSupport452_007_mask, ridgeSupport452_008_mask, ridgeSupport452_009_mask, ridgeSupport452_010_mask, ridgeSupport452_011_mask, ridgeSupport452_012_mask, ridgeSupport452_013_mask, ridgeSupport452_014_mask, ridgeSupport452_015_mask]
    decide +kernel
  · rw [ridgeSupport452_eq]
    simp only [ridgeSupport452_suffix_000, ridgeSupport452_suffix_001, ridgeSupport452_suffix_002, ridgeSupport452_suffix_003, ridgeSupport452_suffix_004, ridgeSupport452_suffix_005, ridgeSupport452_suffix_006, ridgeSupport452_suffix_007, ridgeSupport452_suffix_008, ridgeSupport452_suffix_009, ridgeSupport452_suffix_010, ridgeSupport452_suffix_011, ridgeSupport452_suffix_012, ridgeSupport452_suffix_013, ridgeSupport452_suffix_014, ridgeSupport452_suffix_015, ridgeSupport452_suffix_016, List.all_append, List.all_nil, ridgeSupport452_000_checked, ridgeSupport452_001_checked, ridgeSupport452_002_checked, ridgeSupport452_003_checked, ridgeSupport452_004_checked, ridgeSupport452_005_checked, ridgeSupport452_006_checked, ridgeSupport452_007_checked, ridgeSupport452_008_checked, ridgeSupport452_009_checked, ridgeSupport452_010_checked, ridgeSupport452_011_checked, ridgeSupport452_012_checked, ridgeSupport452_013_checked, ridgeSupport452_014_checked, ridgeSupport452_015_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase01
