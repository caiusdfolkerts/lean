module
prelude
public import RootedSixBase00GrowthCacheRidgeSupport708Part000
public import RootedSixBase00GrowthCacheRidgeSupport708Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport708_suffix_decode_016 : PackedRawNatGrowth.readList 15 0 ridgeSupport708_rest_016 =
    (ridgeSupport708_suffix_016, ridgeSupport708_rest_016) := by rfl
theorem ridgeSupport708_suffix_decode_015 : PackedRawNatGrowth.readList 15 3 ridgeSupport708_rest_015 =
    (ridgeSupport708_suffix_015, ridgeSupport708_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 15 3 0
    ridgeSupport708_rest_015 ridgeSupport708_rest_016 ridgeSupport708_rest_016
    ridgeSupport708_015 ridgeSupport708_suffix_016 ridgeSupport708_015_decode ridgeSupport708_suffix_decode_016
theorem ridgeSupport708_suffix_decode_014 : PackedRawNatGrowth.readList 15 35 ridgeSupport708_rest_014 =
    (ridgeSupport708_suffix_014, ridgeSupport708_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 15 32 3
    ridgeSupport708_rest_014 ridgeSupport708_rest_015 ridgeSupport708_rest_016
    ridgeSupport708_014 ridgeSupport708_suffix_015 ridgeSupport708_014_decode ridgeSupport708_suffix_decode_015
theorem ridgeSupport708_suffix_decode_013 : PackedRawNatGrowth.readList 15 67 ridgeSupport708_rest_013 =
    (ridgeSupport708_suffix_013, ridgeSupport708_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 15 32 35
    ridgeSupport708_rest_013 ridgeSupport708_rest_014 ridgeSupport708_rest_016
    ridgeSupport708_013 ridgeSupport708_suffix_014 ridgeSupport708_013_decode ridgeSupport708_suffix_decode_014
theorem ridgeSupport708_suffix_decode_012 : PackedRawNatGrowth.readList 15 99 ridgeSupport708_rest_012 =
    (ridgeSupport708_suffix_012, ridgeSupport708_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 15 32 67
    ridgeSupport708_rest_012 ridgeSupport708_rest_013 ridgeSupport708_rest_016
    ridgeSupport708_012 ridgeSupport708_suffix_013 ridgeSupport708_012_decode ridgeSupport708_suffix_decode_013
theorem ridgeSupport708_suffix_decode_011 : PackedRawNatGrowth.readList 15 131 ridgeSupport708_rest_011 =
    (ridgeSupport708_suffix_011, ridgeSupport708_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 15 32 99
    ridgeSupport708_rest_011 ridgeSupport708_rest_012 ridgeSupport708_rest_016
    ridgeSupport708_011 ridgeSupport708_suffix_012 ridgeSupport708_011_decode ridgeSupport708_suffix_decode_012
theorem ridgeSupport708_suffix_decode_010 : PackedRawNatGrowth.readList 15 163 ridgeSupport708_rest_010 =
    (ridgeSupport708_suffix_010, ridgeSupport708_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 15 32 131
    ridgeSupport708_rest_010 ridgeSupport708_rest_011 ridgeSupport708_rest_016
    ridgeSupport708_010 ridgeSupport708_suffix_011 ridgeSupport708_010_decode ridgeSupport708_suffix_decode_011
theorem ridgeSupport708_suffix_decode_009 : PackedRawNatGrowth.readList 15 195 ridgeSupport708_rest_009 =
    (ridgeSupport708_suffix_009, ridgeSupport708_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 15 32 163
    ridgeSupport708_rest_009 ridgeSupport708_rest_010 ridgeSupport708_rest_016
    ridgeSupport708_009 ridgeSupport708_suffix_010 ridgeSupport708_009_decode ridgeSupport708_suffix_decode_010
theorem ridgeSupport708_suffix_decode_008 : PackedRawNatGrowth.readList 15 227 ridgeSupport708_rest_008 =
    (ridgeSupport708_suffix_008, ridgeSupport708_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 15 32 195
    ridgeSupport708_rest_008 ridgeSupport708_rest_009 ridgeSupport708_rest_016
    ridgeSupport708_008 ridgeSupport708_suffix_009 ridgeSupport708_008_decode ridgeSupport708_suffix_decode_009
theorem ridgeSupport708_suffix_decode_007 : PackedRawNatGrowth.readList 15 259 ridgeSupport708_rest_007 =
    (ridgeSupport708_suffix_007, ridgeSupport708_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 15 32 227
    ridgeSupport708_rest_007 ridgeSupport708_rest_008 ridgeSupport708_rest_016
    ridgeSupport708_007 ridgeSupport708_suffix_008 ridgeSupport708_007_decode ridgeSupport708_suffix_decode_008
theorem ridgeSupport708_suffix_decode_006 : PackedRawNatGrowth.readList 15 291 ridgeSupport708_rest_006 =
    (ridgeSupport708_suffix_006, ridgeSupport708_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 15 32 259
    ridgeSupport708_rest_006 ridgeSupport708_rest_007 ridgeSupport708_rest_016
    ridgeSupport708_006 ridgeSupport708_suffix_007 ridgeSupport708_006_decode ridgeSupport708_suffix_decode_007
theorem ridgeSupport708_suffix_decode_005 : PackedRawNatGrowth.readList 15 323 ridgeSupport708_rest_005 =
    (ridgeSupport708_suffix_005, ridgeSupport708_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 15 32 291
    ridgeSupport708_rest_005 ridgeSupport708_rest_006 ridgeSupport708_rest_016
    ridgeSupport708_005 ridgeSupport708_suffix_006 ridgeSupport708_005_decode ridgeSupport708_suffix_decode_006
theorem ridgeSupport708_suffix_decode_004 : PackedRawNatGrowth.readList 15 355 ridgeSupport708_rest_004 =
    (ridgeSupport708_suffix_004, ridgeSupport708_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 15 32 323
    ridgeSupport708_rest_004 ridgeSupport708_rest_005 ridgeSupport708_rest_016
    ridgeSupport708_004 ridgeSupport708_suffix_005 ridgeSupport708_004_decode ridgeSupport708_suffix_decode_005
theorem ridgeSupport708_suffix_decode_003 : PackedRawNatGrowth.readList 15 387 ridgeSupport708_rest_003 =
    (ridgeSupport708_suffix_003, ridgeSupport708_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 15 32 355
    ridgeSupport708_rest_003 ridgeSupport708_rest_004 ridgeSupport708_rest_016
    ridgeSupport708_003 ridgeSupport708_suffix_004 ridgeSupport708_003_decode ridgeSupport708_suffix_decode_004
theorem ridgeSupport708_suffix_decode_002 : PackedRawNatGrowth.readList 15 419 ridgeSupport708_rest_002 =
    (ridgeSupport708_suffix_002, ridgeSupport708_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 15 32 387
    ridgeSupport708_rest_002 ridgeSupport708_rest_003 ridgeSupport708_rest_016
    ridgeSupport708_002 ridgeSupport708_suffix_003 ridgeSupport708_002_decode ridgeSupport708_suffix_decode_003
theorem ridgeSupport708_suffix_decode_001 : PackedRawNatGrowth.readList 15 451 ridgeSupport708_rest_001 =
    (ridgeSupport708_suffix_001, ridgeSupport708_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 15 32 419
    ridgeSupport708_rest_001 ridgeSupport708_rest_002 ridgeSupport708_rest_016
    ridgeSupport708_001 ridgeSupport708_suffix_002 ridgeSupport708_001_decode ridgeSupport708_suffix_decode_002
theorem ridgeSupport708_suffix_decode_000 : PackedRawNatGrowth.readList 15 483 ridgeSupport708_rest_000 =
    (ridgeSupport708_suffix_000, ridgeSupport708_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 15 32 451
    ridgeSupport708_rest_000 ridgeSupport708_rest_001 ridgeSupport708_rest_016
    ridgeSupport708_000 ridgeSupport708_suffix_001 ridgeSupport708_000_decode ridgeSupport708_suffix_decode_001
theorem ridgeSupport708_eq : candidateRows 708 = ridgeSupport708_suffix_000 := by
  rw [ridgeSupport708_source]
  exact congrArg Prod.fst ridgeSupport708_suffix_decode_000
theorem ridgeTest_large_708 : ridgeTest 708 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport708_eq]
    simp only [ridgeSupport708_suffix_000, ridgeSupport708_suffix_001, ridgeSupport708_suffix_002, ridgeSupport708_suffix_003, ridgeSupport708_suffix_004, ridgeSupport708_suffix_005, ridgeSupport708_suffix_006, ridgeSupport708_suffix_007, ridgeSupport708_suffix_008, ridgeSupport708_suffix_009, ridgeSupport708_suffix_010, ridgeSupport708_suffix_011, ridgeSupport708_suffix_012, ridgeSupport708_suffix_013, ridgeSupport708_suffix_014, ridgeSupport708_suffix_015, ridgeSupport708_suffix_016, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport708_000_mask, ridgeSupport708_001_mask, ridgeSupport708_002_mask, ridgeSupport708_003_mask, ridgeSupport708_004_mask, ridgeSupport708_005_mask, ridgeSupport708_006_mask, ridgeSupport708_007_mask, ridgeSupport708_008_mask, ridgeSupport708_009_mask, ridgeSupport708_010_mask, ridgeSupport708_011_mask, ridgeSupport708_012_mask, ridgeSupport708_013_mask, ridgeSupport708_014_mask, ridgeSupport708_015_mask]
    decide +kernel
  · rw [ridgeSupport708_eq]
    simp only [ridgeSupport708_suffix_000, ridgeSupport708_suffix_001, ridgeSupport708_suffix_002, ridgeSupport708_suffix_003, ridgeSupport708_suffix_004, ridgeSupport708_suffix_005, ridgeSupport708_suffix_006, ridgeSupport708_suffix_007, ridgeSupport708_suffix_008, ridgeSupport708_suffix_009, ridgeSupport708_suffix_010, ridgeSupport708_suffix_011, ridgeSupport708_suffix_012, ridgeSupport708_suffix_013, ridgeSupport708_suffix_014, ridgeSupport708_suffix_015, ridgeSupport708_suffix_016, List.all_append, List.all_nil, ridgeSupport708_000_checked, ridgeSupport708_001_checked, ridgeSupport708_002_checked, ridgeSupport708_003_checked, ridgeSupport708_004_checked, ridgeSupport708_005_checked, ridgeSupport708_006_checked, ridgeSupport708_007_checked, ridgeSupport708_008_checked, ridgeSupport708_009_checked, ridgeSupport708_010_checked, ridgeSupport708_011_checked, ridgeSupport708_012_checked, ridgeSupport708_013_checked, ridgeSupport708_014_checked, ridgeSupport708_015_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase00
