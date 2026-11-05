module
prelude
public import RootedSixBase00GrowthCacheRidgeSupport712Part000
public import RootedSixBase00GrowthCacheRidgeSupport712Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport712_suffix_decode_016 : PackedRawNatGrowth.readList 15 0 ridgeSupport712_rest_016 =
    (ridgeSupport712_suffix_016, ridgeSupport712_rest_016) := by rfl
theorem ridgeSupport712_suffix_decode_015 : PackedRawNatGrowth.readList 15 3 ridgeSupport712_rest_015 =
    (ridgeSupport712_suffix_015, ridgeSupport712_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 15 3 0
    ridgeSupport712_rest_015 ridgeSupport712_rest_016 ridgeSupport712_rest_016
    ridgeSupport712_015 ridgeSupport712_suffix_016 ridgeSupport712_015_decode ridgeSupport712_suffix_decode_016
theorem ridgeSupport712_suffix_decode_014 : PackedRawNatGrowth.readList 15 35 ridgeSupport712_rest_014 =
    (ridgeSupport712_suffix_014, ridgeSupport712_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 15 32 3
    ridgeSupport712_rest_014 ridgeSupport712_rest_015 ridgeSupport712_rest_016
    ridgeSupport712_014 ridgeSupport712_suffix_015 ridgeSupport712_014_decode ridgeSupport712_suffix_decode_015
theorem ridgeSupport712_suffix_decode_013 : PackedRawNatGrowth.readList 15 67 ridgeSupport712_rest_013 =
    (ridgeSupport712_suffix_013, ridgeSupport712_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 15 32 35
    ridgeSupport712_rest_013 ridgeSupport712_rest_014 ridgeSupport712_rest_016
    ridgeSupport712_013 ridgeSupport712_suffix_014 ridgeSupport712_013_decode ridgeSupport712_suffix_decode_014
theorem ridgeSupport712_suffix_decode_012 : PackedRawNatGrowth.readList 15 99 ridgeSupport712_rest_012 =
    (ridgeSupport712_suffix_012, ridgeSupport712_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 15 32 67
    ridgeSupport712_rest_012 ridgeSupport712_rest_013 ridgeSupport712_rest_016
    ridgeSupport712_012 ridgeSupport712_suffix_013 ridgeSupport712_012_decode ridgeSupport712_suffix_decode_013
theorem ridgeSupport712_suffix_decode_011 : PackedRawNatGrowth.readList 15 131 ridgeSupport712_rest_011 =
    (ridgeSupport712_suffix_011, ridgeSupport712_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 15 32 99
    ridgeSupport712_rest_011 ridgeSupport712_rest_012 ridgeSupport712_rest_016
    ridgeSupport712_011 ridgeSupport712_suffix_012 ridgeSupport712_011_decode ridgeSupport712_suffix_decode_012
theorem ridgeSupport712_suffix_decode_010 : PackedRawNatGrowth.readList 15 163 ridgeSupport712_rest_010 =
    (ridgeSupport712_suffix_010, ridgeSupport712_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 15 32 131
    ridgeSupport712_rest_010 ridgeSupport712_rest_011 ridgeSupport712_rest_016
    ridgeSupport712_010 ridgeSupport712_suffix_011 ridgeSupport712_010_decode ridgeSupport712_suffix_decode_011
theorem ridgeSupport712_suffix_decode_009 : PackedRawNatGrowth.readList 15 195 ridgeSupport712_rest_009 =
    (ridgeSupport712_suffix_009, ridgeSupport712_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 15 32 163
    ridgeSupport712_rest_009 ridgeSupport712_rest_010 ridgeSupport712_rest_016
    ridgeSupport712_009 ridgeSupport712_suffix_010 ridgeSupport712_009_decode ridgeSupport712_suffix_decode_010
theorem ridgeSupport712_suffix_decode_008 : PackedRawNatGrowth.readList 15 227 ridgeSupport712_rest_008 =
    (ridgeSupport712_suffix_008, ridgeSupport712_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 15 32 195
    ridgeSupport712_rest_008 ridgeSupport712_rest_009 ridgeSupport712_rest_016
    ridgeSupport712_008 ridgeSupport712_suffix_009 ridgeSupport712_008_decode ridgeSupport712_suffix_decode_009
theorem ridgeSupport712_suffix_decode_007 : PackedRawNatGrowth.readList 15 259 ridgeSupport712_rest_007 =
    (ridgeSupport712_suffix_007, ridgeSupport712_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 15 32 227
    ridgeSupport712_rest_007 ridgeSupport712_rest_008 ridgeSupport712_rest_016
    ridgeSupport712_007 ridgeSupport712_suffix_008 ridgeSupport712_007_decode ridgeSupport712_suffix_decode_008
theorem ridgeSupport712_suffix_decode_006 : PackedRawNatGrowth.readList 15 291 ridgeSupport712_rest_006 =
    (ridgeSupport712_suffix_006, ridgeSupport712_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 15 32 259
    ridgeSupport712_rest_006 ridgeSupport712_rest_007 ridgeSupport712_rest_016
    ridgeSupport712_006 ridgeSupport712_suffix_007 ridgeSupport712_006_decode ridgeSupport712_suffix_decode_007
theorem ridgeSupport712_suffix_decode_005 : PackedRawNatGrowth.readList 15 323 ridgeSupport712_rest_005 =
    (ridgeSupport712_suffix_005, ridgeSupport712_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 15 32 291
    ridgeSupport712_rest_005 ridgeSupport712_rest_006 ridgeSupport712_rest_016
    ridgeSupport712_005 ridgeSupport712_suffix_006 ridgeSupport712_005_decode ridgeSupport712_suffix_decode_006
theorem ridgeSupport712_suffix_decode_004 : PackedRawNatGrowth.readList 15 355 ridgeSupport712_rest_004 =
    (ridgeSupport712_suffix_004, ridgeSupport712_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 15 32 323
    ridgeSupport712_rest_004 ridgeSupport712_rest_005 ridgeSupport712_rest_016
    ridgeSupport712_004 ridgeSupport712_suffix_005 ridgeSupport712_004_decode ridgeSupport712_suffix_decode_005
theorem ridgeSupport712_suffix_decode_003 : PackedRawNatGrowth.readList 15 387 ridgeSupport712_rest_003 =
    (ridgeSupport712_suffix_003, ridgeSupport712_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 15 32 355
    ridgeSupport712_rest_003 ridgeSupport712_rest_004 ridgeSupport712_rest_016
    ridgeSupport712_003 ridgeSupport712_suffix_004 ridgeSupport712_003_decode ridgeSupport712_suffix_decode_004
theorem ridgeSupport712_suffix_decode_002 : PackedRawNatGrowth.readList 15 419 ridgeSupport712_rest_002 =
    (ridgeSupport712_suffix_002, ridgeSupport712_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 15 32 387
    ridgeSupport712_rest_002 ridgeSupport712_rest_003 ridgeSupport712_rest_016
    ridgeSupport712_002 ridgeSupport712_suffix_003 ridgeSupport712_002_decode ridgeSupport712_suffix_decode_003
theorem ridgeSupport712_suffix_decode_001 : PackedRawNatGrowth.readList 15 451 ridgeSupport712_rest_001 =
    (ridgeSupport712_suffix_001, ridgeSupport712_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 15 32 419
    ridgeSupport712_rest_001 ridgeSupport712_rest_002 ridgeSupport712_rest_016
    ridgeSupport712_001 ridgeSupport712_suffix_002 ridgeSupport712_001_decode ridgeSupport712_suffix_decode_002
theorem ridgeSupport712_suffix_decode_000 : PackedRawNatGrowth.readList 15 483 ridgeSupport712_rest_000 =
    (ridgeSupport712_suffix_000, ridgeSupport712_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 15 32 451
    ridgeSupport712_rest_000 ridgeSupport712_rest_001 ridgeSupport712_rest_016
    ridgeSupport712_000 ridgeSupport712_suffix_001 ridgeSupport712_000_decode ridgeSupport712_suffix_decode_001
theorem ridgeSupport712_eq : candidateRows 712 = ridgeSupport712_suffix_000 := by
  rw [ridgeSupport712_source]
  exact congrArg Prod.fst ridgeSupport712_suffix_decode_000
theorem ridgeTest_large_712 : ridgeTest 712 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport712_eq]
    simp only [ridgeSupport712_suffix_000, ridgeSupport712_suffix_001, ridgeSupport712_suffix_002, ridgeSupport712_suffix_003, ridgeSupport712_suffix_004, ridgeSupport712_suffix_005, ridgeSupport712_suffix_006, ridgeSupport712_suffix_007, ridgeSupport712_suffix_008, ridgeSupport712_suffix_009, ridgeSupport712_suffix_010, ridgeSupport712_suffix_011, ridgeSupport712_suffix_012, ridgeSupport712_suffix_013, ridgeSupport712_suffix_014, ridgeSupport712_suffix_015, ridgeSupport712_suffix_016, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport712_000_mask, ridgeSupport712_001_mask, ridgeSupport712_002_mask, ridgeSupport712_003_mask, ridgeSupport712_004_mask, ridgeSupport712_005_mask, ridgeSupport712_006_mask, ridgeSupport712_007_mask, ridgeSupport712_008_mask, ridgeSupport712_009_mask, ridgeSupport712_010_mask, ridgeSupport712_011_mask, ridgeSupport712_012_mask, ridgeSupport712_013_mask, ridgeSupport712_014_mask, ridgeSupport712_015_mask]
    decide +kernel
  · rw [ridgeSupport712_eq]
    simp only [ridgeSupport712_suffix_000, ridgeSupport712_suffix_001, ridgeSupport712_suffix_002, ridgeSupport712_suffix_003, ridgeSupport712_suffix_004, ridgeSupport712_suffix_005, ridgeSupport712_suffix_006, ridgeSupport712_suffix_007, ridgeSupport712_suffix_008, ridgeSupport712_suffix_009, ridgeSupport712_suffix_010, ridgeSupport712_suffix_011, ridgeSupport712_suffix_012, ridgeSupport712_suffix_013, ridgeSupport712_suffix_014, ridgeSupport712_suffix_015, ridgeSupport712_suffix_016, List.all_append, List.all_nil, ridgeSupport712_000_checked, ridgeSupport712_001_checked, ridgeSupport712_002_checked, ridgeSupport712_003_checked, ridgeSupport712_004_checked, ridgeSupport712_005_checked, ridgeSupport712_006_checked, ridgeSupport712_007_checked, ridgeSupport712_008_checked, ridgeSupport712_009_checked, ridgeSupport712_010_checked, ridgeSupport712_011_checked, ridgeSupport712_012_checked, ridgeSupport712_013_checked, ridgeSupport712_014_checked, ridgeSupport712_015_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase00
