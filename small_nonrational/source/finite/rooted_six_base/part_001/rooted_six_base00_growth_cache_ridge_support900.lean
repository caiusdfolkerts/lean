module
prelude
public import RootedSixBase00GrowthCacheRidgeSupport900Part000
public import RootedSixBase00GrowthCacheRidgeSupport900Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport900_suffix_decode_016 : PackedRawNatGrowth.readList 15 0 ridgeSupport900_rest_016 =
    (ridgeSupport900_suffix_016, ridgeSupport900_rest_016) := by rfl
theorem ridgeSupport900_suffix_decode_015 : PackedRawNatGrowth.readList 15 3 ridgeSupport900_rest_015 =
    (ridgeSupport900_suffix_015, ridgeSupport900_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 15 3 0
    ridgeSupport900_rest_015 ridgeSupport900_rest_016 ridgeSupport900_rest_016
    ridgeSupport900_015 ridgeSupport900_suffix_016 ridgeSupport900_015_decode ridgeSupport900_suffix_decode_016
theorem ridgeSupport900_suffix_decode_014 : PackedRawNatGrowth.readList 15 35 ridgeSupport900_rest_014 =
    (ridgeSupport900_suffix_014, ridgeSupport900_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 15 32 3
    ridgeSupport900_rest_014 ridgeSupport900_rest_015 ridgeSupport900_rest_016
    ridgeSupport900_014 ridgeSupport900_suffix_015 ridgeSupport900_014_decode ridgeSupport900_suffix_decode_015
theorem ridgeSupport900_suffix_decode_013 : PackedRawNatGrowth.readList 15 67 ridgeSupport900_rest_013 =
    (ridgeSupport900_suffix_013, ridgeSupport900_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 15 32 35
    ridgeSupport900_rest_013 ridgeSupport900_rest_014 ridgeSupport900_rest_016
    ridgeSupport900_013 ridgeSupport900_suffix_014 ridgeSupport900_013_decode ridgeSupport900_suffix_decode_014
theorem ridgeSupport900_suffix_decode_012 : PackedRawNatGrowth.readList 15 99 ridgeSupport900_rest_012 =
    (ridgeSupport900_suffix_012, ridgeSupport900_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 15 32 67
    ridgeSupport900_rest_012 ridgeSupport900_rest_013 ridgeSupport900_rest_016
    ridgeSupport900_012 ridgeSupport900_suffix_013 ridgeSupport900_012_decode ridgeSupport900_suffix_decode_013
theorem ridgeSupport900_suffix_decode_011 : PackedRawNatGrowth.readList 15 131 ridgeSupport900_rest_011 =
    (ridgeSupport900_suffix_011, ridgeSupport900_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 15 32 99
    ridgeSupport900_rest_011 ridgeSupport900_rest_012 ridgeSupport900_rest_016
    ridgeSupport900_011 ridgeSupport900_suffix_012 ridgeSupport900_011_decode ridgeSupport900_suffix_decode_012
theorem ridgeSupport900_suffix_decode_010 : PackedRawNatGrowth.readList 15 163 ridgeSupport900_rest_010 =
    (ridgeSupport900_suffix_010, ridgeSupport900_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 15 32 131
    ridgeSupport900_rest_010 ridgeSupport900_rest_011 ridgeSupport900_rest_016
    ridgeSupport900_010 ridgeSupport900_suffix_011 ridgeSupport900_010_decode ridgeSupport900_suffix_decode_011
theorem ridgeSupport900_suffix_decode_009 : PackedRawNatGrowth.readList 15 195 ridgeSupport900_rest_009 =
    (ridgeSupport900_suffix_009, ridgeSupport900_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 15 32 163
    ridgeSupport900_rest_009 ridgeSupport900_rest_010 ridgeSupport900_rest_016
    ridgeSupport900_009 ridgeSupport900_suffix_010 ridgeSupport900_009_decode ridgeSupport900_suffix_decode_010
theorem ridgeSupport900_suffix_decode_008 : PackedRawNatGrowth.readList 15 227 ridgeSupport900_rest_008 =
    (ridgeSupport900_suffix_008, ridgeSupport900_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 15 32 195
    ridgeSupport900_rest_008 ridgeSupport900_rest_009 ridgeSupport900_rest_016
    ridgeSupport900_008 ridgeSupport900_suffix_009 ridgeSupport900_008_decode ridgeSupport900_suffix_decode_009
theorem ridgeSupport900_suffix_decode_007 : PackedRawNatGrowth.readList 15 259 ridgeSupport900_rest_007 =
    (ridgeSupport900_suffix_007, ridgeSupport900_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 15 32 227
    ridgeSupport900_rest_007 ridgeSupport900_rest_008 ridgeSupport900_rest_016
    ridgeSupport900_007 ridgeSupport900_suffix_008 ridgeSupport900_007_decode ridgeSupport900_suffix_decode_008
theorem ridgeSupport900_suffix_decode_006 : PackedRawNatGrowth.readList 15 291 ridgeSupport900_rest_006 =
    (ridgeSupport900_suffix_006, ridgeSupport900_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 15 32 259
    ridgeSupport900_rest_006 ridgeSupport900_rest_007 ridgeSupport900_rest_016
    ridgeSupport900_006 ridgeSupport900_suffix_007 ridgeSupport900_006_decode ridgeSupport900_suffix_decode_007
theorem ridgeSupport900_suffix_decode_005 : PackedRawNatGrowth.readList 15 323 ridgeSupport900_rest_005 =
    (ridgeSupport900_suffix_005, ridgeSupport900_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 15 32 291
    ridgeSupport900_rest_005 ridgeSupport900_rest_006 ridgeSupport900_rest_016
    ridgeSupport900_005 ridgeSupport900_suffix_006 ridgeSupport900_005_decode ridgeSupport900_suffix_decode_006
theorem ridgeSupport900_suffix_decode_004 : PackedRawNatGrowth.readList 15 355 ridgeSupport900_rest_004 =
    (ridgeSupport900_suffix_004, ridgeSupport900_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 15 32 323
    ridgeSupport900_rest_004 ridgeSupport900_rest_005 ridgeSupport900_rest_016
    ridgeSupport900_004 ridgeSupport900_suffix_005 ridgeSupport900_004_decode ridgeSupport900_suffix_decode_005
theorem ridgeSupport900_suffix_decode_003 : PackedRawNatGrowth.readList 15 387 ridgeSupport900_rest_003 =
    (ridgeSupport900_suffix_003, ridgeSupport900_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 15 32 355
    ridgeSupport900_rest_003 ridgeSupport900_rest_004 ridgeSupport900_rest_016
    ridgeSupport900_003 ridgeSupport900_suffix_004 ridgeSupport900_003_decode ridgeSupport900_suffix_decode_004
theorem ridgeSupport900_suffix_decode_002 : PackedRawNatGrowth.readList 15 419 ridgeSupport900_rest_002 =
    (ridgeSupport900_suffix_002, ridgeSupport900_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 15 32 387
    ridgeSupport900_rest_002 ridgeSupport900_rest_003 ridgeSupport900_rest_016
    ridgeSupport900_002 ridgeSupport900_suffix_003 ridgeSupport900_002_decode ridgeSupport900_suffix_decode_003
theorem ridgeSupport900_suffix_decode_001 : PackedRawNatGrowth.readList 15 451 ridgeSupport900_rest_001 =
    (ridgeSupport900_suffix_001, ridgeSupport900_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 15 32 419
    ridgeSupport900_rest_001 ridgeSupport900_rest_002 ridgeSupport900_rest_016
    ridgeSupport900_001 ridgeSupport900_suffix_002 ridgeSupport900_001_decode ridgeSupport900_suffix_decode_002
theorem ridgeSupport900_suffix_decode_000 : PackedRawNatGrowth.readList 15 483 ridgeSupport900_rest_000 =
    (ridgeSupport900_suffix_000, ridgeSupport900_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 15 32 451
    ridgeSupport900_rest_000 ridgeSupport900_rest_001 ridgeSupport900_rest_016
    ridgeSupport900_000 ridgeSupport900_suffix_001 ridgeSupport900_000_decode ridgeSupport900_suffix_decode_001
theorem ridgeSupport900_eq : candidateRows 900 = ridgeSupport900_suffix_000 := by
  rw [ridgeSupport900_source]
  exact congrArg Prod.fst ridgeSupport900_suffix_decode_000
theorem ridgeTest_large_900 : ridgeTest 900 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport900_eq]
    simp only [ridgeSupport900_suffix_000, ridgeSupport900_suffix_001, ridgeSupport900_suffix_002, ridgeSupport900_suffix_003, ridgeSupport900_suffix_004, ridgeSupport900_suffix_005, ridgeSupport900_suffix_006, ridgeSupport900_suffix_007, ridgeSupport900_suffix_008, ridgeSupport900_suffix_009, ridgeSupport900_suffix_010, ridgeSupport900_suffix_011, ridgeSupport900_suffix_012, ridgeSupport900_suffix_013, ridgeSupport900_suffix_014, ridgeSupport900_suffix_015, ridgeSupport900_suffix_016, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport900_000_mask, ridgeSupport900_001_mask, ridgeSupport900_002_mask, ridgeSupport900_003_mask, ridgeSupport900_004_mask, ridgeSupport900_005_mask, ridgeSupport900_006_mask, ridgeSupport900_007_mask, ridgeSupport900_008_mask, ridgeSupport900_009_mask, ridgeSupport900_010_mask, ridgeSupport900_011_mask, ridgeSupport900_012_mask, ridgeSupport900_013_mask, ridgeSupport900_014_mask, ridgeSupport900_015_mask]
    decide +kernel
  · rw [ridgeSupport900_eq]
    simp only [ridgeSupport900_suffix_000, ridgeSupport900_suffix_001, ridgeSupport900_suffix_002, ridgeSupport900_suffix_003, ridgeSupport900_suffix_004, ridgeSupport900_suffix_005, ridgeSupport900_suffix_006, ridgeSupport900_suffix_007, ridgeSupport900_suffix_008, ridgeSupport900_suffix_009, ridgeSupport900_suffix_010, ridgeSupport900_suffix_011, ridgeSupport900_suffix_012, ridgeSupport900_suffix_013, ridgeSupport900_suffix_014, ridgeSupport900_suffix_015, ridgeSupport900_suffix_016, List.all_append, List.all_nil, ridgeSupport900_000_checked, ridgeSupport900_001_checked, ridgeSupport900_002_checked, ridgeSupport900_003_checked, ridgeSupport900_004_checked, ridgeSupport900_005_checked, ridgeSupport900_006_checked, ridgeSupport900_007_checked, ridgeSupport900_008_checked, ridgeSupport900_009_checked, ridgeSupport900_010_checked, ridgeSupport900_011_checked, ridgeSupport900_012_checked, ridgeSupport900_013_checked, ridgeSupport900_014_checked, ridgeSupport900_015_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase00
