module
prelude
public import RootedSixBase00GrowthCacheRidgeSupport840Part000
public import RootedSixBase00GrowthCacheRidgeSupport840Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport840_suffix_decode_016 : PackedRawNatGrowth.readList 15 0 ridgeSupport840_rest_016 =
    (ridgeSupport840_suffix_016, ridgeSupport840_rest_016) := by rfl
theorem ridgeSupport840_suffix_decode_015 : PackedRawNatGrowth.readList 15 3 ridgeSupport840_rest_015 =
    (ridgeSupport840_suffix_015, ridgeSupport840_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 15 3 0
    ridgeSupport840_rest_015 ridgeSupport840_rest_016 ridgeSupport840_rest_016
    ridgeSupport840_015 ridgeSupport840_suffix_016 ridgeSupport840_015_decode ridgeSupport840_suffix_decode_016
theorem ridgeSupport840_suffix_decode_014 : PackedRawNatGrowth.readList 15 35 ridgeSupport840_rest_014 =
    (ridgeSupport840_suffix_014, ridgeSupport840_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 15 32 3
    ridgeSupport840_rest_014 ridgeSupport840_rest_015 ridgeSupport840_rest_016
    ridgeSupport840_014 ridgeSupport840_suffix_015 ridgeSupport840_014_decode ridgeSupport840_suffix_decode_015
theorem ridgeSupport840_suffix_decode_013 : PackedRawNatGrowth.readList 15 67 ridgeSupport840_rest_013 =
    (ridgeSupport840_suffix_013, ridgeSupport840_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 15 32 35
    ridgeSupport840_rest_013 ridgeSupport840_rest_014 ridgeSupport840_rest_016
    ridgeSupport840_013 ridgeSupport840_suffix_014 ridgeSupport840_013_decode ridgeSupport840_suffix_decode_014
theorem ridgeSupport840_suffix_decode_012 : PackedRawNatGrowth.readList 15 99 ridgeSupport840_rest_012 =
    (ridgeSupport840_suffix_012, ridgeSupport840_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 15 32 67
    ridgeSupport840_rest_012 ridgeSupport840_rest_013 ridgeSupport840_rest_016
    ridgeSupport840_012 ridgeSupport840_suffix_013 ridgeSupport840_012_decode ridgeSupport840_suffix_decode_013
theorem ridgeSupport840_suffix_decode_011 : PackedRawNatGrowth.readList 15 131 ridgeSupport840_rest_011 =
    (ridgeSupport840_suffix_011, ridgeSupport840_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 15 32 99
    ridgeSupport840_rest_011 ridgeSupport840_rest_012 ridgeSupport840_rest_016
    ridgeSupport840_011 ridgeSupport840_suffix_012 ridgeSupport840_011_decode ridgeSupport840_suffix_decode_012
theorem ridgeSupport840_suffix_decode_010 : PackedRawNatGrowth.readList 15 163 ridgeSupport840_rest_010 =
    (ridgeSupport840_suffix_010, ridgeSupport840_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 15 32 131
    ridgeSupport840_rest_010 ridgeSupport840_rest_011 ridgeSupport840_rest_016
    ridgeSupport840_010 ridgeSupport840_suffix_011 ridgeSupport840_010_decode ridgeSupport840_suffix_decode_011
theorem ridgeSupport840_suffix_decode_009 : PackedRawNatGrowth.readList 15 195 ridgeSupport840_rest_009 =
    (ridgeSupport840_suffix_009, ridgeSupport840_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 15 32 163
    ridgeSupport840_rest_009 ridgeSupport840_rest_010 ridgeSupport840_rest_016
    ridgeSupport840_009 ridgeSupport840_suffix_010 ridgeSupport840_009_decode ridgeSupport840_suffix_decode_010
theorem ridgeSupport840_suffix_decode_008 : PackedRawNatGrowth.readList 15 227 ridgeSupport840_rest_008 =
    (ridgeSupport840_suffix_008, ridgeSupport840_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 15 32 195
    ridgeSupport840_rest_008 ridgeSupport840_rest_009 ridgeSupport840_rest_016
    ridgeSupport840_008 ridgeSupport840_suffix_009 ridgeSupport840_008_decode ridgeSupport840_suffix_decode_009
theorem ridgeSupport840_suffix_decode_007 : PackedRawNatGrowth.readList 15 259 ridgeSupport840_rest_007 =
    (ridgeSupport840_suffix_007, ridgeSupport840_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 15 32 227
    ridgeSupport840_rest_007 ridgeSupport840_rest_008 ridgeSupport840_rest_016
    ridgeSupport840_007 ridgeSupport840_suffix_008 ridgeSupport840_007_decode ridgeSupport840_suffix_decode_008
theorem ridgeSupport840_suffix_decode_006 : PackedRawNatGrowth.readList 15 291 ridgeSupport840_rest_006 =
    (ridgeSupport840_suffix_006, ridgeSupport840_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 15 32 259
    ridgeSupport840_rest_006 ridgeSupport840_rest_007 ridgeSupport840_rest_016
    ridgeSupport840_006 ridgeSupport840_suffix_007 ridgeSupport840_006_decode ridgeSupport840_suffix_decode_007
theorem ridgeSupport840_suffix_decode_005 : PackedRawNatGrowth.readList 15 323 ridgeSupport840_rest_005 =
    (ridgeSupport840_suffix_005, ridgeSupport840_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 15 32 291
    ridgeSupport840_rest_005 ridgeSupport840_rest_006 ridgeSupport840_rest_016
    ridgeSupport840_005 ridgeSupport840_suffix_006 ridgeSupport840_005_decode ridgeSupport840_suffix_decode_006
theorem ridgeSupport840_suffix_decode_004 : PackedRawNatGrowth.readList 15 355 ridgeSupport840_rest_004 =
    (ridgeSupport840_suffix_004, ridgeSupport840_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 15 32 323
    ridgeSupport840_rest_004 ridgeSupport840_rest_005 ridgeSupport840_rest_016
    ridgeSupport840_004 ridgeSupport840_suffix_005 ridgeSupport840_004_decode ridgeSupport840_suffix_decode_005
theorem ridgeSupport840_suffix_decode_003 : PackedRawNatGrowth.readList 15 387 ridgeSupport840_rest_003 =
    (ridgeSupport840_suffix_003, ridgeSupport840_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 15 32 355
    ridgeSupport840_rest_003 ridgeSupport840_rest_004 ridgeSupport840_rest_016
    ridgeSupport840_003 ridgeSupport840_suffix_004 ridgeSupport840_003_decode ridgeSupport840_suffix_decode_004
theorem ridgeSupport840_suffix_decode_002 : PackedRawNatGrowth.readList 15 419 ridgeSupport840_rest_002 =
    (ridgeSupport840_suffix_002, ridgeSupport840_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 15 32 387
    ridgeSupport840_rest_002 ridgeSupport840_rest_003 ridgeSupport840_rest_016
    ridgeSupport840_002 ridgeSupport840_suffix_003 ridgeSupport840_002_decode ridgeSupport840_suffix_decode_003
theorem ridgeSupport840_suffix_decode_001 : PackedRawNatGrowth.readList 15 451 ridgeSupport840_rest_001 =
    (ridgeSupport840_suffix_001, ridgeSupport840_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 15 32 419
    ridgeSupport840_rest_001 ridgeSupport840_rest_002 ridgeSupport840_rest_016
    ridgeSupport840_001 ridgeSupport840_suffix_002 ridgeSupport840_001_decode ridgeSupport840_suffix_decode_002
theorem ridgeSupport840_suffix_decode_000 : PackedRawNatGrowth.readList 15 483 ridgeSupport840_rest_000 =
    (ridgeSupport840_suffix_000, ridgeSupport840_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 15 32 451
    ridgeSupport840_rest_000 ridgeSupport840_rest_001 ridgeSupport840_rest_016
    ridgeSupport840_000 ridgeSupport840_suffix_001 ridgeSupport840_000_decode ridgeSupport840_suffix_decode_001
theorem ridgeSupport840_eq : candidateRows 840 = ridgeSupport840_suffix_000 := by
  rw [ridgeSupport840_source]
  exact congrArg Prod.fst ridgeSupport840_suffix_decode_000
theorem ridgeTest_large_840 : ridgeTest 840 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport840_eq]
    simp only [ridgeSupport840_suffix_000, ridgeSupport840_suffix_001, ridgeSupport840_suffix_002, ridgeSupport840_suffix_003, ridgeSupport840_suffix_004, ridgeSupport840_suffix_005, ridgeSupport840_suffix_006, ridgeSupport840_suffix_007, ridgeSupport840_suffix_008, ridgeSupport840_suffix_009, ridgeSupport840_suffix_010, ridgeSupport840_suffix_011, ridgeSupport840_suffix_012, ridgeSupport840_suffix_013, ridgeSupport840_suffix_014, ridgeSupport840_suffix_015, ridgeSupport840_suffix_016, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport840_000_mask, ridgeSupport840_001_mask, ridgeSupport840_002_mask, ridgeSupport840_003_mask, ridgeSupport840_004_mask, ridgeSupport840_005_mask, ridgeSupport840_006_mask, ridgeSupport840_007_mask, ridgeSupport840_008_mask, ridgeSupport840_009_mask, ridgeSupport840_010_mask, ridgeSupport840_011_mask, ridgeSupport840_012_mask, ridgeSupport840_013_mask, ridgeSupport840_014_mask, ridgeSupport840_015_mask]
    decide +kernel
  · rw [ridgeSupport840_eq]
    simp only [ridgeSupport840_suffix_000, ridgeSupport840_suffix_001, ridgeSupport840_suffix_002, ridgeSupport840_suffix_003, ridgeSupport840_suffix_004, ridgeSupport840_suffix_005, ridgeSupport840_suffix_006, ridgeSupport840_suffix_007, ridgeSupport840_suffix_008, ridgeSupport840_suffix_009, ridgeSupport840_suffix_010, ridgeSupport840_suffix_011, ridgeSupport840_suffix_012, ridgeSupport840_suffix_013, ridgeSupport840_suffix_014, ridgeSupport840_suffix_015, ridgeSupport840_suffix_016, List.all_append, List.all_nil, ridgeSupport840_000_checked, ridgeSupport840_001_checked, ridgeSupport840_002_checked, ridgeSupport840_003_checked, ridgeSupport840_004_checked, ridgeSupport840_005_checked, ridgeSupport840_006_checked, ridgeSupport840_007_checked, ridgeSupport840_008_checked, ridgeSupport840_009_checked, ridgeSupport840_010_checked, ridgeSupport840_011_checked, ridgeSupport840_012_checked, ridgeSupport840_013_checked, ridgeSupport840_014_checked, ridgeSupport840_015_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase00
