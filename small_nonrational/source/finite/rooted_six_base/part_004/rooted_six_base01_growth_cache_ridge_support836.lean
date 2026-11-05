module
prelude
public import RootedSixBase01GrowthCacheRidgeSupport836Part000
public import RootedSixBase01GrowthCacheRidgeSupport836Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport836_suffix_decode_016 : PackedRawNatGrowth.readList 14 0 ridgeSupport836_rest_016 =
    (ridgeSupport836_suffix_016, ridgeSupport836_rest_016) := by rfl
theorem ridgeSupport836_suffix_decode_015 : PackedRawNatGrowth.readList 14 3 ridgeSupport836_rest_015 =
    (ridgeSupport836_suffix_015, ridgeSupport836_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 3 0
    ridgeSupport836_rest_015 ridgeSupport836_rest_016 ridgeSupport836_rest_016
    ridgeSupport836_015 ridgeSupport836_suffix_016 ridgeSupport836_015_decode ridgeSupport836_suffix_decode_016
theorem ridgeSupport836_suffix_decode_014 : PackedRawNatGrowth.readList 14 35 ridgeSupport836_rest_014 =
    (ridgeSupport836_suffix_014, ridgeSupport836_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 3
    ridgeSupport836_rest_014 ridgeSupport836_rest_015 ridgeSupport836_rest_016
    ridgeSupport836_014 ridgeSupport836_suffix_015 ridgeSupport836_014_decode ridgeSupport836_suffix_decode_015
theorem ridgeSupport836_suffix_decode_013 : PackedRawNatGrowth.readList 14 67 ridgeSupport836_rest_013 =
    (ridgeSupport836_suffix_013, ridgeSupport836_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 35
    ridgeSupport836_rest_013 ridgeSupport836_rest_014 ridgeSupport836_rest_016
    ridgeSupport836_013 ridgeSupport836_suffix_014 ridgeSupport836_013_decode ridgeSupport836_suffix_decode_014
theorem ridgeSupport836_suffix_decode_012 : PackedRawNatGrowth.readList 14 99 ridgeSupport836_rest_012 =
    (ridgeSupport836_suffix_012, ridgeSupport836_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 67
    ridgeSupport836_rest_012 ridgeSupport836_rest_013 ridgeSupport836_rest_016
    ridgeSupport836_012 ridgeSupport836_suffix_013 ridgeSupport836_012_decode ridgeSupport836_suffix_decode_013
theorem ridgeSupport836_suffix_decode_011 : PackedRawNatGrowth.readList 14 131 ridgeSupport836_rest_011 =
    (ridgeSupport836_suffix_011, ridgeSupport836_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 99
    ridgeSupport836_rest_011 ridgeSupport836_rest_012 ridgeSupport836_rest_016
    ridgeSupport836_011 ridgeSupport836_suffix_012 ridgeSupport836_011_decode ridgeSupport836_suffix_decode_012
theorem ridgeSupport836_suffix_decode_010 : PackedRawNatGrowth.readList 14 163 ridgeSupport836_rest_010 =
    (ridgeSupport836_suffix_010, ridgeSupport836_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 131
    ridgeSupport836_rest_010 ridgeSupport836_rest_011 ridgeSupport836_rest_016
    ridgeSupport836_010 ridgeSupport836_suffix_011 ridgeSupport836_010_decode ridgeSupport836_suffix_decode_011
theorem ridgeSupport836_suffix_decode_009 : PackedRawNatGrowth.readList 14 195 ridgeSupport836_rest_009 =
    (ridgeSupport836_suffix_009, ridgeSupport836_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 163
    ridgeSupport836_rest_009 ridgeSupport836_rest_010 ridgeSupport836_rest_016
    ridgeSupport836_009 ridgeSupport836_suffix_010 ridgeSupport836_009_decode ridgeSupport836_suffix_decode_010
theorem ridgeSupport836_suffix_decode_008 : PackedRawNatGrowth.readList 14 227 ridgeSupport836_rest_008 =
    (ridgeSupport836_suffix_008, ridgeSupport836_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 195
    ridgeSupport836_rest_008 ridgeSupport836_rest_009 ridgeSupport836_rest_016
    ridgeSupport836_008 ridgeSupport836_suffix_009 ridgeSupport836_008_decode ridgeSupport836_suffix_decode_009
theorem ridgeSupport836_suffix_decode_007 : PackedRawNatGrowth.readList 14 259 ridgeSupport836_rest_007 =
    (ridgeSupport836_suffix_007, ridgeSupport836_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 227
    ridgeSupport836_rest_007 ridgeSupport836_rest_008 ridgeSupport836_rest_016
    ridgeSupport836_007 ridgeSupport836_suffix_008 ridgeSupport836_007_decode ridgeSupport836_suffix_decode_008
theorem ridgeSupport836_suffix_decode_006 : PackedRawNatGrowth.readList 14 291 ridgeSupport836_rest_006 =
    (ridgeSupport836_suffix_006, ridgeSupport836_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 259
    ridgeSupport836_rest_006 ridgeSupport836_rest_007 ridgeSupport836_rest_016
    ridgeSupport836_006 ridgeSupport836_suffix_007 ridgeSupport836_006_decode ridgeSupport836_suffix_decode_007
theorem ridgeSupport836_suffix_decode_005 : PackedRawNatGrowth.readList 14 323 ridgeSupport836_rest_005 =
    (ridgeSupport836_suffix_005, ridgeSupport836_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 291
    ridgeSupport836_rest_005 ridgeSupport836_rest_006 ridgeSupport836_rest_016
    ridgeSupport836_005 ridgeSupport836_suffix_006 ridgeSupport836_005_decode ridgeSupport836_suffix_decode_006
theorem ridgeSupport836_suffix_decode_004 : PackedRawNatGrowth.readList 14 355 ridgeSupport836_rest_004 =
    (ridgeSupport836_suffix_004, ridgeSupport836_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 323
    ridgeSupport836_rest_004 ridgeSupport836_rest_005 ridgeSupport836_rest_016
    ridgeSupport836_004 ridgeSupport836_suffix_005 ridgeSupport836_004_decode ridgeSupport836_suffix_decode_005
theorem ridgeSupport836_suffix_decode_003 : PackedRawNatGrowth.readList 14 387 ridgeSupport836_rest_003 =
    (ridgeSupport836_suffix_003, ridgeSupport836_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 355
    ridgeSupport836_rest_003 ridgeSupport836_rest_004 ridgeSupport836_rest_016
    ridgeSupport836_003 ridgeSupport836_suffix_004 ridgeSupport836_003_decode ridgeSupport836_suffix_decode_004
theorem ridgeSupport836_suffix_decode_002 : PackedRawNatGrowth.readList 14 419 ridgeSupport836_rest_002 =
    (ridgeSupport836_suffix_002, ridgeSupport836_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 387
    ridgeSupport836_rest_002 ridgeSupport836_rest_003 ridgeSupport836_rest_016
    ridgeSupport836_002 ridgeSupport836_suffix_003 ridgeSupport836_002_decode ridgeSupport836_suffix_decode_003
theorem ridgeSupport836_suffix_decode_001 : PackedRawNatGrowth.readList 14 451 ridgeSupport836_rest_001 =
    (ridgeSupport836_suffix_001, ridgeSupport836_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 419
    ridgeSupport836_rest_001 ridgeSupport836_rest_002 ridgeSupport836_rest_016
    ridgeSupport836_001 ridgeSupport836_suffix_002 ridgeSupport836_001_decode ridgeSupport836_suffix_decode_002
theorem ridgeSupport836_suffix_decode_000 : PackedRawNatGrowth.readList 14 483 ridgeSupport836_rest_000 =
    (ridgeSupport836_suffix_000, ridgeSupport836_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 451
    ridgeSupport836_rest_000 ridgeSupport836_rest_001 ridgeSupport836_rest_016
    ridgeSupport836_000 ridgeSupport836_suffix_001 ridgeSupport836_000_decode ridgeSupport836_suffix_decode_001
theorem ridgeSupport836_eq : candidateRows 836 = ridgeSupport836_suffix_000 := by
  rw [ridgeSupport836_source]
  exact congrArg Prod.fst ridgeSupport836_suffix_decode_000
theorem ridgeTest_large_836 : ridgeTest 836 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport836_eq]
    simp only [ridgeSupport836_suffix_000, ridgeSupport836_suffix_001, ridgeSupport836_suffix_002, ridgeSupport836_suffix_003, ridgeSupport836_suffix_004, ridgeSupport836_suffix_005, ridgeSupport836_suffix_006, ridgeSupport836_suffix_007, ridgeSupport836_suffix_008, ridgeSupport836_suffix_009, ridgeSupport836_suffix_010, ridgeSupport836_suffix_011, ridgeSupport836_suffix_012, ridgeSupport836_suffix_013, ridgeSupport836_suffix_014, ridgeSupport836_suffix_015, ridgeSupport836_suffix_016, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport836_000_mask, ridgeSupport836_001_mask, ridgeSupport836_002_mask, ridgeSupport836_003_mask, ridgeSupport836_004_mask, ridgeSupport836_005_mask, ridgeSupport836_006_mask, ridgeSupport836_007_mask, ridgeSupport836_008_mask, ridgeSupport836_009_mask, ridgeSupport836_010_mask, ridgeSupport836_011_mask, ridgeSupport836_012_mask, ridgeSupport836_013_mask, ridgeSupport836_014_mask, ridgeSupport836_015_mask]
    decide +kernel
  · rw [ridgeSupport836_eq]
    simp only [ridgeSupport836_suffix_000, ridgeSupport836_suffix_001, ridgeSupport836_suffix_002, ridgeSupport836_suffix_003, ridgeSupport836_suffix_004, ridgeSupport836_suffix_005, ridgeSupport836_suffix_006, ridgeSupport836_suffix_007, ridgeSupport836_suffix_008, ridgeSupport836_suffix_009, ridgeSupport836_suffix_010, ridgeSupport836_suffix_011, ridgeSupport836_suffix_012, ridgeSupport836_suffix_013, ridgeSupport836_suffix_014, ridgeSupport836_suffix_015, ridgeSupport836_suffix_016, List.all_append, List.all_nil, ridgeSupport836_000_checked, ridgeSupport836_001_checked, ridgeSupport836_002_checked, ridgeSupport836_003_checked, ridgeSupport836_004_checked, ridgeSupport836_005_checked, ridgeSupport836_006_checked, ridgeSupport836_007_checked, ridgeSupport836_008_checked, ridgeSupport836_009_checked, ridgeSupport836_010_checked, ridgeSupport836_011_checked, ridgeSupport836_012_checked, ridgeSupport836_013_checked, ridgeSupport836_014_checked, ridgeSupport836_015_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase01
