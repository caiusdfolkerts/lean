module
prelude
public import RootedSixBase00GrowthCacheRidgeSupport904Part000
public import RootedSixBase00GrowthCacheRidgeSupport904Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport904_suffix_decode_016 : PackedRawNatGrowth.readList 15 0 ridgeSupport904_rest_016 =
    (ridgeSupport904_suffix_016, ridgeSupport904_rest_016) := by rfl
theorem ridgeSupport904_suffix_decode_015 : PackedRawNatGrowth.readList 15 3 ridgeSupport904_rest_015 =
    (ridgeSupport904_suffix_015, ridgeSupport904_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 15 3 0
    ridgeSupport904_rest_015 ridgeSupport904_rest_016 ridgeSupport904_rest_016
    ridgeSupport904_015 ridgeSupport904_suffix_016 ridgeSupport904_015_decode ridgeSupport904_suffix_decode_016
theorem ridgeSupport904_suffix_decode_014 : PackedRawNatGrowth.readList 15 35 ridgeSupport904_rest_014 =
    (ridgeSupport904_suffix_014, ridgeSupport904_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 15 32 3
    ridgeSupport904_rest_014 ridgeSupport904_rest_015 ridgeSupport904_rest_016
    ridgeSupport904_014 ridgeSupport904_suffix_015 ridgeSupport904_014_decode ridgeSupport904_suffix_decode_015
theorem ridgeSupport904_suffix_decode_013 : PackedRawNatGrowth.readList 15 67 ridgeSupport904_rest_013 =
    (ridgeSupport904_suffix_013, ridgeSupport904_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 15 32 35
    ridgeSupport904_rest_013 ridgeSupport904_rest_014 ridgeSupport904_rest_016
    ridgeSupport904_013 ridgeSupport904_suffix_014 ridgeSupport904_013_decode ridgeSupport904_suffix_decode_014
theorem ridgeSupport904_suffix_decode_012 : PackedRawNatGrowth.readList 15 99 ridgeSupport904_rest_012 =
    (ridgeSupport904_suffix_012, ridgeSupport904_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 15 32 67
    ridgeSupport904_rest_012 ridgeSupport904_rest_013 ridgeSupport904_rest_016
    ridgeSupport904_012 ridgeSupport904_suffix_013 ridgeSupport904_012_decode ridgeSupport904_suffix_decode_013
theorem ridgeSupport904_suffix_decode_011 : PackedRawNatGrowth.readList 15 131 ridgeSupport904_rest_011 =
    (ridgeSupport904_suffix_011, ridgeSupport904_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 15 32 99
    ridgeSupport904_rest_011 ridgeSupport904_rest_012 ridgeSupport904_rest_016
    ridgeSupport904_011 ridgeSupport904_suffix_012 ridgeSupport904_011_decode ridgeSupport904_suffix_decode_012
theorem ridgeSupport904_suffix_decode_010 : PackedRawNatGrowth.readList 15 163 ridgeSupport904_rest_010 =
    (ridgeSupport904_suffix_010, ridgeSupport904_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 15 32 131
    ridgeSupport904_rest_010 ridgeSupport904_rest_011 ridgeSupport904_rest_016
    ridgeSupport904_010 ridgeSupport904_suffix_011 ridgeSupport904_010_decode ridgeSupport904_suffix_decode_011
theorem ridgeSupport904_suffix_decode_009 : PackedRawNatGrowth.readList 15 195 ridgeSupport904_rest_009 =
    (ridgeSupport904_suffix_009, ridgeSupport904_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 15 32 163
    ridgeSupport904_rest_009 ridgeSupport904_rest_010 ridgeSupport904_rest_016
    ridgeSupport904_009 ridgeSupport904_suffix_010 ridgeSupport904_009_decode ridgeSupport904_suffix_decode_010
theorem ridgeSupport904_suffix_decode_008 : PackedRawNatGrowth.readList 15 227 ridgeSupport904_rest_008 =
    (ridgeSupport904_suffix_008, ridgeSupport904_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 15 32 195
    ridgeSupport904_rest_008 ridgeSupport904_rest_009 ridgeSupport904_rest_016
    ridgeSupport904_008 ridgeSupport904_suffix_009 ridgeSupport904_008_decode ridgeSupport904_suffix_decode_009
theorem ridgeSupport904_suffix_decode_007 : PackedRawNatGrowth.readList 15 259 ridgeSupport904_rest_007 =
    (ridgeSupport904_suffix_007, ridgeSupport904_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 15 32 227
    ridgeSupport904_rest_007 ridgeSupport904_rest_008 ridgeSupport904_rest_016
    ridgeSupport904_007 ridgeSupport904_suffix_008 ridgeSupport904_007_decode ridgeSupport904_suffix_decode_008
theorem ridgeSupport904_suffix_decode_006 : PackedRawNatGrowth.readList 15 291 ridgeSupport904_rest_006 =
    (ridgeSupport904_suffix_006, ridgeSupport904_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 15 32 259
    ridgeSupport904_rest_006 ridgeSupport904_rest_007 ridgeSupport904_rest_016
    ridgeSupport904_006 ridgeSupport904_suffix_007 ridgeSupport904_006_decode ridgeSupport904_suffix_decode_007
theorem ridgeSupport904_suffix_decode_005 : PackedRawNatGrowth.readList 15 323 ridgeSupport904_rest_005 =
    (ridgeSupport904_suffix_005, ridgeSupport904_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 15 32 291
    ridgeSupport904_rest_005 ridgeSupport904_rest_006 ridgeSupport904_rest_016
    ridgeSupport904_005 ridgeSupport904_suffix_006 ridgeSupport904_005_decode ridgeSupport904_suffix_decode_006
theorem ridgeSupport904_suffix_decode_004 : PackedRawNatGrowth.readList 15 355 ridgeSupport904_rest_004 =
    (ridgeSupport904_suffix_004, ridgeSupport904_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 15 32 323
    ridgeSupport904_rest_004 ridgeSupport904_rest_005 ridgeSupport904_rest_016
    ridgeSupport904_004 ridgeSupport904_suffix_005 ridgeSupport904_004_decode ridgeSupport904_suffix_decode_005
theorem ridgeSupport904_suffix_decode_003 : PackedRawNatGrowth.readList 15 387 ridgeSupport904_rest_003 =
    (ridgeSupport904_suffix_003, ridgeSupport904_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 15 32 355
    ridgeSupport904_rest_003 ridgeSupport904_rest_004 ridgeSupport904_rest_016
    ridgeSupport904_003 ridgeSupport904_suffix_004 ridgeSupport904_003_decode ridgeSupport904_suffix_decode_004
theorem ridgeSupport904_suffix_decode_002 : PackedRawNatGrowth.readList 15 419 ridgeSupport904_rest_002 =
    (ridgeSupport904_suffix_002, ridgeSupport904_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 15 32 387
    ridgeSupport904_rest_002 ridgeSupport904_rest_003 ridgeSupport904_rest_016
    ridgeSupport904_002 ridgeSupport904_suffix_003 ridgeSupport904_002_decode ridgeSupport904_suffix_decode_003
theorem ridgeSupport904_suffix_decode_001 : PackedRawNatGrowth.readList 15 451 ridgeSupport904_rest_001 =
    (ridgeSupport904_suffix_001, ridgeSupport904_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 15 32 419
    ridgeSupport904_rest_001 ridgeSupport904_rest_002 ridgeSupport904_rest_016
    ridgeSupport904_001 ridgeSupport904_suffix_002 ridgeSupport904_001_decode ridgeSupport904_suffix_decode_002
theorem ridgeSupport904_suffix_decode_000 : PackedRawNatGrowth.readList 15 483 ridgeSupport904_rest_000 =
    (ridgeSupport904_suffix_000, ridgeSupport904_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 15 32 451
    ridgeSupport904_rest_000 ridgeSupport904_rest_001 ridgeSupport904_rest_016
    ridgeSupport904_000 ridgeSupport904_suffix_001 ridgeSupport904_000_decode ridgeSupport904_suffix_decode_001
theorem ridgeSupport904_eq : candidateRows 904 = ridgeSupport904_suffix_000 := by
  rw [ridgeSupport904_source]
  exact congrArg Prod.fst ridgeSupport904_suffix_decode_000
theorem ridgeTest_large_904 : ridgeTest 904 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport904_eq]
    simp only [ridgeSupport904_suffix_000, ridgeSupport904_suffix_001, ridgeSupport904_suffix_002, ridgeSupport904_suffix_003, ridgeSupport904_suffix_004, ridgeSupport904_suffix_005, ridgeSupport904_suffix_006, ridgeSupport904_suffix_007, ridgeSupport904_suffix_008, ridgeSupport904_suffix_009, ridgeSupport904_suffix_010, ridgeSupport904_suffix_011, ridgeSupport904_suffix_012, ridgeSupport904_suffix_013, ridgeSupport904_suffix_014, ridgeSupport904_suffix_015, ridgeSupport904_suffix_016, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport904_000_mask, ridgeSupport904_001_mask, ridgeSupport904_002_mask, ridgeSupport904_003_mask, ridgeSupport904_004_mask, ridgeSupport904_005_mask, ridgeSupport904_006_mask, ridgeSupport904_007_mask, ridgeSupport904_008_mask, ridgeSupport904_009_mask, ridgeSupport904_010_mask, ridgeSupport904_011_mask, ridgeSupport904_012_mask, ridgeSupport904_013_mask, ridgeSupport904_014_mask, ridgeSupport904_015_mask]
    decide +kernel
  · rw [ridgeSupport904_eq]
    simp only [ridgeSupport904_suffix_000, ridgeSupport904_suffix_001, ridgeSupport904_suffix_002, ridgeSupport904_suffix_003, ridgeSupport904_suffix_004, ridgeSupport904_suffix_005, ridgeSupport904_suffix_006, ridgeSupport904_suffix_007, ridgeSupport904_suffix_008, ridgeSupport904_suffix_009, ridgeSupport904_suffix_010, ridgeSupport904_suffix_011, ridgeSupport904_suffix_012, ridgeSupport904_suffix_013, ridgeSupport904_suffix_014, ridgeSupport904_suffix_015, ridgeSupport904_suffix_016, List.all_append, List.all_nil, ridgeSupport904_000_checked, ridgeSupport904_001_checked, ridgeSupport904_002_checked, ridgeSupport904_003_checked, ridgeSupport904_004_checked, ridgeSupport904_005_checked, ridgeSupport904_006_checked, ridgeSupport904_007_checked, ridgeSupport904_008_checked, ridgeSupport904_009_checked, ridgeSupport904_010_checked, ridgeSupport904_011_checked, ridgeSupport904_012_checked, ridgeSupport904_013_checked, ridgeSupport904_014_checked, ridgeSupport904_015_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase00
