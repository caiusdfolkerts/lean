module
prelude
public import RootedSixBase00GrowthCacheRidgeSupport464Part000
public import RootedSixBase00GrowthCacheRidgeSupport464Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport464_suffix_decode_013 : PackedRawNatGrowth.readList 15 0 ridgeSupport464_rest_013 =
    (ridgeSupport464_suffix_013, ridgeSupport464_rest_013) := by rfl
theorem ridgeSupport464_suffix_decode_012 : PackedRawNatGrowth.readList 15 3 ridgeSupport464_rest_012 =
    (ridgeSupport464_suffix_012, ridgeSupport464_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 15 3 0
    ridgeSupport464_rest_012 ridgeSupport464_rest_013 ridgeSupport464_rest_013
    ridgeSupport464_012 ridgeSupport464_suffix_013 ridgeSupport464_012_decode ridgeSupport464_suffix_decode_013
theorem ridgeSupport464_suffix_decode_011 : PackedRawNatGrowth.readList 15 35 ridgeSupport464_rest_011 =
    (ridgeSupport464_suffix_011, ridgeSupport464_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 15 32 3
    ridgeSupport464_rest_011 ridgeSupport464_rest_012 ridgeSupport464_rest_013
    ridgeSupport464_011 ridgeSupport464_suffix_012 ridgeSupport464_011_decode ridgeSupport464_suffix_decode_012
theorem ridgeSupport464_suffix_decode_010 : PackedRawNatGrowth.readList 15 67 ridgeSupport464_rest_010 =
    (ridgeSupport464_suffix_010, ridgeSupport464_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 15 32 35
    ridgeSupport464_rest_010 ridgeSupport464_rest_011 ridgeSupport464_rest_013
    ridgeSupport464_010 ridgeSupport464_suffix_011 ridgeSupport464_010_decode ridgeSupport464_suffix_decode_011
theorem ridgeSupport464_suffix_decode_009 : PackedRawNatGrowth.readList 15 99 ridgeSupport464_rest_009 =
    (ridgeSupport464_suffix_009, ridgeSupport464_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 15 32 67
    ridgeSupport464_rest_009 ridgeSupport464_rest_010 ridgeSupport464_rest_013
    ridgeSupport464_009 ridgeSupport464_suffix_010 ridgeSupport464_009_decode ridgeSupport464_suffix_decode_010
theorem ridgeSupport464_suffix_decode_008 : PackedRawNatGrowth.readList 15 131 ridgeSupport464_rest_008 =
    (ridgeSupport464_suffix_008, ridgeSupport464_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 15 32 99
    ridgeSupport464_rest_008 ridgeSupport464_rest_009 ridgeSupport464_rest_013
    ridgeSupport464_008 ridgeSupport464_suffix_009 ridgeSupport464_008_decode ridgeSupport464_suffix_decode_009
theorem ridgeSupport464_suffix_decode_007 : PackedRawNatGrowth.readList 15 163 ridgeSupport464_rest_007 =
    (ridgeSupport464_suffix_007, ridgeSupport464_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 15 32 131
    ridgeSupport464_rest_007 ridgeSupport464_rest_008 ridgeSupport464_rest_013
    ridgeSupport464_007 ridgeSupport464_suffix_008 ridgeSupport464_007_decode ridgeSupport464_suffix_decode_008
theorem ridgeSupport464_suffix_decode_006 : PackedRawNatGrowth.readList 15 195 ridgeSupport464_rest_006 =
    (ridgeSupport464_suffix_006, ridgeSupport464_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 15 32 163
    ridgeSupport464_rest_006 ridgeSupport464_rest_007 ridgeSupport464_rest_013
    ridgeSupport464_006 ridgeSupport464_suffix_007 ridgeSupport464_006_decode ridgeSupport464_suffix_decode_007
theorem ridgeSupport464_suffix_decode_005 : PackedRawNatGrowth.readList 15 227 ridgeSupport464_rest_005 =
    (ridgeSupport464_suffix_005, ridgeSupport464_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 15 32 195
    ridgeSupport464_rest_005 ridgeSupport464_rest_006 ridgeSupport464_rest_013
    ridgeSupport464_005 ridgeSupport464_suffix_006 ridgeSupport464_005_decode ridgeSupport464_suffix_decode_006
theorem ridgeSupport464_suffix_decode_004 : PackedRawNatGrowth.readList 15 259 ridgeSupport464_rest_004 =
    (ridgeSupport464_suffix_004, ridgeSupport464_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 15 32 227
    ridgeSupport464_rest_004 ridgeSupport464_rest_005 ridgeSupport464_rest_013
    ridgeSupport464_004 ridgeSupport464_suffix_005 ridgeSupport464_004_decode ridgeSupport464_suffix_decode_005
theorem ridgeSupport464_suffix_decode_003 : PackedRawNatGrowth.readList 15 291 ridgeSupport464_rest_003 =
    (ridgeSupport464_suffix_003, ridgeSupport464_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 15 32 259
    ridgeSupport464_rest_003 ridgeSupport464_rest_004 ridgeSupport464_rest_013
    ridgeSupport464_003 ridgeSupport464_suffix_004 ridgeSupport464_003_decode ridgeSupport464_suffix_decode_004
theorem ridgeSupport464_suffix_decode_002 : PackedRawNatGrowth.readList 15 323 ridgeSupport464_rest_002 =
    (ridgeSupport464_suffix_002, ridgeSupport464_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 15 32 291
    ridgeSupport464_rest_002 ridgeSupport464_rest_003 ridgeSupport464_rest_013
    ridgeSupport464_002 ridgeSupport464_suffix_003 ridgeSupport464_002_decode ridgeSupport464_suffix_decode_003
theorem ridgeSupport464_suffix_decode_001 : PackedRawNatGrowth.readList 15 355 ridgeSupport464_rest_001 =
    (ridgeSupport464_suffix_001, ridgeSupport464_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 15 32 323
    ridgeSupport464_rest_001 ridgeSupport464_rest_002 ridgeSupport464_rest_013
    ridgeSupport464_001 ridgeSupport464_suffix_002 ridgeSupport464_001_decode ridgeSupport464_suffix_decode_002
theorem ridgeSupport464_suffix_decode_000 : PackedRawNatGrowth.readList 15 387 ridgeSupport464_rest_000 =
    (ridgeSupport464_suffix_000, ridgeSupport464_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 15 32 355
    ridgeSupport464_rest_000 ridgeSupport464_rest_001 ridgeSupport464_rest_013
    ridgeSupport464_000 ridgeSupport464_suffix_001 ridgeSupport464_000_decode ridgeSupport464_suffix_decode_001
theorem ridgeSupport464_eq : candidateRows 464 = ridgeSupport464_suffix_000 := by
  rw [ridgeSupport464_source]
  exact congrArg Prod.fst ridgeSupport464_suffix_decode_000
theorem ridgeTest_large_464 : ridgeTest 464 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport464_eq]
    simp only [ridgeSupport464_suffix_000, ridgeSupport464_suffix_001, ridgeSupport464_suffix_002, ridgeSupport464_suffix_003, ridgeSupport464_suffix_004, ridgeSupport464_suffix_005, ridgeSupport464_suffix_006, ridgeSupport464_suffix_007, ridgeSupport464_suffix_008, ridgeSupport464_suffix_009, ridgeSupport464_suffix_010, ridgeSupport464_suffix_011, ridgeSupport464_suffix_012, ridgeSupport464_suffix_013, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport464_000_mask, ridgeSupport464_001_mask, ridgeSupport464_002_mask, ridgeSupport464_003_mask, ridgeSupport464_004_mask, ridgeSupport464_005_mask, ridgeSupport464_006_mask, ridgeSupport464_007_mask, ridgeSupport464_008_mask, ridgeSupport464_009_mask, ridgeSupport464_010_mask, ridgeSupport464_011_mask, ridgeSupport464_012_mask]
    decide +kernel
  · rw [ridgeSupport464_eq]
    simp only [ridgeSupport464_suffix_000, ridgeSupport464_suffix_001, ridgeSupport464_suffix_002, ridgeSupport464_suffix_003, ridgeSupport464_suffix_004, ridgeSupport464_suffix_005, ridgeSupport464_suffix_006, ridgeSupport464_suffix_007, ridgeSupport464_suffix_008, ridgeSupport464_suffix_009, ridgeSupport464_suffix_010, ridgeSupport464_suffix_011, ridgeSupport464_suffix_012, ridgeSupport464_suffix_013, List.all_append, List.all_nil, ridgeSupport464_000_checked, ridgeSupport464_001_checked, ridgeSupport464_002_checked, ridgeSupport464_003_checked, ridgeSupport464_004_checked, ridgeSupport464_005_checked, ridgeSupport464_006_checked, ridgeSupport464_007_checked, ridgeSupport464_008_checked, ridgeSupport464_009_checked, ridgeSupport464_010_checked, ridgeSupport464_011_checked, ridgeSupport464_012_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase00
