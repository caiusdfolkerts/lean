module
prelude
public import RootedSixBase00GrowthCacheRidgeSupport834Part000
public import RootedSixBase00GrowthCacheRidgeSupport834Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport834_suffix_decode_013 : PackedRawNatGrowth.readList 15 0 ridgeSupport834_rest_013 =
    (ridgeSupport834_suffix_013, ridgeSupport834_rest_013) := by rfl
theorem ridgeSupport834_suffix_decode_012 : PackedRawNatGrowth.readList 15 3 ridgeSupport834_rest_012 =
    (ridgeSupport834_suffix_012, ridgeSupport834_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 15 3 0
    ridgeSupport834_rest_012 ridgeSupport834_rest_013 ridgeSupport834_rest_013
    ridgeSupport834_012 ridgeSupport834_suffix_013 ridgeSupport834_012_decode ridgeSupport834_suffix_decode_013
theorem ridgeSupport834_suffix_decode_011 : PackedRawNatGrowth.readList 15 35 ridgeSupport834_rest_011 =
    (ridgeSupport834_suffix_011, ridgeSupport834_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 15 32 3
    ridgeSupport834_rest_011 ridgeSupport834_rest_012 ridgeSupport834_rest_013
    ridgeSupport834_011 ridgeSupport834_suffix_012 ridgeSupport834_011_decode ridgeSupport834_suffix_decode_012
theorem ridgeSupport834_suffix_decode_010 : PackedRawNatGrowth.readList 15 67 ridgeSupport834_rest_010 =
    (ridgeSupport834_suffix_010, ridgeSupport834_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 15 32 35
    ridgeSupport834_rest_010 ridgeSupport834_rest_011 ridgeSupport834_rest_013
    ridgeSupport834_010 ridgeSupport834_suffix_011 ridgeSupport834_010_decode ridgeSupport834_suffix_decode_011
theorem ridgeSupport834_suffix_decode_009 : PackedRawNatGrowth.readList 15 99 ridgeSupport834_rest_009 =
    (ridgeSupport834_suffix_009, ridgeSupport834_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 15 32 67
    ridgeSupport834_rest_009 ridgeSupport834_rest_010 ridgeSupport834_rest_013
    ridgeSupport834_009 ridgeSupport834_suffix_010 ridgeSupport834_009_decode ridgeSupport834_suffix_decode_010
theorem ridgeSupport834_suffix_decode_008 : PackedRawNatGrowth.readList 15 131 ridgeSupport834_rest_008 =
    (ridgeSupport834_suffix_008, ridgeSupport834_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 15 32 99
    ridgeSupport834_rest_008 ridgeSupport834_rest_009 ridgeSupport834_rest_013
    ridgeSupport834_008 ridgeSupport834_suffix_009 ridgeSupport834_008_decode ridgeSupport834_suffix_decode_009
theorem ridgeSupport834_suffix_decode_007 : PackedRawNatGrowth.readList 15 163 ridgeSupport834_rest_007 =
    (ridgeSupport834_suffix_007, ridgeSupport834_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 15 32 131
    ridgeSupport834_rest_007 ridgeSupport834_rest_008 ridgeSupport834_rest_013
    ridgeSupport834_007 ridgeSupport834_suffix_008 ridgeSupport834_007_decode ridgeSupport834_suffix_decode_008
theorem ridgeSupport834_suffix_decode_006 : PackedRawNatGrowth.readList 15 195 ridgeSupport834_rest_006 =
    (ridgeSupport834_suffix_006, ridgeSupport834_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 15 32 163
    ridgeSupport834_rest_006 ridgeSupport834_rest_007 ridgeSupport834_rest_013
    ridgeSupport834_006 ridgeSupport834_suffix_007 ridgeSupport834_006_decode ridgeSupport834_suffix_decode_007
theorem ridgeSupport834_suffix_decode_005 : PackedRawNatGrowth.readList 15 227 ridgeSupport834_rest_005 =
    (ridgeSupport834_suffix_005, ridgeSupport834_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 15 32 195
    ridgeSupport834_rest_005 ridgeSupport834_rest_006 ridgeSupport834_rest_013
    ridgeSupport834_005 ridgeSupport834_suffix_006 ridgeSupport834_005_decode ridgeSupport834_suffix_decode_006
theorem ridgeSupport834_suffix_decode_004 : PackedRawNatGrowth.readList 15 259 ridgeSupport834_rest_004 =
    (ridgeSupport834_suffix_004, ridgeSupport834_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 15 32 227
    ridgeSupport834_rest_004 ridgeSupport834_rest_005 ridgeSupport834_rest_013
    ridgeSupport834_004 ridgeSupport834_suffix_005 ridgeSupport834_004_decode ridgeSupport834_suffix_decode_005
theorem ridgeSupport834_suffix_decode_003 : PackedRawNatGrowth.readList 15 291 ridgeSupport834_rest_003 =
    (ridgeSupport834_suffix_003, ridgeSupport834_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 15 32 259
    ridgeSupport834_rest_003 ridgeSupport834_rest_004 ridgeSupport834_rest_013
    ridgeSupport834_003 ridgeSupport834_suffix_004 ridgeSupport834_003_decode ridgeSupport834_suffix_decode_004
theorem ridgeSupport834_suffix_decode_002 : PackedRawNatGrowth.readList 15 323 ridgeSupport834_rest_002 =
    (ridgeSupport834_suffix_002, ridgeSupport834_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 15 32 291
    ridgeSupport834_rest_002 ridgeSupport834_rest_003 ridgeSupport834_rest_013
    ridgeSupport834_002 ridgeSupport834_suffix_003 ridgeSupport834_002_decode ridgeSupport834_suffix_decode_003
theorem ridgeSupport834_suffix_decode_001 : PackedRawNatGrowth.readList 15 355 ridgeSupport834_rest_001 =
    (ridgeSupport834_suffix_001, ridgeSupport834_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 15 32 323
    ridgeSupport834_rest_001 ridgeSupport834_rest_002 ridgeSupport834_rest_013
    ridgeSupport834_001 ridgeSupport834_suffix_002 ridgeSupport834_001_decode ridgeSupport834_suffix_decode_002
theorem ridgeSupport834_suffix_decode_000 : PackedRawNatGrowth.readList 15 387 ridgeSupport834_rest_000 =
    (ridgeSupport834_suffix_000, ridgeSupport834_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 15 32 355
    ridgeSupport834_rest_000 ridgeSupport834_rest_001 ridgeSupport834_rest_013
    ridgeSupport834_000 ridgeSupport834_suffix_001 ridgeSupport834_000_decode ridgeSupport834_suffix_decode_001
theorem ridgeSupport834_eq : candidateRows 834 = ridgeSupport834_suffix_000 := by
  rw [ridgeSupport834_source]
  exact congrArg Prod.fst ridgeSupport834_suffix_decode_000
theorem ridgeTest_large_834 : ridgeTest 834 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport834_eq]
    simp only [ridgeSupport834_suffix_000, ridgeSupport834_suffix_001, ridgeSupport834_suffix_002, ridgeSupport834_suffix_003, ridgeSupport834_suffix_004, ridgeSupport834_suffix_005, ridgeSupport834_suffix_006, ridgeSupport834_suffix_007, ridgeSupport834_suffix_008, ridgeSupport834_suffix_009, ridgeSupport834_suffix_010, ridgeSupport834_suffix_011, ridgeSupport834_suffix_012, ridgeSupport834_suffix_013, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport834_000_mask, ridgeSupport834_001_mask, ridgeSupport834_002_mask, ridgeSupport834_003_mask, ridgeSupport834_004_mask, ridgeSupport834_005_mask, ridgeSupport834_006_mask, ridgeSupport834_007_mask, ridgeSupport834_008_mask, ridgeSupport834_009_mask, ridgeSupport834_010_mask, ridgeSupport834_011_mask, ridgeSupport834_012_mask]
    decide +kernel
  · rw [ridgeSupport834_eq]
    simp only [ridgeSupport834_suffix_000, ridgeSupport834_suffix_001, ridgeSupport834_suffix_002, ridgeSupport834_suffix_003, ridgeSupport834_suffix_004, ridgeSupport834_suffix_005, ridgeSupport834_suffix_006, ridgeSupport834_suffix_007, ridgeSupport834_suffix_008, ridgeSupport834_suffix_009, ridgeSupport834_suffix_010, ridgeSupport834_suffix_011, ridgeSupport834_suffix_012, ridgeSupport834_suffix_013, List.all_append, List.all_nil, ridgeSupport834_000_checked, ridgeSupport834_001_checked, ridgeSupport834_002_checked, ridgeSupport834_003_checked, ridgeSupport834_004_checked, ridgeSupport834_005_checked, ridgeSupport834_006_checked, ridgeSupport834_007_checked, ridgeSupport834_008_checked, ridgeSupport834_009_checked, ridgeSupport834_010_checked, ridgeSupport834_011_checked, ridgeSupport834_012_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase00
