module
prelude
public import RootedSixBase00GrowthCacheRidgeSupport912Part000
public import RootedSixBase00GrowthCacheRidgeSupport912Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport912_suffix_decode_013 : PackedRawNatGrowth.readList 15 0 ridgeSupport912_rest_013 =
    (ridgeSupport912_suffix_013, ridgeSupport912_rest_013) := by rfl
theorem ridgeSupport912_suffix_decode_012 : PackedRawNatGrowth.readList 15 3 ridgeSupport912_rest_012 =
    (ridgeSupport912_suffix_012, ridgeSupport912_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 15 3 0
    ridgeSupport912_rest_012 ridgeSupport912_rest_013 ridgeSupport912_rest_013
    ridgeSupport912_012 ridgeSupport912_suffix_013 ridgeSupport912_012_decode ridgeSupport912_suffix_decode_013
theorem ridgeSupport912_suffix_decode_011 : PackedRawNatGrowth.readList 15 35 ridgeSupport912_rest_011 =
    (ridgeSupport912_suffix_011, ridgeSupport912_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 15 32 3
    ridgeSupport912_rest_011 ridgeSupport912_rest_012 ridgeSupport912_rest_013
    ridgeSupport912_011 ridgeSupport912_suffix_012 ridgeSupport912_011_decode ridgeSupport912_suffix_decode_012
theorem ridgeSupport912_suffix_decode_010 : PackedRawNatGrowth.readList 15 67 ridgeSupport912_rest_010 =
    (ridgeSupport912_suffix_010, ridgeSupport912_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 15 32 35
    ridgeSupport912_rest_010 ridgeSupport912_rest_011 ridgeSupport912_rest_013
    ridgeSupport912_010 ridgeSupport912_suffix_011 ridgeSupport912_010_decode ridgeSupport912_suffix_decode_011
theorem ridgeSupport912_suffix_decode_009 : PackedRawNatGrowth.readList 15 99 ridgeSupport912_rest_009 =
    (ridgeSupport912_suffix_009, ridgeSupport912_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 15 32 67
    ridgeSupport912_rest_009 ridgeSupport912_rest_010 ridgeSupport912_rest_013
    ridgeSupport912_009 ridgeSupport912_suffix_010 ridgeSupport912_009_decode ridgeSupport912_suffix_decode_010
theorem ridgeSupport912_suffix_decode_008 : PackedRawNatGrowth.readList 15 131 ridgeSupport912_rest_008 =
    (ridgeSupport912_suffix_008, ridgeSupport912_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 15 32 99
    ridgeSupport912_rest_008 ridgeSupport912_rest_009 ridgeSupport912_rest_013
    ridgeSupport912_008 ridgeSupport912_suffix_009 ridgeSupport912_008_decode ridgeSupport912_suffix_decode_009
theorem ridgeSupport912_suffix_decode_007 : PackedRawNatGrowth.readList 15 163 ridgeSupport912_rest_007 =
    (ridgeSupport912_suffix_007, ridgeSupport912_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 15 32 131
    ridgeSupport912_rest_007 ridgeSupport912_rest_008 ridgeSupport912_rest_013
    ridgeSupport912_007 ridgeSupport912_suffix_008 ridgeSupport912_007_decode ridgeSupport912_suffix_decode_008
theorem ridgeSupport912_suffix_decode_006 : PackedRawNatGrowth.readList 15 195 ridgeSupport912_rest_006 =
    (ridgeSupport912_suffix_006, ridgeSupport912_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 15 32 163
    ridgeSupport912_rest_006 ridgeSupport912_rest_007 ridgeSupport912_rest_013
    ridgeSupport912_006 ridgeSupport912_suffix_007 ridgeSupport912_006_decode ridgeSupport912_suffix_decode_007
theorem ridgeSupport912_suffix_decode_005 : PackedRawNatGrowth.readList 15 227 ridgeSupport912_rest_005 =
    (ridgeSupport912_suffix_005, ridgeSupport912_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 15 32 195
    ridgeSupport912_rest_005 ridgeSupport912_rest_006 ridgeSupport912_rest_013
    ridgeSupport912_005 ridgeSupport912_suffix_006 ridgeSupport912_005_decode ridgeSupport912_suffix_decode_006
theorem ridgeSupport912_suffix_decode_004 : PackedRawNatGrowth.readList 15 259 ridgeSupport912_rest_004 =
    (ridgeSupport912_suffix_004, ridgeSupport912_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 15 32 227
    ridgeSupport912_rest_004 ridgeSupport912_rest_005 ridgeSupport912_rest_013
    ridgeSupport912_004 ridgeSupport912_suffix_005 ridgeSupport912_004_decode ridgeSupport912_suffix_decode_005
theorem ridgeSupport912_suffix_decode_003 : PackedRawNatGrowth.readList 15 291 ridgeSupport912_rest_003 =
    (ridgeSupport912_suffix_003, ridgeSupport912_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 15 32 259
    ridgeSupport912_rest_003 ridgeSupport912_rest_004 ridgeSupport912_rest_013
    ridgeSupport912_003 ridgeSupport912_suffix_004 ridgeSupport912_003_decode ridgeSupport912_suffix_decode_004
theorem ridgeSupport912_suffix_decode_002 : PackedRawNatGrowth.readList 15 323 ridgeSupport912_rest_002 =
    (ridgeSupport912_suffix_002, ridgeSupport912_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 15 32 291
    ridgeSupport912_rest_002 ridgeSupport912_rest_003 ridgeSupport912_rest_013
    ridgeSupport912_002 ridgeSupport912_suffix_003 ridgeSupport912_002_decode ridgeSupport912_suffix_decode_003
theorem ridgeSupport912_suffix_decode_001 : PackedRawNatGrowth.readList 15 355 ridgeSupport912_rest_001 =
    (ridgeSupport912_suffix_001, ridgeSupport912_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 15 32 323
    ridgeSupport912_rest_001 ridgeSupport912_rest_002 ridgeSupport912_rest_013
    ridgeSupport912_001 ridgeSupport912_suffix_002 ridgeSupport912_001_decode ridgeSupport912_suffix_decode_002
theorem ridgeSupport912_suffix_decode_000 : PackedRawNatGrowth.readList 15 387 ridgeSupport912_rest_000 =
    (ridgeSupport912_suffix_000, ridgeSupport912_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 15 32 355
    ridgeSupport912_rest_000 ridgeSupport912_rest_001 ridgeSupport912_rest_013
    ridgeSupport912_000 ridgeSupport912_suffix_001 ridgeSupport912_000_decode ridgeSupport912_suffix_decode_001
theorem ridgeSupport912_eq : candidateRows 912 = ridgeSupport912_suffix_000 := by
  rw [ridgeSupport912_source]
  exact congrArg Prod.fst ridgeSupport912_suffix_decode_000
theorem ridgeTest_large_912 : ridgeTest 912 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport912_eq]
    simp only [ridgeSupport912_suffix_000, ridgeSupport912_suffix_001, ridgeSupport912_suffix_002, ridgeSupport912_suffix_003, ridgeSupport912_suffix_004, ridgeSupport912_suffix_005, ridgeSupport912_suffix_006, ridgeSupport912_suffix_007, ridgeSupport912_suffix_008, ridgeSupport912_suffix_009, ridgeSupport912_suffix_010, ridgeSupport912_suffix_011, ridgeSupport912_suffix_012, ridgeSupport912_suffix_013, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport912_000_mask, ridgeSupport912_001_mask, ridgeSupport912_002_mask, ridgeSupport912_003_mask, ridgeSupport912_004_mask, ridgeSupport912_005_mask, ridgeSupport912_006_mask, ridgeSupport912_007_mask, ridgeSupport912_008_mask, ridgeSupport912_009_mask, ridgeSupport912_010_mask, ridgeSupport912_011_mask, ridgeSupport912_012_mask]
    decide +kernel
  · rw [ridgeSupport912_eq]
    simp only [ridgeSupport912_suffix_000, ridgeSupport912_suffix_001, ridgeSupport912_suffix_002, ridgeSupport912_suffix_003, ridgeSupport912_suffix_004, ridgeSupport912_suffix_005, ridgeSupport912_suffix_006, ridgeSupport912_suffix_007, ridgeSupport912_suffix_008, ridgeSupport912_suffix_009, ridgeSupport912_suffix_010, ridgeSupport912_suffix_011, ridgeSupport912_suffix_012, ridgeSupport912_suffix_013, List.all_append, List.all_nil, ridgeSupport912_000_checked, ridgeSupport912_001_checked, ridgeSupport912_002_checked, ridgeSupport912_003_checked, ridgeSupport912_004_checked, ridgeSupport912_005_checked, ridgeSupport912_006_checked, ridgeSupport912_007_checked, ridgeSupport912_008_checked, ridgeSupport912_009_checked, ridgeSupport912_010_checked, ridgeSupport912_011_checked, ridgeSupport912_012_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase00
