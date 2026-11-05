module
prelude
public import RootedSixBase00GrowthCacheRidgeSupport898Part000
public import RootedSixBase00GrowthCacheRidgeSupport898Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport898_suffix_decode_013 : PackedRawNatGrowth.readList 15 0 ridgeSupport898_rest_013 =
    (ridgeSupport898_suffix_013, ridgeSupport898_rest_013) := by rfl
theorem ridgeSupport898_suffix_decode_012 : PackedRawNatGrowth.readList 15 3 ridgeSupport898_rest_012 =
    (ridgeSupport898_suffix_012, ridgeSupport898_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 15 3 0
    ridgeSupport898_rest_012 ridgeSupport898_rest_013 ridgeSupport898_rest_013
    ridgeSupport898_012 ridgeSupport898_suffix_013 ridgeSupport898_012_decode ridgeSupport898_suffix_decode_013
theorem ridgeSupport898_suffix_decode_011 : PackedRawNatGrowth.readList 15 35 ridgeSupport898_rest_011 =
    (ridgeSupport898_suffix_011, ridgeSupport898_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 15 32 3
    ridgeSupport898_rest_011 ridgeSupport898_rest_012 ridgeSupport898_rest_013
    ridgeSupport898_011 ridgeSupport898_suffix_012 ridgeSupport898_011_decode ridgeSupport898_suffix_decode_012
theorem ridgeSupport898_suffix_decode_010 : PackedRawNatGrowth.readList 15 67 ridgeSupport898_rest_010 =
    (ridgeSupport898_suffix_010, ridgeSupport898_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 15 32 35
    ridgeSupport898_rest_010 ridgeSupport898_rest_011 ridgeSupport898_rest_013
    ridgeSupport898_010 ridgeSupport898_suffix_011 ridgeSupport898_010_decode ridgeSupport898_suffix_decode_011
theorem ridgeSupport898_suffix_decode_009 : PackedRawNatGrowth.readList 15 99 ridgeSupport898_rest_009 =
    (ridgeSupport898_suffix_009, ridgeSupport898_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 15 32 67
    ridgeSupport898_rest_009 ridgeSupport898_rest_010 ridgeSupport898_rest_013
    ridgeSupport898_009 ridgeSupport898_suffix_010 ridgeSupport898_009_decode ridgeSupport898_suffix_decode_010
theorem ridgeSupport898_suffix_decode_008 : PackedRawNatGrowth.readList 15 131 ridgeSupport898_rest_008 =
    (ridgeSupport898_suffix_008, ridgeSupport898_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 15 32 99
    ridgeSupport898_rest_008 ridgeSupport898_rest_009 ridgeSupport898_rest_013
    ridgeSupport898_008 ridgeSupport898_suffix_009 ridgeSupport898_008_decode ridgeSupport898_suffix_decode_009
theorem ridgeSupport898_suffix_decode_007 : PackedRawNatGrowth.readList 15 163 ridgeSupport898_rest_007 =
    (ridgeSupport898_suffix_007, ridgeSupport898_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 15 32 131
    ridgeSupport898_rest_007 ridgeSupport898_rest_008 ridgeSupport898_rest_013
    ridgeSupport898_007 ridgeSupport898_suffix_008 ridgeSupport898_007_decode ridgeSupport898_suffix_decode_008
theorem ridgeSupport898_suffix_decode_006 : PackedRawNatGrowth.readList 15 195 ridgeSupport898_rest_006 =
    (ridgeSupport898_suffix_006, ridgeSupport898_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 15 32 163
    ridgeSupport898_rest_006 ridgeSupport898_rest_007 ridgeSupport898_rest_013
    ridgeSupport898_006 ridgeSupport898_suffix_007 ridgeSupport898_006_decode ridgeSupport898_suffix_decode_007
theorem ridgeSupport898_suffix_decode_005 : PackedRawNatGrowth.readList 15 227 ridgeSupport898_rest_005 =
    (ridgeSupport898_suffix_005, ridgeSupport898_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 15 32 195
    ridgeSupport898_rest_005 ridgeSupport898_rest_006 ridgeSupport898_rest_013
    ridgeSupport898_005 ridgeSupport898_suffix_006 ridgeSupport898_005_decode ridgeSupport898_suffix_decode_006
theorem ridgeSupport898_suffix_decode_004 : PackedRawNatGrowth.readList 15 259 ridgeSupport898_rest_004 =
    (ridgeSupport898_suffix_004, ridgeSupport898_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 15 32 227
    ridgeSupport898_rest_004 ridgeSupport898_rest_005 ridgeSupport898_rest_013
    ridgeSupport898_004 ridgeSupport898_suffix_005 ridgeSupport898_004_decode ridgeSupport898_suffix_decode_005
theorem ridgeSupport898_suffix_decode_003 : PackedRawNatGrowth.readList 15 291 ridgeSupport898_rest_003 =
    (ridgeSupport898_suffix_003, ridgeSupport898_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 15 32 259
    ridgeSupport898_rest_003 ridgeSupport898_rest_004 ridgeSupport898_rest_013
    ridgeSupport898_003 ridgeSupport898_suffix_004 ridgeSupport898_003_decode ridgeSupport898_suffix_decode_004
theorem ridgeSupport898_suffix_decode_002 : PackedRawNatGrowth.readList 15 323 ridgeSupport898_rest_002 =
    (ridgeSupport898_suffix_002, ridgeSupport898_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 15 32 291
    ridgeSupport898_rest_002 ridgeSupport898_rest_003 ridgeSupport898_rest_013
    ridgeSupport898_002 ridgeSupport898_suffix_003 ridgeSupport898_002_decode ridgeSupport898_suffix_decode_003
theorem ridgeSupport898_suffix_decode_001 : PackedRawNatGrowth.readList 15 355 ridgeSupport898_rest_001 =
    (ridgeSupport898_suffix_001, ridgeSupport898_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 15 32 323
    ridgeSupport898_rest_001 ridgeSupport898_rest_002 ridgeSupport898_rest_013
    ridgeSupport898_001 ridgeSupport898_suffix_002 ridgeSupport898_001_decode ridgeSupport898_suffix_decode_002
theorem ridgeSupport898_suffix_decode_000 : PackedRawNatGrowth.readList 15 387 ridgeSupport898_rest_000 =
    (ridgeSupport898_suffix_000, ridgeSupport898_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 15 32 355
    ridgeSupport898_rest_000 ridgeSupport898_rest_001 ridgeSupport898_rest_013
    ridgeSupport898_000 ridgeSupport898_suffix_001 ridgeSupport898_000_decode ridgeSupport898_suffix_decode_001
theorem ridgeSupport898_eq : candidateRows 898 = ridgeSupport898_suffix_000 := by
  rw [ridgeSupport898_source]
  exact congrArg Prod.fst ridgeSupport898_suffix_decode_000
theorem ridgeTest_large_898 : ridgeTest 898 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport898_eq]
    simp only [ridgeSupport898_suffix_000, ridgeSupport898_suffix_001, ridgeSupport898_suffix_002, ridgeSupport898_suffix_003, ridgeSupport898_suffix_004, ridgeSupport898_suffix_005, ridgeSupport898_suffix_006, ridgeSupport898_suffix_007, ridgeSupport898_suffix_008, ridgeSupport898_suffix_009, ridgeSupport898_suffix_010, ridgeSupport898_suffix_011, ridgeSupport898_suffix_012, ridgeSupport898_suffix_013, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport898_000_mask, ridgeSupport898_001_mask, ridgeSupport898_002_mask, ridgeSupport898_003_mask, ridgeSupport898_004_mask, ridgeSupport898_005_mask, ridgeSupport898_006_mask, ridgeSupport898_007_mask, ridgeSupport898_008_mask, ridgeSupport898_009_mask, ridgeSupport898_010_mask, ridgeSupport898_011_mask, ridgeSupport898_012_mask]
    decide +kernel
  · rw [ridgeSupport898_eq]
    simp only [ridgeSupport898_suffix_000, ridgeSupport898_suffix_001, ridgeSupport898_suffix_002, ridgeSupport898_suffix_003, ridgeSupport898_suffix_004, ridgeSupport898_suffix_005, ridgeSupport898_suffix_006, ridgeSupport898_suffix_007, ridgeSupport898_suffix_008, ridgeSupport898_suffix_009, ridgeSupport898_suffix_010, ridgeSupport898_suffix_011, ridgeSupport898_suffix_012, ridgeSupport898_suffix_013, List.all_append, List.all_nil, ridgeSupport898_000_checked, ridgeSupport898_001_checked, ridgeSupport898_002_checked, ridgeSupport898_003_checked, ridgeSupport898_004_checked, ridgeSupport898_005_checked, ridgeSupport898_006_checked, ridgeSupport898_007_checked, ridgeSupport898_008_checked, ridgeSupport898_009_checked, ridgeSupport898_010_checked, ridgeSupport898_011_checked, ridgeSupport898_012_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase00
