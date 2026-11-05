module
prelude
public import RootedSixBase00GrowthCacheRidgeSupport706Part000
public import RootedSixBase00GrowthCacheRidgeSupport706Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport706_suffix_decode_013 : PackedRawNatGrowth.readList 15 0 ridgeSupport706_rest_013 =
    (ridgeSupport706_suffix_013, ridgeSupport706_rest_013) := by rfl
theorem ridgeSupport706_suffix_decode_012 : PackedRawNatGrowth.readList 15 3 ridgeSupport706_rest_012 =
    (ridgeSupport706_suffix_012, ridgeSupport706_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 15 3 0
    ridgeSupport706_rest_012 ridgeSupport706_rest_013 ridgeSupport706_rest_013
    ridgeSupport706_012 ridgeSupport706_suffix_013 ridgeSupport706_012_decode ridgeSupport706_suffix_decode_013
theorem ridgeSupport706_suffix_decode_011 : PackedRawNatGrowth.readList 15 35 ridgeSupport706_rest_011 =
    (ridgeSupport706_suffix_011, ridgeSupport706_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 15 32 3
    ridgeSupport706_rest_011 ridgeSupport706_rest_012 ridgeSupport706_rest_013
    ridgeSupport706_011 ridgeSupport706_suffix_012 ridgeSupport706_011_decode ridgeSupport706_suffix_decode_012
theorem ridgeSupport706_suffix_decode_010 : PackedRawNatGrowth.readList 15 67 ridgeSupport706_rest_010 =
    (ridgeSupport706_suffix_010, ridgeSupport706_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 15 32 35
    ridgeSupport706_rest_010 ridgeSupport706_rest_011 ridgeSupport706_rest_013
    ridgeSupport706_010 ridgeSupport706_suffix_011 ridgeSupport706_010_decode ridgeSupport706_suffix_decode_011
theorem ridgeSupport706_suffix_decode_009 : PackedRawNatGrowth.readList 15 99 ridgeSupport706_rest_009 =
    (ridgeSupport706_suffix_009, ridgeSupport706_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 15 32 67
    ridgeSupport706_rest_009 ridgeSupport706_rest_010 ridgeSupport706_rest_013
    ridgeSupport706_009 ridgeSupport706_suffix_010 ridgeSupport706_009_decode ridgeSupport706_suffix_decode_010
theorem ridgeSupport706_suffix_decode_008 : PackedRawNatGrowth.readList 15 131 ridgeSupport706_rest_008 =
    (ridgeSupport706_suffix_008, ridgeSupport706_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 15 32 99
    ridgeSupport706_rest_008 ridgeSupport706_rest_009 ridgeSupport706_rest_013
    ridgeSupport706_008 ridgeSupport706_suffix_009 ridgeSupport706_008_decode ridgeSupport706_suffix_decode_009
theorem ridgeSupport706_suffix_decode_007 : PackedRawNatGrowth.readList 15 163 ridgeSupport706_rest_007 =
    (ridgeSupport706_suffix_007, ridgeSupport706_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 15 32 131
    ridgeSupport706_rest_007 ridgeSupport706_rest_008 ridgeSupport706_rest_013
    ridgeSupport706_007 ridgeSupport706_suffix_008 ridgeSupport706_007_decode ridgeSupport706_suffix_decode_008
theorem ridgeSupport706_suffix_decode_006 : PackedRawNatGrowth.readList 15 195 ridgeSupport706_rest_006 =
    (ridgeSupport706_suffix_006, ridgeSupport706_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 15 32 163
    ridgeSupport706_rest_006 ridgeSupport706_rest_007 ridgeSupport706_rest_013
    ridgeSupport706_006 ridgeSupport706_suffix_007 ridgeSupport706_006_decode ridgeSupport706_suffix_decode_007
theorem ridgeSupport706_suffix_decode_005 : PackedRawNatGrowth.readList 15 227 ridgeSupport706_rest_005 =
    (ridgeSupport706_suffix_005, ridgeSupport706_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 15 32 195
    ridgeSupport706_rest_005 ridgeSupport706_rest_006 ridgeSupport706_rest_013
    ridgeSupport706_005 ridgeSupport706_suffix_006 ridgeSupport706_005_decode ridgeSupport706_suffix_decode_006
theorem ridgeSupport706_suffix_decode_004 : PackedRawNatGrowth.readList 15 259 ridgeSupport706_rest_004 =
    (ridgeSupport706_suffix_004, ridgeSupport706_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 15 32 227
    ridgeSupport706_rest_004 ridgeSupport706_rest_005 ridgeSupport706_rest_013
    ridgeSupport706_004 ridgeSupport706_suffix_005 ridgeSupport706_004_decode ridgeSupport706_suffix_decode_005
theorem ridgeSupport706_suffix_decode_003 : PackedRawNatGrowth.readList 15 291 ridgeSupport706_rest_003 =
    (ridgeSupport706_suffix_003, ridgeSupport706_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 15 32 259
    ridgeSupport706_rest_003 ridgeSupport706_rest_004 ridgeSupport706_rest_013
    ridgeSupport706_003 ridgeSupport706_suffix_004 ridgeSupport706_003_decode ridgeSupport706_suffix_decode_004
theorem ridgeSupport706_suffix_decode_002 : PackedRawNatGrowth.readList 15 323 ridgeSupport706_rest_002 =
    (ridgeSupport706_suffix_002, ridgeSupport706_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 15 32 291
    ridgeSupport706_rest_002 ridgeSupport706_rest_003 ridgeSupport706_rest_013
    ridgeSupport706_002 ridgeSupport706_suffix_003 ridgeSupport706_002_decode ridgeSupport706_suffix_decode_003
theorem ridgeSupport706_suffix_decode_001 : PackedRawNatGrowth.readList 15 355 ridgeSupport706_rest_001 =
    (ridgeSupport706_suffix_001, ridgeSupport706_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 15 32 323
    ridgeSupport706_rest_001 ridgeSupport706_rest_002 ridgeSupport706_rest_013
    ridgeSupport706_001 ridgeSupport706_suffix_002 ridgeSupport706_001_decode ridgeSupport706_suffix_decode_002
theorem ridgeSupport706_suffix_decode_000 : PackedRawNatGrowth.readList 15 387 ridgeSupport706_rest_000 =
    (ridgeSupport706_suffix_000, ridgeSupport706_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 15 32 355
    ridgeSupport706_rest_000 ridgeSupport706_rest_001 ridgeSupport706_rest_013
    ridgeSupport706_000 ridgeSupport706_suffix_001 ridgeSupport706_000_decode ridgeSupport706_suffix_decode_001
theorem ridgeSupport706_eq : candidateRows 706 = ridgeSupport706_suffix_000 := by
  rw [ridgeSupport706_source]
  exact congrArg Prod.fst ridgeSupport706_suffix_decode_000
theorem ridgeTest_large_706 : ridgeTest 706 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport706_eq]
    simp only [ridgeSupport706_suffix_000, ridgeSupport706_suffix_001, ridgeSupport706_suffix_002, ridgeSupport706_suffix_003, ridgeSupport706_suffix_004, ridgeSupport706_suffix_005, ridgeSupport706_suffix_006, ridgeSupport706_suffix_007, ridgeSupport706_suffix_008, ridgeSupport706_suffix_009, ridgeSupport706_suffix_010, ridgeSupport706_suffix_011, ridgeSupport706_suffix_012, ridgeSupport706_suffix_013, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport706_000_mask, ridgeSupport706_001_mask, ridgeSupport706_002_mask, ridgeSupport706_003_mask, ridgeSupport706_004_mask, ridgeSupport706_005_mask, ridgeSupport706_006_mask, ridgeSupport706_007_mask, ridgeSupport706_008_mask, ridgeSupport706_009_mask, ridgeSupport706_010_mask, ridgeSupport706_011_mask, ridgeSupport706_012_mask]
    decide +kernel
  · rw [ridgeSupport706_eq]
    simp only [ridgeSupport706_suffix_000, ridgeSupport706_suffix_001, ridgeSupport706_suffix_002, ridgeSupport706_suffix_003, ridgeSupport706_suffix_004, ridgeSupport706_suffix_005, ridgeSupport706_suffix_006, ridgeSupport706_suffix_007, ridgeSupport706_suffix_008, ridgeSupport706_suffix_009, ridgeSupport706_suffix_010, ridgeSupport706_suffix_011, ridgeSupport706_suffix_012, ridgeSupport706_suffix_013, List.all_append, List.all_nil, ridgeSupport706_000_checked, ridgeSupport706_001_checked, ridgeSupport706_002_checked, ridgeSupport706_003_checked, ridgeSupport706_004_checked, ridgeSupport706_005_checked, ridgeSupport706_006_checked, ridgeSupport706_007_checked, ridgeSupport706_008_checked, ridgeSupport706_009_checked, ridgeSupport706_010_checked, ridgeSupport706_011_checked, ridgeSupport706_012_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase00
