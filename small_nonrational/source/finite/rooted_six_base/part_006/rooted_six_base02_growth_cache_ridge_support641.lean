module
prelude
public import RootedSixBase02GrowthCacheRidgeSupport641Part000
public import RootedSixBase02GrowthCacheRidgeSupport641Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase02
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport641_suffix_decode_013 : PackedRawNatGrowth.readList 13 0 ridgeSupport641_rest_013 =
    (ridgeSupport641_suffix_013, ridgeSupport641_rest_013) := by rfl
theorem ridgeSupport641_suffix_decode_012 : PackedRawNatGrowth.readList 13 15 ridgeSupport641_rest_012 =
    (ridgeSupport641_suffix_012, ridgeSupport641_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 13 15 0
    ridgeSupport641_rest_012 ridgeSupport641_rest_013 ridgeSupport641_rest_013
    ridgeSupport641_012 ridgeSupport641_suffix_013 ridgeSupport641_012_decode ridgeSupport641_suffix_decode_013
theorem ridgeSupport641_suffix_decode_011 : PackedRawNatGrowth.readList 13 47 ridgeSupport641_rest_011 =
    (ridgeSupport641_suffix_011, ridgeSupport641_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 15
    ridgeSupport641_rest_011 ridgeSupport641_rest_012 ridgeSupport641_rest_013
    ridgeSupport641_011 ridgeSupport641_suffix_012 ridgeSupport641_011_decode ridgeSupport641_suffix_decode_012
theorem ridgeSupport641_suffix_decode_010 : PackedRawNatGrowth.readList 13 79 ridgeSupport641_rest_010 =
    (ridgeSupport641_suffix_010, ridgeSupport641_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 47
    ridgeSupport641_rest_010 ridgeSupport641_rest_011 ridgeSupport641_rest_013
    ridgeSupport641_010 ridgeSupport641_suffix_011 ridgeSupport641_010_decode ridgeSupport641_suffix_decode_011
theorem ridgeSupport641_suffix_decode_009 : PackedRawNatGrowth.readList 13 111 ridgeSupport641_rest_009 =
    (ridgeSupport641_suffix_009, ridgeSupport641_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 79
    ridgeSupport641_rest_009 ridgeSupport641_rest_010 ridgeSupport641_rest_013
    ridgeSupport641_009 ridgeSupport641_suffix_010 ridgeSupport641_009_decode ridgeSupport641_suffix_decode_010
theorem ridgeSupport641_suffix_decode_008 : PackedRawNatGrowth.readList 13 143 ridgeSupport641_rest_008 =
    (ridgeSupport641_suffix_008, ridgeSupport641_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 111
    ridgeSupport641_rest_008 ridgeSupport641_rest_009 ridgeSupport641_rest_013
    ridgeSupport641_008 ridgeSupport641_suffix_009 ridgeSupport641_008_decode ridgeSupport641_suffix_decode_009
theorem ridgeSupport641_suffix_decode_007 : PackedRawNatGrowth.readList 13 175 ridgeSupport641_rest_007 =
    (ridgeSupport641_suffix_007, ridgeSupport641_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 143
    ridgeSupport641_rest_007 ridgeSupport641_rest_008 ridgeSupport641_rest_013
    ridgeSupport641_007 ridgeSupport641_suffix_008 ridgeSupport641_007_decode ridgeSupport641_suffix_decode_008
theorem ridgeSupport641_suffix_decode_006 : PackedRawNatGrowth.readList 13 207 ridgeSupport641_rest_006 =
    (ridgeSupport641_suffix_006, ridgeSupport641_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 175
    ridgeSupport641_rest_006 ridgeSupport641_rest_007 ridgeSupport641_rest_013
    ridgeSupport641_006 ridgeSupport641_suffix_007 ridgeSupport641_006_decode ridgeSupport641_suffix_decode_007
theorem ridgeSupport641_suffix_decode_005 : PackedRawNatGrowth.readList 13 239 ridgeSupport641_rest_005 =
    (ridgeSupport641_suffix_005, ridgeSupport641_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 207
    ridgeSupport641_rest_005 ridgeSupport641_rest_006 ridgeSupport641_rest_013
    ridgeSupport641_005 ridgeSupport641_suffix_006 ridgeSupport641_005_decode ridgeSupport641_suffix_decode_006
theorem ridgeSupport641_suffix_decode_004 : PackedRawNatGrowth.readList 13 271 ridgeSupport641_rest_004 =
    (ridgeSupport641_suffix_004, ridgeSupport641_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 239
    ridgeSupport641_rest_004 ridgeSupport641_rest_005 ridgeSupport641_rest_013
    ridgeSupport641_004 ridgeSupport641_suffix_005 ridgeSupport641_004_decode ridgeSupport641_suffix_decode_005
theorem ridgeSupport641_suffix_decode_003 : PackedRawNatGrowth.readList 13 303 ridgeSupport641_rest_003 =
    (ridgeSupport641_suffix_003, ridgeSupport641_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 271
    ridgeSupport641_rest_003 ridgeSupport641_rest_004 ridgeSupport641_rest_013
    ridgeSupport641_003 ridgeSupport641_suffix_004 ridgeSupport641_003_decode ridgeSupport641_suffix_decode_004
theorem ridgeSupport641_suffix_decode_002 : PackedRawNatGrowth.readList 13 335 ridgeSupport641_rest_002 =
    (ridgeSupport641_suffix_002, ridgeSupport641_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 303
    ridgeSupport641_rest_002 ridgeSupport641_rest_003 ridgeSupport641_rest_013
    ridgeSupport641_002 ridgeSupport641_suffix_003 ridgeSupport641_002_decode ridgeSupport641_suffix_decode_003
theorem ridgeSupport641_suffix_decode_001 : PackedRawNatGrowth.readList 13 367 ridgeSupport641_rest_001 =
    (ridgeSupport641_suffix_001, ridgeSupport641_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 335
    ridgeSupport641_rest_001 ridgeSupport641_rest_002 ridgeSupport641_rest_013
    ridgeSupport641_001 ridgeSupport641_suffix_002 ridgeSupport641_001_decode ridgeSupport641_suffix_decode_002
theorem ridgeSupport641_suffix_decode_000 : PackedRawNatGrowth.readList 13 399 ridgeSupport641_rest_000 =
    (ridgeSupport641_suffix_000, ridgeSupport641_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 367
    ridgeSupport641_rest_000 ridgeSupport641_rest_001 ridgeSupport641_rest_013
    ridgeSupport641_000 ridgeSupport641_suffix_001 ridgeSupport641_000_decode ridgeSupport641_suffix_decode_001
theorem ridgeSupport641_eq : candidateRows 641 = ridgeSupport641_suffix_000 := by
  change candidateSupports 641 = ridgeSupport641_suffix_000
  rw [ridgeSupport641_source]
  exact congrArg Prod.fst ridgeSupport641_suffix_decode_000
theorem ridgeTest_large_641 : ridgeTest 641 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport641_eq]
    simp only [ridgeSupport641_suffix_000, ridgeSupport641_suffix_001, ridgeSupport641_suffix_002, ridgeSupport641_suffix_003, ridgeSupport641_suffix_004, ridgeSupport641_suffix_005, ridgeSupport641_suffix_006, ridgeSupport641_suffix_007, ridgeSupport641_suffix_008, ridgeSupport641_suffix_009, ridgeSupport641_suffix_010, ridgeSupport641_suffix_011, ridgeSupport641_suffix_012, ridgeSupport641_suffix_013, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport641_000_mask, ridgeSupport641_001_mask, ridgeSupport641_002_mask, ridgeSupport641_003_mask, ridgeSupport641_004_mask, ridgeSupport641_005_mask, ridgeSupport641_006_mask, ridgeSupport641_007_mask, ridgeSupport641_008_mask, ridgeSupport641_009_mask, ridgeSupport641_010_mask, ridgeSupport641_011_mask, ridgeSupport641_012_mask]
    decide +kernel
  · rw [ridgeSupport641_eq]
    simp only [ridgeSupport641_suffix_000, ridgeSupport641_suffix_001, ridgeSupport641_suffix_002, ridgeSupport641_suffix_003, ridgeSupport641_suffix_004, ridgeSupport641_suffix_005, ridgeSupport641_suffix_006, ridgeSupport641_suffix_007, ridgeSupport641_suffix_008, ridgeSupport641_suffix_009, ridgeSupport641_suffix_010, ridgeSupport641_suffix_011, ridgeSupport641_suffix_012, ridgeSupport641_suffix_013, List.all_append, List.all_nil, ridgeSupport641_000_checked, ridgeSupport641_001_checked, ridgeSupport641_002_checked, ridgeSupport641_003_checked, ridgeSupport641_004_checked, ridgeSupport641_005_checked, ridgeSupport641_006_checked, ridgeSupport641_007_checked, ridgeSupport641_008_checked, ridgeSupport641_009_checked, ridgeSupport641_010_checked, ridgeSupport641_011_checked, ridgeSupport641_012_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase02
