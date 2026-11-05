module
prelude
public import RootedSixBase02GrowthCacheRidgeSupport385Part000
public import RootedSixBase02GrowthCacheRidgeSupport385Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase02
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport385_suffix_decode_013 : PackedRawNatGrowth.readList 13 0 ridgeSupport385_rest_013 =
    (ridgeSupport385_suffix_013, ridgeSupport385_rest_013) := by rfl
theorem ridgeSupport385_suffix_decode_012 : PackedRawNatGrowth.readList 13 15 ridgeSupport385_rest_012 =
    (ridgeSupport385_suffix_012, ridgeSupport385_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 13 15 0
    ridgeSupport385_rest_012 ridgeSupport385_rest_013 ridgeSupport385_rest_013
    ridgeSupport385_012 ridgeSupport385_suffix_013 ridgeSupport385_012_decode ridgeSupport385_suffix_decode_013
theorem ridgeSupport385_suffix_decode_011 : PackedRawNatGrowth.readList 13 47 ridgeSupport385_rest_011 =
    (ridgeSupport385_suffix_011, ridgeSupport385_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 15
    ridgeSupport385_rest_011 ridgeSupport385_rest_012 ridgeSupport385_rest_013
    ridgeSupport385_011 ridgeSupport385_suffix_012 ridgeSupport385_011_decode ridgeSupport385_suffix_decode_012
theorem ridgeSupport385_suffix_decode_010 : PackedRawNatGrowth.readList 13 79 ridgeSupport385_rest_010 =
    (ridgeSupport385_suffix_010, ridgeSupport385_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 47
    ridgeSupport385_rest_010 ridgeSupport385_rest_011 ridgeSupport385_rest_013
    ridgeSupport385_010 ridgeSupport385_suffix_011 ridgeSupport385_010_decode ridgeSupport385_suffix_decode_011
theorem ridgeSupport385_suffix_decode_009 : PackedRawNatGrowth.readList 13 111 ridgeSupport385_rest_009 =
    (ridgeSupport385_suffix_009, ridgeSupport385_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 79
    ridgeSupport385_rest_009 ridgeSupport385_rest_010 ridgeSupport385_rest_013
    ridgeSupport385_009 ridgeSupport385_suffix_010 ridgeSupport385_009_decode ridgeSupport385_suffix_decode_010
theorem ridgeSupport385_suffix_decode_008 : PackedRawNatGrowth.readList 13 143 ridgeSupport385_rest_008 =
    (ridgeSupport385_suffix_008, ridgeSupport385_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 111
    ridgeSupport385_rest_008 ridgeSupport385_rest_009 ridgeSupport385_rest_013
    ridgeSupport385_008 ridgeSupport385_suffix_009 ridgeSupport385_008_decode ridgeSupport385_suffix_decode_009
theorem ridgeSupport385_suffix_decode_007 : PackedRawNatGrowth.readList 13 175 ridgeSupport385_rest_007 =
    (ridgeSupport385_suffix_007, ridgeSupport385_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 143
    ridgeSupport385_rest_007 ridgeSupport385_rest_008 ridgeSupport385_rest_013
    ridgeSupport385_007 ridgeSupport385_suffix_008 ridgeSupport385_007_decode ridgeSupport385_suffix_decode_008
theorem ridgeSupport385_suffix_decode_006 : PackedRawNatGrowth.readList 13 207 ridgeSupport385_rest_006 =
    (ridgeSupport385_suffix_006, ridgeSupport385_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 175
    ridgeSupport385_rest_006 ridgeSupport385_rest_007 ridgeSupport385_rest_013
    ridgeSupport385_006 ridgeSupport385_suffix_007 ridgeSupport385_006_decode ridgeSupport385_suffix_decode_007
theorem ridgeSupport385_suffix_decode_005 : PackedRawNatGrowth.readList 13 239 ridgeSupport385_rest_005 =
    (ridgeSupport385_suffix_005, ridgeSupport385_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 207
    ridgeSupport385_rest_005 ridgeSupport385_rest_006 ridgeSupport385_rest_013
    ridgeSupport385_005 ridgeSupport385_suffix_006 ridgeSupport385_005_decode ridgeSupport385_suffix_decode_006
theorem ridgeSupport385_suffix_decode_004 : PackedRawNatGrowth.readList 13 271 ridgeSupport385_rest_004 =
    (ridgeSupport385_suffix_004, ridgeSupport385_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 239
    ridgeSupport385_rest_004 ridgeSupport385_rest_005 ridgeSupport385_rest_013
    ridgeSupport385_004 ridgeSupport385_suffix_005 ridgeSupport385_004_decode ridgeSupport385_suffix_decode_005
theorem ridgeSupport385_suffix_decode_003 : PackedRawNatGrowth.readList 13 303 ridgeSupport385_rest_003 =
    (ridgeSupport385_suffix_003, ridgeSupport385_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 271
    ridgeSupport385_rest_003 ridgeSupport385_rest_004 ridgeSupport385_rest_013
    ridgeSupport385_003 ridgeSupport385_suffix_004 ridgeSupport385_003_decode ridgeSupport385_suffix_decode_004
theorem ridgeSupport385_suffix_decode_002 : PackedRawNatGrowth.readList 13 335 ridgeSupport385_rest_002 =
    (ridgeSupport385_suffix_002, ridgeSupport385_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 303
    ridgeSupport385_rest_002 ridgeSupport385_rest_003 ridgeSupport385_rest_013
    ridgeSupport385_002 ridgeSupport385_suffix_003 ridgeSupport385_002_decode ridgeSupport385_suffix_decode_003
theorem ridgeSupport385_suffix_decode_001 : PackedRawNatGrowth.readList 13 367 ridgeSupport385_rest_001 =
    (ridgeSupport385_suffix_001, ridgeSupport385_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 335
    ridgeSupport385_rest_001 ridgeSupport385_rest_002 ridgeSupport385_rest_013
    ridgeSupport385_001 ridgeSupport385_suffix_002 ridgeSupport385_001_decode ridgeSupport385_suffix_decode_002
theorem ridgeSupport385_suffix_decode_000 : PackedRawNatGrowth.readList 13 399 ridgeSupport385_rest_000 =
    (ridgeSupport385_suffix_000, ridgeSupport385_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 367
    ridgeSupport385_rest_000 ridgeSupport385_rest_001 ridgeSupport385_rest_013
    ridgeSupport385_000 ridgeSupport385_suffix_001 ridgeSupport385_000_decode ridgeSupport385_suffix_decode_001
theorem ridgeSupport385_eq : candidateRows 385 = ridgeSupport385_suffix_000 := by
  change candidateSupports 385 = ridgeSupport385_suffix_000
  rw [ridgeSupport385_source]
  exact congrArg Prod.fst ridgeSupport385_suffix_decode_000
theorem ridgeTest_large_385 : ridgeTest 385 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport385_eq]
    simp only [ridgeSupport385_suffix_000, ridgeSupport385_suffix_001, ridgeSupport385_suffix_002, ridgeSupport385_suffix_003, ridgeSupport385_suffix_004, ridgeSupport385_suffix_005, ridgeSupport385_suffix_006, ridgeSupport385_suffix_007, ridgeSupport385_suffix_008, ridgeSupport385_suffix_009, ridgeSupport385_suffix_010, ridgeSupport385_suffix_011, ridgeSupport385_suffix_012, ridgeSupport385_suffix_013, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport385_000_mask, ridgeSupport385_001_mask, ridgeSupport385_002_mask, ridgeSupport385_003_mask, ridgeSupport385_004_mask, ridgeSupport385_005_mask, ridgeSupport385_006_mask, ridgeSupport385_007_mask, ridgeSupport385_008_mask, ridgeSupport385_009_mask, ridgeSupport385_010_mask, ridgeSupport385_011_mask, ridgeSupport385_012_mask]
    decide +kernel
  · rw [ridgeSupport385_eq]
    simp only [ridgeSupport385_suffix_000, ridgeSupport385_suffix_001, ridgeSupport385_suffix_002, ridgeSupport385_suffix_003, ridgeSupport385_suffix_004, ridgeSupport385_suffix_005, ridgeSupport385_suffix_006, ridgeSupport385_suffix_007, ridgeSupport385_suffix_008, ridgeSupport385_suffix_009, ridgeSupport385_suffix_010, ridgeSupport385_suffix_011, ridgeSupport385_suffix_012, ridgeSupport385_suffix_013, List.all_append, List.all_nil, ridgeSupport385_000_checked, ridgeSupport385_001_checked, ridgeSupport385_002_checked, ridgeSupport385_003_checked, ridgeSupport385_004_checked, ridgeSupport385_005_checked, ridgeSupport385_006_checked, ridgeSupport385_007_checked, ridgeSupport385_008_checked, ridgeSupport385_009_checked, ridgeSupport385_010_checked, ridgeSupport385_011_checked, ridgeSupport385_012_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase02
