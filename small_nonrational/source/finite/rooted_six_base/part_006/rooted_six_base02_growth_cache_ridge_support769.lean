module
prelude
public import RootedSixBase02GrowthCacheRidgeSupport769Part000
public import RootedSixBase02GrowthCacheRidgeSupport769Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase02
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport769_suffix_decode_013 : PackedRawNatGrowth.readList 13 0 ridgeSupport769_rest_013 =
    (ridgeSupport769_suffix_013, ridgeSupport769_rest_013) := by rfl
theorem ridgeSupport769_suffix_decode_012 : PackedRawNatGrowth.readList 13 15 ridgeSupport769_rest_012 =
    (ridgeSupport769_suffix_012, ridgeSupport769_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 13 15 0
    ridgeSupport769_rest_012 ridgeSupport769_rest_013 ridgeSupport769_rest_013
    ridgeSupport769_012 ridgeSupport769_suffix_013 ridgeSupport769_012_decode ridgeSupport769_suffix_decode_013
theorem ridgeSupport769_suffix_decode_011 : PackedRawNatGrowth.readList 13 47 ridgeSupport769_rest_011 =
    (ridgeSupport769_suffix_011, ridgeSupport769_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 15
    ridgeSupport769_rest_011 ridgeSupport769_rest_012 ridgeSupport769_rest_013
    ridgeSupport769_011 ridgeSupport769_suffix_012 ridgeSupport769_011_decode ridgeSupport769_suffix_decode_012
theorem ridgeSupport769_suffix_decode_010 : PackedRawNatGrowth.readList 13 79 ridgeSupport769_rest_010 =
    (ridgeSupport769_suffix_010, ridgeSupport769_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 47
    ridgeSupport769_rest_010 ridgeSupport769_rest_011 ridgeSupport769_rest_013
    ridgeSupport769_010 ridgeSupport769_suffix_011 ridgeSupport769_010_decode ridgeSupport769_suffix_decode_011
theorem ridgeSupport769_suffix_decode_009 : PackedRawNatGrowth.readList 13 111 ridgeSupport769_rest_009 =
    (ridgeSupport769_suffix_009, ridgeSupport769_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 79
    ridgeSupport769_rest_009 ridgeSupport769_rest_010 ridgeSupport769_rest_013
    ridgeSupport769_009 ridgeSupport769_suffix_010 ridgeSupport769_009_decode ridgeSupport769_suffix_decode_010
theorem ridgeSupport769_suffix_decode_008 : PackedRawNatGrowth.readList 13 143 ridgeSupport769_rest_008 =
    (ridgeSupport769_suffix_008, ridgeSupport769_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 111
    ridgeSupport769_rest_008 ridgeSupport769_rest_009 ridgeSupport769_rest_013
    ridgeSupport769_008 ridgeSupport769_suffix_009 ridgeSupport769_008_decode ridgeSupport769_suffix_decode_009
theorem ridgeSupport769_suffix_decode_007 : PackedRawNatGrowth.readList 13 175 ridgeSupport769_rest_007 =
    (ridgeSupport769_suffix_007, ridgeSupport769_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 143
    ridgeSupport769_rest_007 ridgeSupport769_rest_008 ridgeSupport769_rest_013
    ridgeSupport769_007 ridgeSupport769_suffix_008 ridgeSupport769_007_decode ridgeSupport769_suffix_decode_008
theorem ridgeSupport769_suffix_decode_006 : PackedRawNatGrowth.readList 13 207 ridgeSupport769_rest_006 =
    (ridgeSupport769_suffix_006, ridgeSupport769_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 175
    ridgeSupport769_rest_006 ridgeSupport769_rest_007 ridgeSupport769_rest_013
    ridgeSupport769_006 ridgeSupport769_suffix_007 ridgeSupport769_006_decode ridgeSupport769_suffix_decode_007
theorem ridgeSupport769_suffix_decode_005 : PackedRawNatGrowth.readList 13 239 ridgeSupport769_rest_005 =
    (ridgeSupport769_suffix_005, ridgeSupport769_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 207
    ridgeSupport769_rest_005 ridgeSupport769_rest_006 ridgeSupport769_rest_013
    ridgeSupport769_005 ridgeSupport769_suffix_006 ridgeSupport769_005_decode ridgeSupport769_suffix_decode_006
theorem ridgeSupport769_suffix_decode_004 : PackedRawNatGrowth.readList 13 271 ridgeSupport769_rest_004 =
    (ridgeSupport769_suffix_004, ridgeSupport769_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 239
    ridgeSupport769_rest_004 ridgeSupport769_rest_005 ridgeSupport769_rest_013
    ridgeSupport769_004 ridgeSupport769_suffix_005 ridgeSupport769_004_decode ridgeSupport769_suffix_decode_005
theorem ridgeSupport769_suffix_decode_003 : PackedRawNatGrowth.readList 13 303 ridgeSupport769_rest_003 =
    (ridgeSupport769_suffix_003, ridgeSupport769_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 271
    ridgeSupport769_rest_003 ridgeSupport769_rest_004 ridgeSupport769_rest_013
    ridgeSupport769_003 ridgeSupport769_suffix_004 ridgeSupport769_003_decode ridgeSupport769_suffix_decode_004
theorem ridgeSupport769_suffix_decode_002 : PackedRawNatGrowth.readList 13 335 ridgeSupport769_rest_002 =
    (ridgeSupport769_suffix_002, ridgeSupport769_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 303
    ridgeSupport769_rest_002 ridgeSupport769_rest_003 ridgeSupport769_rest_013
    ridgeSupport769_002 ridgeSupport769_suffix_003 ridgeSupport769_002_decode ridgeSupport769_suffix_decode_003
theorem ridgeSupport769_suffix_decode_001 : PackedRawNatGrowth.readList 13 367 ridgeSupport769_rest_001 =
    (ridgeSupport769_suffix_001, ridgeSupport769_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 335
    ridgeSupport769_rest_001 ridgeSupport769_rest_002 ridgeSupport769_rest_013
    ridgeSupport769_001 ridgeSupport769_suffix_002 ridgeSupport769_001_decode ridgeSupport769_suffix_decode_002
theorem ridgeSupport769_suffix_decode_000 : PackedRawNatGrowth.readList 13 399 ridgeSupport769_rest_000 =
    (ridgeSupport769_suffix_000, ridgeSupport769_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 367
    ridgeSupport769_rest_000 ridgeSupport769_rest_001 ridgeSupport769_rest_013
    ridgeSupport769_000 ridgeSupport769_suffix_001 ridgeSupport769_000_decode ridgeSupport769_suffix_decode_001
theorem ridgeSupport769_eq : candidateRows 769 = ridgeSupport769_suffix_000 := by
  change candidateSupports 769 = ridgeSupport769_suffix_000
  rw [ridgeSupport769_source]
  exact congrArg Prod.fst ridgeSupport769_suffix_decode_000
theorem ridgeTest_large_769 : ridgeTest 769 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport769_eq]
    simp only [ridgeSupport769_suffix_000, ridgeSupport769_suffix_001, ridgeSupport769_suffix_002, ridgeSupport769_suffix_003, ridgeSupport769_suffix_004, ridgeSupport769_suffix_005, ridgeSupport769_suffix_006, ridgeSupport769_suffix_007, ridgeSupport769_suffix_008, ridgeSupport769_suffix_009, ridgeSupport769_suffix_010, ridgeSupport769_suffix_011, ridgeSupport769_suffix_012, ridgeSupport769_suffix_013, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport769_000_mask, ridgeSupport769_001_mask, ridgeSupport769_002_mask, ridgeSupport769_003_mask, ridgeSupport769_004_mask, ridgeSupport769_005_mask, ridgeSupport769_006_mask, ridgeSupport769_007_mask, ridgeSupport769_008_mask, ridgeSupport769_009_mask, ridgeSupport769_010_mask, ridgeSupport769_011_mask, ridgeSupport769_012_mask]
    decide +kernel
  · rw [ridgeSupport769_eq]
    simp only [ridgeSupport769_suffix_000, ridgeSupport769_suffix_001, ridgeSupport769_suffix_002, ridgeSupport769_suffix_003, ridgeSupport769_suffix_004, ridgeSupport769_suffix_005, ridgeSupport769_suffix_006, ridgeSupport769_suffix_007, ridgeSupport769_suffix_008, ridgeSupport769_suffix_009, ridgeSupport769_suffix_010, ridgeSupport769_suffix_011, ridgeSupport769_suffix_012, ridgeSupport769_suffix_013, List.all_append, List.all_nil, ridgeSupport769_000_checked, ridgeSupport769_001_checked, ridgeSupport769_002_checked, ridgeSupport769_003_checked, ridgeSupport769_004_checked, ridgeSupport769_005_checked, ridgeSupport769_006_checked, ridgeSupport769_007_checked, ridgeSupport769_008_checked, ridgeSupport769_009_checked, ridgeSupport769_010_checked, ridgeSupport769_011_checked, ridgeSupport769_012_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase02
