module
prelude
public import RootedSixBase02GrowthCacheRidgeSupport290Part000
public import RootedSixBase02GrowthCacheRidgeSupport290Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase02
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport290_suffix_decode_010 : PackedRawNatGrowth.readList 13 0 ridgeSupport290_rest_010 =
    (ridgeSupport290_suffix_010, ridgeSupport290_rest_010) := by rfl
theorem ridgeSupport290_suffix_decode_009 : PackedRawNatGrowth.readList 13 17 ridgeSupport290_rest_009 =
    (ridgeSupport290_suffix_009, ridgeSupport290_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 13 17 0
    ridgeSupport290_rest_009 ridgeSupport290_rest_010 ridgeSupport290_rest_010
    ridgeSupport290_009 ridgeSupport290_suffix_010 ridgeSupport290_009_decode ridgeSupport290_suffix_decode_010
theorem ridgeSupport290_suffix_decode_008 : PackedRawNatGrowth.readList 13 49 ridgeSupport290_rest_008 =
    (ridgeSupport290_suffix_008, ridgeSupport290_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 17
    ridgeSupport290_rest_008 ridgeSupport290_rest_009 ridgeSupport290_rest_010
    ridgeSupport290_008 ridgeSupport290_suffix_009 ridgeSupport290_008_decode ridgeSupport290_suffix_decode_009
theorem ridgeSupport290_suffix_decode_007 : PackedRawNatGrowth.readList 13 81 ridgeSupport290_rest_007 =
    (ridgeSupport290_suffix_007, ridgeSupport290_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 49
    ridgeSupport290_rest_007 ridgeSupport290_rest_008 ridgeSupport290_rest_010
    ridgeSupport290_007 ridgeSupport290_suffix_008 ridgeSupport290_007_decode ridgeSupport290_suffix_decode_008
theorem ridgeSupport290_suffix_decode_006 : PackedRawNatGrowth.readList 13 113 ridgeSupport290_rest_006 =
    (ridgeSupport290_suffix_006, ridgeSupport290_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 81
    ridgeSupport290_rest_006 ridgeSupport290_rest_007 ridgeSupport290_rest_010
    ridgeSupport290_006 ridgeSupport290_suffix_007 ridgeSupport290_006_decode ridgeSupport290_suffix_decode_007
theorem ridgeSupport290_suffix_decode_005 : PackedRawNatGrowth.readList 13 145 ridgeSupport290_rest_005 =
    (ridgeSupport290_suffix_005, ridgeSupport290_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 113
    ridgeSupport290_rest_005 ridgeSupport290_rest_006 ridgeSupport290_rest_010
    ridgeSupport290_005 ridgeSupport290_suffix_006 ridgeSupport290_005_decode ridgeSupport290_suffix_decode_006
theorem ridgeSupport290_suffix_decode_004 : PackedRawNatGrowth.readList 13 177 ridgeSupport290_rest_004 =
    (ridgeSupport290_suffix_004, ridgeSupport290_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 145
    ridgeSupport290_rest_004 ridgeSupport290_rest_005 ridgeSupport290_rest_010
    ridgeSupport290_004 ridgeSupport290_suffix_005 ridgeSupport290_004_decode ridgeSupport290_suffix_decode_005
theorem ridgeSupport290_suffix_decode_003 : PackedRawNatGrowth.readList 13 209 ridgeSupport290_rest_003 =
    (ridgeSupport290_suffix_003, ridgeSupport290_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 177
    ridgeSupport290_rest_003 ridgeSupport290_rest_004 ridgeSupport290_rest_010
    ridgeSupport290_003 ridgeSupport290_suffix_004 ridgeSupport290_003_decode ridgeSupport290_suffix_decode_004
theorem ridgeSupport290_suffix_decode_002 : PackedRawNatGrowth.readList 13 241 ridgeSupport290_rest_002 =
    (ridgeSupport290_suffix_002, ridgeSupport290_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 209
    ridgeSupport290_rest_002 ridgeSupport290_rest_003 ridgeSupport290_rest_010
    ridgeSupport290_002 ridgeSupport290_suffix_003 ridgeSupport290_002_decode ridgeSupport290_suffix_decode_003
theorem ridgeSupport290_suffix_decode_001 : PackedRawNatGrowth.readList 13 273 ridgeSupport290_rest_001 =
    (ridgeSupport290_suffix_001, ridgeSupport290_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 241
    ridgeSupport290_rest_001 ridgeSupport290_rest_002 ridgeSupport290_rest_010
    ridgeSupport290_001 ridgeSupport290_suffix_002 ridgeSupport290_001_decode ridgeSupport290_suffix_decode_002
theorem ridgeSupport290_suffix_decode_000 : PackedRawNatGrowth.readList 13 305 ridgeSupport290_rest_000 =
    (ridgeSupport290_suffix_000, ridgeSupport290_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 273
    ridgeSupport290_rest_000 ridgeSupport290_rest_001 ridgeSupport290_rest_010
    ridgeSupport290_000 ridgeSupport290_suffix_001 ridgeSupport290_000_decode ridgeSupport290_suffix_decode_001
theorem ridgeSupport290_eq : candidateRows 290 = ridgeSupport290_suffix_000 := by
  change candidateSupports 290 = ridgeSupport290_suffix_000
  rw [ridgeSupport290_source]
  exact congrArg Prod.fst ridgeSupport290_suffix_decode_000
theorem ridgeTest_large_290 : ridgeTest 290 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport290_eq]
    simp only [ridgeSupport290_suffix_000, ridgeSupport290_suffix_001, ridgeSupport290_suffix_002, ridgeSupport290_suffix_003, ridgeSupport290_suffix_004, ridgeSupport290_suffix_005, ridgeSupport290_suffix_006, ridgeSupport290_suffix_007, ridgeSupport290_suffix_008, ridgeSupport290_suffix_009, ridgeSupport290_suffix_010, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport290_000_mask, ridgeSupport290_001_mask, ridgeSupport290_002_mask, ridgeSupport290_003_mask, ridgeSupport290_004_mask, ridgeSupport290_005_mask, ridgeSupport290_006_mask, ridgeSupport290_007_mask, ridgeSupport290_008_mask, ridgeSupport290_009_mask]
    decide +kernel
  · rw [ridgeSupport290_eq]
    simp only [ridgeSupport290_suffix_000, ridgeSupport290_suffix_001, ridgeSupport290_suffix_002, ridgeSupport290_suffix_003, ridgeSupport290_suffix_004, ridgeSupport290_suffix_005, ridgeSupport290_suffix_006, ridgeSupport290_suffix_007, ridgeSupport290_suffix_008, ridgeSupport290_suffix_009, ridgeSupport290_suffix_010, List.all_append, List.all_nil, ridgeSupport290_000_checked, ridgeSupport290_001_checked, ridgeSupport290_002_checked, ridgeSupport290_003_checked, ridgeSupport290_004_checked, ridgeSupport290_005_checked, ridgeSupport290_006_checked, ridgeSupport290_007_checked, ridgeSupport290_008_checked, ridgeSupport290_009_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase02
