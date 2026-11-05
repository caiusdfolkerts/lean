module
prelude
public import RootedSixBase02GrowthCacheRidgeSupport88Part000
public import RootedSixBase02GrowthCacheRidgeSupport88Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase02
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport88_suffix_decode_010 : PackedRawNatGrowth.readList 13 0 ridgeSupport88_rest_010 =
    (ridgeSupport88_suffix_010, ridgeSupport88_rest_010) := by rfl
theorem ridgeSupport88_suffix_decode_009 : PackedRawNatGrowth.readList 13 17 ridgeSupport88_rest_009 =
    (ridgeSupport88_suffix_009, ridgeSupport88_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 13 17 0
    ridgeSupport88_rest_009 ridgeSupport88_rest_010 ridgeSupport88_rest_010
    ridgeSupport88_009 ridgeSupport88_suffix_010 ridgeSupport88_009_decode ridgeSupport88_suffix_decode_010
theorem ridgeSupport88_suffix_decode_008 : PackedRawNatGrowth.readList 13 49 ridgeSupport88_rest_008 =
    (ridgeSupport88_suffix_008, ridgeSupport88_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 17
    ridgeSupport88_rest_008 ridgeSupport88_rest_009 ridgeSupport88_rest_010
    ridgeSupport88_008 ridgeSupport88_suffix_009 ridgeSupport88_008_decode ridgeSupport88_suffix_decode_009
theorem ridgeSupport88_suffix_decode_007 : PackedRawNatGrowth.readList 13 81 ridgeSupport88_rest_007 =
    (ridgeSupport88_suffix_007, ridgeSupport88_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 49
    ridgeSupport88_rest_007 ridgeSupport88_rest_008 ridgeSupport88_rest_010
    ridgeSupport88_007 ridgeSupport88_suffix_008 ridgeSupport88_007_decode ridgeSupport88_suffix_decode_008
theorem ridgeSupport88_suffix_decode_006 : PackedRawNatGrowth.readList 13 113 ridgeSupport88_rest_006 =
    (ridgeSupport88_suffix_006, ridgeSupport88_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 81
    ridgeSupport88_rest_006 ridgeSupport88_rest_007 ridgeSupport88_rest_010
    ridgeSupport88_006 ridgeSupport88_suffix_007 ridgeSupport88_006_decode ridgeSupport88_suffix_decode_007
theorem ridgeSupport88_suffix_decode_005 : PackedRawNatGrowth.readList 13 145 ridgeSupport88_rest_005 =
    (ridgeSupport88_suffix_005, ridgeSupport88_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 113
    ridgeSupport88_rest_005 ridgeSupport88_rest_006 ridgeSupport88_rest_010
    ridgeSupport88_005 ridgeSupport88_suffix_006 ridgeSupport88_005_decode ridgeSupport88_suffix_decode_006
theorem ridgeSupport88_suffix_decode_004 : PackedRawNatGrowth.readList 13 177 ridgeSupport88_rest_004 =
    (ridgeSupport88_suffix_004, ridgeSupport88_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 145
    ridgeSupport88_rest_004 ridgeSupport88_rest_005 ridgeSupport88_rest_010
    ridgeSupport88_004 ridgeSupport88_suffix_005 ridgeSupport88_004_decode ridgeSupport88_suffix_decode_005
theorem ridgeSupport88_suffix_decode_003 : PackedRawNatGrowth.readList 13 209 ridgeSupport88_rest_003 =
    (ridgeSupport88_suffix_003, ridgeSupport88_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 177
    ridgeSupport88_rest_003 ridgeSupport88_rest_004 ridgeSupport88_rest_010
    ridgeSupport88_003 ridgeSupport88_suffix_004 ridgeSupport88_003_decode ridgeSupport88_suffix_decode_004
theorem ridgeSupport88_suffix_decode_002 : PackedRawNatGrowth.readList 13 241 ridgeSupport88_rest_002 =
    (ridgeSupport88_suffix_002, ridgeSupport88_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 209
    ridgeSupport88_rest_002 ridgeSupport88_rest_003 ridgeSupport88_rest_010
    ridgeSupport88_002 ridgeSupport88_suffix_003 ridgeSupport88_002_decode ridgeSupport88_suffix_decode_003
theorem ridgeSupport88_suffix_decode_001 : PackedRawNatGrowth.readList 13 273 ridgeSupport88_rest_001 =
    (ridgeSupport88_suffix_001, ridgeSupport88_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 241
    ridgeSupport88_rest_001 ridgeSupport88_rest_002 ridgeSupport88_rest_010
    ridgeSupport88_001 ridgeSupport88_suffix_002 ridgeSupport88_001_decode ridgeSupport88_suffix_decode_002
theorem ridgeSupport88_suffix_decode_000 : PackedRawNatGrowth.readList 13 305 ridgeSupport88_rest_000 =
    (ridgeSupport88_suffix_000, ridgeSupport88_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 273
    ridgeSupport88_rest_000 ridgeSupport88_rest_001 ridgeSupport88_rest_010
    ridgeSupport88_000 ridgeSupport88_suffix_001 ridgeSupport88_000_decode ridgeSupport88_suffix_decode_001
theorem ridgeSupport88_eq : candidateRows 88 = ridgeSupport88_suffix_000 := by
  change candidateSupports 88 = ridgeSupport88_suffix_000
  rw [ridgeSupport88_source]
  exact congrArg Prod.fst ridgeSupport88_suffix_decode_000
theorem ridgeTest_large_88 : ridgeTest 88 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport88_eq]
    simp only [ridgeSupport88_suffix_000, ridgeSupport88_suffix_001, ridgeSupport88_suffix_002, ridgeSupport88_suffix_003, ridgeSupport88_suffix_004, ridgeSupport88_suffix_005, ridgeSupport88_suffix_006, ridgeSupport88_suffix_007, ridgeSupport88_suffix_008, ridgeSupport88_suffix_009, ridgeSupport88_suffix_010, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport88_000_mask, ridgeSupport88_001_mask, ridgeSupport88_002_mask, ridgeSupport88_003_mask, ridgeSupport88_004_mask, ridgeSupport88_005_mask, ridgeSupport88_006_mask, ridgeSupport88_007_mask, ridgeSupport88_008_mask, ridgeSupport88_009_mask]
    decide +kernel
  · rw [ridgeSupport88_eq]
    simp only [ridgeSupport88_suffix_000, ridgeSupport88_suffix_001, ridgeSupport88_suffix_002, ridgeSupport88_suffix_003, ridgeSupport88_suffix_004, ridgeSupport88_suffix_005, ridgeSupport88_suffix_006, ridgeSupport88_suffix_007, ridgeSupport88_suffix_008, ridgeSupport88_suffix_009, ridgeSupport88_suffix_010, List.all_append, List.all_nil, ridgeSupport88_000_checked, ridgeSupport88_001_checked, ridgeSupport88_002_checked, ridgeSupport88_003_checked, ridgeSupport88_004_checked, ridgeSupport88_005_checked, ridgeSupport88_006_checked, ridgeSupport88_007_checked, ridgeSupport88_008_checked, ridgeSupport88_009_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase02
