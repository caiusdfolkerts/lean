module
prelude
public import RootedSixBase02GrowthCacheRidgeSupport133Part000
public import RootedSixBase02GrowthCacheRidgeSupport133Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase02
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport133_suffix_decode_010 : PackedRawNatGrowth.readList 13 0 ridgeSupport133_rest_010 =
    (ridgeSupport133_suffix_010, ridgeSupport133_rest_010) := by rfl
theorem ridgeSupport133_suffix_decode_009 : PackedRawNatGrowth.readList 13 17 ridgeSupport133_rest_009 =
    (ridgeSupport133_suffix_009, ridgeSupport133_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 13 17 0
    ridgeSupport133_rest_009 ridgeSupport133_rest_010 ridgeSupport133_rest_010
    ridgeSupport133_009 ridgeSupport133_suffix_010 ridgeSupport133_009_decode ridgeSupport133_suffix_decode_010
theorem ridgeSupport133_suffix_decode_008 : PackedRawNatGrowth.readList 13 49 ridgeSupport133_rest_008 =
    (ridgeSupport133_suffix_008, ridgeSupport133_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 17
    ridgeSupport133_rest_008 ridgeSupport133_rest_009 ridgeSupport133_rest_010
    ridgeSupport133_008 ridgeSupport133_suffix_009 ridgeSupport133_008_decode ridgeSupport133_suffix_decode_009
theorem ridgeSupport133_suffix_decode_007 : PackedRawNatGrowth.readList 13 81 ridgeSupport133_rest_007 =
    (ridgeSupport133_suffix_007, ridgeSupport133_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 49
    ridgeSupport133_rest_007 ridgeSupport133_rest_008 ridgeSupport133_rest_010
    ridgeSupport133_007 ridgeSupport133_suffix_008 ridgeSupport133_007_decode ridgeSupport133_suffix_decode_008
theorem ridgeSupport133_suffix_decode_006 : PackedRawNatGrowth.readList 13 113 ridgeSupport133_rest_006 =
    (ridgeSupport133_suffix_006, ridgeSupport133_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 81
    ridgeSupport133_rest_006 ridgeSupport133_rest_007 ridgeSupport133_rest_010
    ridgeSupport133_006 ridgeSupport133_suffix_007 ridgeSupport133_006_decode ridgeSupport133_suffix_decode_007
theorem ridgeSupport133_suffix_decode_005 : PackedRawNatGrowth.readList 13 145 ridgeSupport133_rest_005 =
    (ridgeSupport133_suffix_005, ridgeSupport133_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 113
    ridgeSupport133_rest_005 ridgeSupport133_rest_006 ridgeSupport133_rest_010
    ridgeSupport133_005 ridgeSupport133_suffix_006 ridgeSupport133_005_decode ridgeSupport133_suffix_decode_006
theorem ridgeSupport133_suffix_decode_004 : PackedRawNatGrowth.readList 13 177 ridgeSupport133_rest_004 =
    (ridgeSupport133_suffix_004, ridgeSupport133_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 145
    ridgeSupport133_rest_004 ridgeSupport133_rest_005 ridgeSupport133_rest_010
    ridgeSupport133_004 ridgeSupport133_suffix_005 ridgeSupport133_004_decode ridgeSupport133_suffix_decode_005
theorem ridgeSupport133_suffix_decode_003 : PackedRawNatGrowth.readList 13 209 ridgeSupport133_rest_003 =
    (ridgeSupport133_suffix_003, ridgeSupport133_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 177
    ridgeSupport133_rest_003 ridgeSupport133_rest_004 ridgeSupport133_rest_010
    ridgeSupport133_003 ridgeSupport133_suffix_004 ridgeSupport133_003_decode ridgeSupport133_suffix_decode_004
theorem ridgeSupport133_suffix_decode_002 : PackedRawNatGrowth.readList 13 241 ridgeSupport133_rest_002 =
    (ridgeSupport133_suffix_002, ridgeSupport133_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 209
    ridgeSupport133_rest_002 ridgeSupport133_rest_003 ridgeSupport133_rest_010
    ridgeSupport133_002 ridgeSupport133_suffix_003 ridgeSupport133_002_decode ridgeSupport133_suffix_decode_003
theorem ridgeSupport133_suffix_decode_001 : PackedRawNatGrowth.readList 13 273 ridgeSupport133_rest_001 =
    (ridgeSupport133_suffix_001, ridgeSupport133_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 241
    ridgeSupport133_rest_001 ridgeSupport133_rest_002 ridgeSupport133_rest_010
    ridgeSupport133_001 ridgeSupport133_suffix_002 ridgeSupport133_001_decode ridgeSupport133_suffix_decode_002
theorem ridgeSupport133_suffix_decode_000 : PackedRawNatGrowth.readList 13 305 ridgeSupport133_rest_000 =
    (ridgeSupport133_suffix_000, ridgeSupport133_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 273
    ridgeSupport133_rest_000 ridgeSupport133_rest_001 ridgeSupport133_rest_010
    ridgeSupport133_000 ridgeSupport133_suffix_001 ridgeSupport133_000_decode ridgeSupport133_suffix_decode_001
theorem ridgeSupport133_eq : candidateRows 133 = ridgeSupport133_suffix_000 := by
  change candidateSupports 133 = ridgeSupport133_suffix_000
  rw [ridgeSupport133_source]
  exact congrArg Prod.fst ridgeSupport133_suffix_decode_000
theorem ridgeTest_large_133 : ridgeTest 133 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport133_eq]
    simp only [ridgeSupport133_suffix_000, ridgeSupport133_suffix_001, ridgeSupport133_suffix_002, ridgeSupport133_suffix_003, ridgeSupport133_suffix_004, ridgeSupport133_suffix_005, ridgeSupport133_suffix_006, ridgeSupport133_suffix_007, ridgeSupport133_suffix_008, ridgeSupport133_suffix_009, ridgeSupport133_suffix_010, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport133_000_mask, ridgeSupport133_001_mask, ridgeSupport133_002_mask, ridgeSupport133_003_mask, ridgeSupport133_004_mask, ridgeSupport133_005_mask, ridgeSupport133_006_mask, ridgeSupport133_007_mask, ridgeSupport133_008_mask, ridgeSupport133_009_mask]
    decide +kernel
  · rw [ridgeSupport133_eq]
    simp only [ridgeSupport133_suffix_000, ridgeSupport133_suffix_001, ridgeSupport133_suffix_002, ridgeSupport133_suffix_003, ridgeSupport133_suffix_004, ridgeSupport133_suffix_005, ridgeSupport133_suffix_006, ridgeSupport133_suffix_007, ridgeSupport133_suffix_008, ridgeSupport133_suffix_009, ridgeSupport133_suffix_010, List.all_append, List.all_nil, ridgeSupport133_000_checked, ridgeSupport133_001_checked, ridgeSupport133_002_checked, ridgeSupport133_003_checked, ridgeSupport133_004_checked, ridgeSupport133_005_checked, ridgeSupport133_006_checked, ridgeSupport133_007_checked, ridgeSupport133_008_checked, ridgeSupport133_009_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase02
