module
prelude
public import RootedSixBase02GrowthCacheRidgeSupport280Part000
public import RootedSixBase02GrowthCacheRidgeSupport280Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase02
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport280_suffix_decode_010 : PackedRawNatGrowth.readList 13 0 ridgeSupport280_rest_010 =
    (ridgeSupport280_suffix_010, ridgeSupport280_rest_010) := by rfl
theorem ridgeSupport280_suffix_decode_009 : PackedRawNatGrowth.readList 13 17 ridgeSupport280_rest_009 =
    (ridgeSupport280_suffix_009, ridgeSupport280_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 13 17 0
    ridgeSupport280_rest_009 ridgeSupport280_rest_010 ridgeSupport280_rest_010
    ridgeSupport280_009 ridgeSupport280_suffix_010 ridgeSupport280_009_decode ridgeSupport280_suffix_decode_010
theorem ridgeSupport280_suffix_decode_008 : PackedRawNatGrowth.readList 13 49 ridgeSupport280_rest_008 =
    (ridgeSupport280_suffix_008, ridgeSupport280_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 17
    ridgeSupport280_rest_008 ridgeSupport280_rest_009 ridgeSupport280_rest_010
    ridgeSupport280_008 ridgeSupport280_suffix_009 ridgeSupport280_008_decode ridgeSupport280_suffix_decode_009
theorem ridgeSupport280_suffix_decode_007 : PackedRawNatGrowth.readList 13 81 ridgeSupport280_rest_007 =
    (ridgeSupport280_suffix_007, ridgeSupport280_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 49
    ridgeSupport280_rest_007 ridgeSupport280_rest_008 ridgeSupport280_rest_010
    ridgeSupport280_007 ridgeSupport280_suffix_008 ridgeSupport280_007_decode ridgeSupport280_suffix_decode_008
theorem ridgeSupport280_suffix_decode_006 : PackedRawNatGrowth.readList 13 113 ridgeSupport280_rest_006 =
    (ridgeSupport280_suffix_006, ridgeSupport280_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 81
    ridgeSupport280_rest_006 ridgeSupport280_rest_007 ridgeSupport280_rest_010
    ridgeSupport280_006 ridgeSupport280_suffix_007 ridgeSupport280_006_decode ridgeSupport280_suffix_decode_007
theorem ridgeSupport280_suffix_decode_005 : PackedRawNatGrowth.readList 13 145 ridgeSupport280_rest_005 =
    (ridgeSupport280_suffix_005, ridgeSupport280_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 113
    ridgeSupport280_rest_005 ridgeSupport280_rest_006 ridgeSupport280_rest_010
    ridgeSupport280_005 ridgeSupport280_suffix_006 ridgeSupport280_005_decode ridgeSupport280_suffix_decode_006
theorem ridgeSupport280_suffix_decode_004 : PackedRawNatGrowth.readList 13 177 ridgeSupport280_rest_004 =
    (ridgeSupport280_suffix_004, ridgeSupport280_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 145
    ridgeSupport280_rest_004 ridgeSupport280_rest_005 ridgeSupport280_rest_010
    ridgeSupport280_004 ridgeSupport280_suffix_005 ridgeSupport280_004_decode ridgeSupport280_suffix_decode_005
theorem ridgeSupport280_suffix_decode_003 : PackedRawNatGrowth.readList 13 209 ridgeSupport280_rest_003 =
    (ridgeSupport280_suffix_003, ridgeSupport280_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 177
    ridgeSupport280_rest_003 ridgeSupport280_rest_004 ridgeSupport280_rest_010
    ridgeSupport280_003 ridgeSupport280_suffix_004 ridgeSupport280_003_decode ridgeSupport280_suffix_decode_004
theorem ridgeSupport280_suffix_decode_002 : PackedRawNatGrowth.readList 13 241 ridgeSupport280_rest_002 =
    (ridgeSupport280_suffix_002, ridgeSupport280_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 209
    ridgeSupport280_rest_002 ridgeSupport280_rest_003 ridgeSupport280_rest_010
    ridgeSupport280_002 ridgeSupport280_suffix_003 ridgeSupport280_002_decode ridgeSupport280_suffix_decode_003
theorem ridgeSupport280_suffix_decode_001 : PackedRawNatGrowth.readList 13 273 ridgeSupport280_rest_001 =
    (ridgeSupport280_suffix_001, ridgeSupport280_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 241
    ridgeSupport280_rest_001 ridgeSupport280_rest_002 ridgeSupport280_rest_010
    ridgeSupport280_001 ridgeSupport280_suffix_002 ridgeSupport280_001_decode ridgeSupport280_suffix_decode_002
theorem ridgeSupport280_suffix_decode_000 : PackedRawNatGrowth.readList 13 305 ridgeSupport280_rest_000 =
    (ridgeSupport280_suffix_000, ridgeSupport280_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 273
    ridgeSupport280_rest_000 ridgeSupport280_rest_001 ridgeSupport280_rest_010
    ridgeSupport280_000 ridgeSupport280_suffix_001 ridgeSupport280_000_decode ridgeSupport280_suffix_decode_001
theorem ridgeSupport280_eq : candidateRows 280 = ridgeSupport280_suffix_000 := by
  change candidateSupports 280 = ridgeSupport280_suffix_000
  rw [ridgeSupport280_source]
  exact congrArg Prod.fst ridgeSupport280_suffix_decode_000
theorem ridgeTest_large_280 : ridgeTest 280 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport280_eq]
    simp only [ridgeSupport280_suffix_000, ridgeSupport280_suffix_001, ridgeSupport280_suffix_002, ridgeSupport280_suffix_003, ridgeSupport280_suffix_004, ridgeSupport280_suffix_005, ridgeSupport280_suffix_006, ridgeSupport280_suffix_007, ridgeSupport280_suffix_008, ridgeSupport280_suffix_009, ridgeSupport280_suffix_010, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport280_000_mask, ridgeSupport280_001_mask, ridgeSupport280_002_mask, ridgeSupport280_003_mask, ridgeSupport280_004_mask, ridgeSupport280_005_mask, ridgeSupport280_006_mask, ridgeSupport280_007_mask, ridgeSupport280_008_mask, ridgeSupport280_009_mask]
    decide +kernel
  · rw [ridgeSupport280_eq]
    simp only [ridgeSupport280_suffix_000, ridgeSupport280_suffix_001, ridgeSupport280_suffix_002, ridgeSupport280_suffix_003, ridgeSupport280_suffix_004, ridgeSupport280_suffix_005, ridgeSupport280_suffix_006, ridgeSupport280_suffix_007, ridgeSupport280_suffix_008, ridgeSupport280_suffix_009, ridgeSupport280_suffix_010, List.all_append, List.all_nil, ridgeSupport280_000_checked, ridgeSupport280_001_checked, ridgeSupport280_002_checked, ridgeSupport280_003_checked, ridgeSupport280_004_checked, ridgeSupport280_005_checked, ridgeSupport280_006_checked, ridgeSupport280_007_checked, ridgeSupport280_008_checked, ridgeSupport280_009_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase02
