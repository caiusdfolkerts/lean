module
prelude
public import RootedSixBase02GrowthCacheRidgeSupport261Part000
public import RootedSixBase02GrowthCacheRidgeSupport261Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase02
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport261_suffix_decode_010 : PackedRawNatGrowth.readList 13 0 ridgeSupport261_rest_010 =
    (ridgeSupport261_suffix_010, ridgeSupport261_rest_010) := by rfl
theorem ridgeSupport261_suffix_decode_009 : PackedRawNatGrowth.readList 13 17 ridgeSupport261_rest_009 =
    (ridgeSupport261_suffix_009, ridgeSupport261_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 13 17 0
    ridgeSupport261_rest_009 ridgeSupport261_rest_010 ridgeSupport261_rest_010
    ridgeSupport261_009 ridgeSupport261_suffix_010 ridgeSupport261_009_decode ridgeSupport261_suffix_decode_010
theorem ridgeSupport261_suffix_decode_008 : PackedRawNatGrowth.readList 13 49 ridgeSupport261_rest_008 =
    (ridgeSupport261_suffix_008, ridgeSupport261_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 17
    ridgeSupport261_rest_008 ridgeSupport261_rest_009 ridgeSupport261_rest_010
    ridgeSupport261_008 ridgeSupport261_suffix_009 ridgeSupport261_008_decode ridgeSupport261_suffix_decode_009
theorem ridgeSupport261_suffix_decode_007 : PackedRawNatGrowth.readList 13 81 ridgeSupport261_rest_007 =
    (ridgeSupport261_suffix_007, ridgeSupport261_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 49
    ridgeSupport261_rest_007 ridgeSupport261_rest_008 ridgeSupport261_rest_010
    ridgeSupport261_007 ridgeSupport261_suffix_008 ridgeSupport261_007_decode ridgeSupport261_suffix_decode_008
theorem ridgeSupport261_suffix_decode_006 : PackedRawNatGrowth.readList 13 113 ridgeSupport261_rest_006 =
    (ridgeSupport261_suffix_006, ridgeSupport261_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 81
    ridgeSupport261_rest_006 ridgeSupport261_rest_007 ridgeSupport261_rest_010
    ridgeSupport261_006 ridgeSupport261_suffix_007 ridgeSupport261_006_decode ridgeSupport261_suffix_decode_007
theorem ridgeSupport261_suffix_decode_005 : PackedRawNatGrowth.readList 13 145 ridgeSupport261_rest_005 =
    (ridgeSupport261_suffix_005, ridgeSupport261_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 113
    ridgeSupport261_rest_005 ridgeSupport261_rest_006 ridgeSupport261_rest_010
    ridgeSupport261_005 ridgeSupport261_suffix_006 ridgeSupport261_005_decode ridgeSupport261_suffix_decode_006
theorem ridgeSupport261_suffix_decode_004 : PackedRawNatGrowth.readList 13 177 ridgeSupport261_rest_004 =
    (ridgeSupport261_suffix_004, ridgeSupport261_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 145
    ridgeSupport261_rest_004 ridgeSupport261_rest_005 ridgeSupport261_rest_010
    ridgeSupport261_004 ridgeSupport261_suffix_005 ridgeSupport261_004_decode ridgeSupport261_suffix_decode_005
theorem ridgeSupport261_suffix_decode_003 : PackedRawNatGrowth.readList 13 209 ridgeSupport261_rest_003 =
    (ridgeSupport261_suffix_003, ridgeSupport261_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 177
    ridgeSupport261_rest_003 ridgeSupport261_rest_004 ridgeSupport261_rest_010
    ridgeSupport261_003 ridgeSupport261_suffix_004 ridgeSupport261_003_decode ridgeSupport261_suffix_decode_004
theorem ridgeSupport261_suffix_decode_002 : PackedRawNatGrowth.readList 13 241 ridgeSupport261_rest_002 =
    (ridgeSupport261_suffix_002, ridgeSupport261_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 209
    ridgeSupport261_rest_002 ridgeSupport261_rest_003 ridgeSupport261_rest_010
    ridgeSupport261_002 ridgeSupport261_suffix_003 ridgeSupport261_002_decode ridgeSupport261_suffix_decode_003
theorem ridgeSupport261_suffix_decode_001 : PackedRawNatGrowth.readList 13 273 ridgeSupport261_rest_001 =
    (ridgeSupport261_suffix_001, ridgeSupport261_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 241
    ridgeSupport261_rest_001 ridgeSupport261_rest_002 ridgeSupport261_rest_010
    ridgeSupport261_001 ridgeSupport261_suffix_002 ridgeSupport261_001_decode ridgeSupport261_suffix_decode_002
theorem ridgeSupport261_suffix_decode_000 : PackedRawNatGrowth.readList 13 305 ridgeSupport261_rest_000 =
    (ridgeSupport261_suffix_000, ridgeSupport261_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 273
    ridgeSupport261_rest_000 ridgeSupport261_rest_001 ridgeSupport261_rest_010
    ridgeSupport261_000 ridgeSupport261_suffix_001 ridgeSupport261_000_decode ridgeSupport261_suffix_decode_001
theorem ridgeSupport261_eq : candidateRows 261 = ridgeSupport261_suffix_000 := by
  change candidateSupports 261 = ridgeSupport261_suffix_000
  rw [ridgeSupport261_source]
  exact congrArg Prod.fst ridgeSupport261_suffix_decode_000
theorem ridgeTest_large_261 : ridgeTest 261 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport261_eq]
    simp only [ridgeSupport261_suffix_000, ridgeSupport261_suffix_001, ridgeSupport261_suffix_002, ridgeSupport261_suffix_003, ridgeSupport261_suffix_004, ridgeSupport261_suffix_005, ridgeSupport261_suffix_006, ridgeSupport261_suffix_007, ridgeSupport261_suffix_008, ridgeSupport261_suffix_009, ridgeSupport261_suffix_010, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport261_000_mask, ridgeSupport261_001_mask, ridgeSupport261_002_mask, ridgeSupport261_003_mask, ridgeSupport261_004_mask, ridgeSupport261_005_mask, ridgeSupport261_006_mask, ridgeSupport261_007_mask, ridgeSupport261_008_mask, ridgeSupport261_009_mask]
    decide +kernel
  · rw [ridgeSupport261_eq]
    simp only [ridgeSupport261_suffix_000, ridgeSupport261_suffix_001, ridgeSupport261_suffix_002, ridgeSupport261_suffix_003, ridgeSupport261_suffix_004, ridgeSupport261_suffix_005, ridgeSupport261_suffix_006, ridgeSupport261_suffix_007, ridgeSupport261_suffix_008, ridgeSupport261_suffix_009, ridgeSupport261_suffix_010, List.all_append, List.all_nil, ridgeSupport261_000_checked, ridgeSupport261_001_checked, ridgeSupport261_002_checked, ridgeSupport261_003_checked, ridgeSupport261_004_checked, ridgeSupport261_005_checked, ridgeSupport261_006_checked, ridgeSupport261_007_checked, ridgeSupport261_008_checked, ridgeSupport261_009_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase02
