module
prelude
public import RootedSixBase02GrowthCacheRidgeSupport546Part000
public import RootedSixBase02GrowthCacheRidgeSupport546Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase02
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport546_suffix_decode_010 : PackedRawNatGrowth.readList 13 0 ridgeSupport546_rest_010 =
    (ridgeSupport546_suffix_010, ridgeSupport546_rest_010) := by rfl
theorem ridgeSupport546_suffix_decode_009 : PackedRawNatGrowth.readList 13 17 ridgeSupport546_rest_009 =
    (ridgeSupport546_suffix_009, ridgeSupport546_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 13 17 0
    ridgeSupport546_rest_009 ridgeSupport546_rest_010 ridgeSupport546_rest_010
    ridgeSupport546_009 ridgeSupport546_suffix_010 ridgeSupport546_009_decode ridgeSupport546_suffix_decode_010
theorem ridgeSupport546_suffix_decode_008 : PackedRawNatGrowth.readList 13 49 ridgeSupport546_rest_008 =
    (ridgeSupport546_suffix_008, ridgeSupport546_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 17
    ridgeSupport546_rest_008 ridgeSupport546_rest_009 ridgeSupport546_rest_010
    ridgeSupport546_008 ridgeSupport546_suffix_009 ridgeSupport546_008_decode ridgeSupport546_suffix_decode_009
theorem ridgeSupport546_suffix_decode_007 : PackedRawNatGrowth.readList 13 81 ridgeSupport546_rest_007 =
    (ridgeSupport546_suffix_007, ridgeSupport546_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 49
    ridgeSupport546_rest_007 ridgeSupport546_rest_008 ridgeSupport546_rest_010
    ridgeSupport546_007 ridgeSupport546_suffix_008 ridgeSupport546_007_decode ridgeSupport546_suffix_decode_008
theorem ridgeSupport546_suffix_decode_006 : PackedRawNatGrowth.readList 13 113 ridgeSupport546_rest_006 =
    (ridgeSupport546_suffix_006, ridgeSupport546_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 81
    ridgeSupport546_rest_006 ridgeSupport546_rest_007 ridgeSupport546_rest_010
    ridgeSupport546_006 ridgeSupport546_suffix_007 ridgeSupport546_006_decode ridgeSupport546_suffix_decode_007
theorem ridgeSupport546_suffix_decode_005 : PackedRawNatGrowth.readList 13 145 ridgeSupport546_rest_005 =
    (ridgeSupport546_suffix_005, ridgeSupport546_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 113
    ridgeSupport546_rest_005 ridgeSupport546_rest_006 ridgeSupport546_rest_010
    ridgeSupport546_005 ridgeSupport546_suffix_006 ridgeSupport546_005_decode ridgeSupport546_suffix_decode_006
theorem ridgeSupport546_suffix_decode_004 : PackedRawNatGrowth.readList 13 177 ridgeSupport546_rest_004 =
    (ridgeSupport546_suffix_004, ridgeSupport546_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 145
    ridgeSupport546_rest_004 ridgeSupport546_rest_005 ridgeSupport546_rest_010
    ridgeSupport546_004 ridgeSupport546_suffix_005 ridgeSupport546_004_decode ridgeSupport546_suffix_decode_005
theorem ridgeSupport546_suffix_decode_003 : PackedRawNatGrowth.readList 13 209 ridgeSupport546_rest_003 =
    (ridgeSupport546_suffix_003, ridgeSupport546_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 177
    ridgeSupport546_rest_003 ridgeSupport546_rest_004 ridgeSupport546_rest_010
    ridgeSupport546_003 ridgeSupport546_suffix_004 ridgeSupport546_003_decode ridgeSupport546_suffix_decode_004
theorem ridgeSupport546_suffix_decode_002 : PackedRawNatGrowth.readList 13 241 ridgeSupport546_rest_002 =
    (ridgeSupport546_suffix_002, ridgeSupport546_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 209
    ridgeSupport546_rest_002 ridgeSupport546_rest_003 ridgeSupport546_rest_010
    ridgeSupport546_002 ridgeSupport546_suffix_003 ridgeSupport546_002_decode ridgeSupport546_suffix_decode_003
theorem ridgeSupport546_suffix_decode_001 : PackedRawNatGrowth.readList 13 273 ridgeSupport546_rest_001 =
    (ridgeSupport546_suffix_001, ridgeSupport546_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 241
    ridgeSupport546_rest_001 ridgeSupport546_rest_002 ridgeSupport546_rest_010
    ridgeSupport546_001 ridgeSupport546_suffix_002 ridgeSupport546_001_decode ridgeSupport546_suffix_decode_002
theorem ridgeSupport546_suffix_decode_000 : PackedRawNatGrowth.readList 13 305 ridgeSupport546_rest_000 =
    (ridgeSupport546_suffix_000, ridgeSupport546_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 273
    ridgeSupport546_rest_000 ridgeSupport546_rest_001 ridgeSupport546_rest_010
    ridgeSupport546_000 ridgeSupport546_suffix_001 ridgeSupport546_000_decode ridgeSupport546_suffix_decode_001
theorem ridgeSupport546_eq : candidateRows 546 = ridgeSupport546_suffix_000 := by
  change candidateSupports 546 = ridgeSupport546_suffix_000
  rw [ridgeSupport546_source]
  exact congrArg Prod.fst ridgeSupport546_suffix_decode_000
theorem ridgeTest_large_546 : ridgeTest 546 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport546_eq]
    simp only [ridgeSupport546_suffix_000, ridgeSupport546_suffix_001, ridgeSupport546_suffix_002, ridgeSupport546_suffix_003, ridgeSupport546_suffix_004, ridgeSupport546_suffix_005, ridgeSupport546_suffix_006, ridgeSupport546_suffix_007, ridgeSupport546_suffix_008, ridgeSupport546_suffix_009, ridgeSupport546_suffix_010, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport546_000_mask, ridgeSupport546_001_mask, ridgeSupport546_002_mask, ridgeSupport546_003_mask, ridgeSupport546_004_mask, ridgeSupport546_005_mask, ridgeSupport546_006_mask, ridgeSupport546_007_mask, ridgeSupport546_008_mask, ridgeSupport546_009_mask]
    decide +kernel
  · rw [ridgeSupport546_eq]
    simp only [ridgeSupport546_suffix_000, ridgeSupport546_suffix_001, ridgeSupport546_suffix_002, ridgeSupport546_suffix_003, ridgeSupport546_suffix_004, ridgeSupport546_suffix_005, ridgeSupport546_suffix_006, ridgeSupport546_suffix_007, ridgeSupport546_suffix_008, ridgeSupport546_suffix_009, ridgeSupport546_suffix_010, List.all_append, List.all_nil, ridgeSupport546_000_checked, ridgeSupport546_001_checked, ridgeSupport546_002_checked, ridgeSupport546_003_checked, ridgeSupport546_004_checked, ridgeSupport546_005_checked, ridgeSupport546_006_checked, ridgeSupport546_007_checked, ridgeSupport546_008_checked, ridgeSupport546_009_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase02
