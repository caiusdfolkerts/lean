module
prelude
public import RootedSixBase02GrowthCacheRidgeSupport70Part000
public import RootedSixBase02GrowthCacheRidgeSupport70Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase02
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport70_suffix_decode_010 : PackedRawNatGrowth.readList 13 0 ridgeSupport70_rest_010 =
    (ridgeSupport70_suffix_010, ridgeSupport70_rest_010) := by rfl
theorem ridgeSupport70_suffix_decode_009 : PackedRawNatGrowth.readList 13 17 ridgeSupport70_rest_009 =
    (ridgeSupport70_suffix_009, ridgeSupport70_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 13 17 0
    ridgeSupport70_rest_009 ridgeSupport70_rest_010 ridgeSupport70_rest_010
    ridgeSupport70_009 ridgeSupport70_suffix_010 ridgeSupport70_009_decode ridgeSupport70_suffix_decode_010
theorem ridgeSupport70_suffix_decode_008 : PackedRawNatGrowth.readList 13 49 ridgeSupport70_rest_008 =
    (ridgeSupport70_suffix_008, ridgeSupport70_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 17
    ridgeSupport70_rest_008 ridgeSupport70_rest_009 ridgeSupport70_rest_010
    ridgeSupport70_008 ridgeSupport70_suffix_009 ridgeSupport70_008_decode ridgeSupport70_suffix_decode_009
theorem ridgeSupport70_suffix_decode_007 : PackedRawNatGrowth.readList 13 81 ridgeSupport70_rest_007 =
    (ridgeSupport70_suffix_007, ridgeSupport70_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 49
    ridgeSupport70_rest_007 ridgeSupport70_rest_008 ridgeSupport70_rest_010
    ridgeSupport70_007 ridgeSupport70_suffix_008 ridgeSupport70_007_decode ridgeSupport70_suffix_decode_008
theorem ridgeSupport70_suffix_decode_006 : PackedRawNatGrowth.readList 13 113 ridgeSupport70_rest_006 =
    (ridgeSupport70_suffix_006, ridgeSupport70_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 81
    ridgeSupport70_rest_006 ridgeSupport70_rest_007 ridgeSupport70_rest_010
    ridgeSupport70_006 ridgeSupport70_suffix_007 ridgeSupport70_006_decode ridgeSupport70_suffix_decode_007
theorem ridgeSupport70_suffix_decode_005 : PackedRawNatGrowth.readList 13 145 ridgeSupport70_rest_005 =
    (ridgeSupport70_suffix_005, ridgeSupport70_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 113
    ridgeSupport70_rest_005 ridgeSupport70_rest_006 ridgeSupport70_rest_010
    ridgeSupport70_005 ridgeSupport70_suffix_006 ridgeSupport70_005_decode ridgeSupport70_suffix_decode_006
theorem ridgeSupport70_suffix_decode_004 : PackedRawNatGrowth.readList 13 177 ridgeSupport70_rest_004 =
    (ridgeSupport70_suffix_004, ridgeSupport70_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 145
    ridgeSupport70_rest_004 ridgeSupport70_rest_005 ridgeSupport70_rest_010
    ridgeSupport70_004 ridgeSupport70_suffix_005 ridgeSupport70_004_decode ridgeSupport70_suffix_decode_005
theorem ridgeSupport70_suffix_decode_003 : PackedRawNatGrowth.readList 13 209 ridgeSupport70_rest_003 =
    (ridgeSupport70_suffix_003, ridgeSupport70_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 177
    ridgeSupport70_rest_003 ridgeSupport70_rest_004 ridgeSupport70_rest_010
    ridgeSupport70_003 ridgeSupport70_suffix_004 ridgeSupport70_003_decode ridgeSupport70_suffix_decode_004
theorem ridgeSupport70_suffix_decode_002 : PackedRawNatGrowth.readList 13 241 ridgeSupport70_rest_002 =
    (ridgeSupport70_suffix_002, ridgeSupport70_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 209
    ridgeSupport70_rest_002 ridgeSupport70_rest_003 ridgeSupport70_rest_010
    ridgeSupport70_002 ridgeSupport70_suffix_003 ridgeSupport70_002_decode ridgeSupport70_suffix_decode_003
theorem ridgeSupport70_suffix_decode_001 : PackedRawNatGrowth.readList 13 273 ridgeSupport70_rest_001 =
    (ridgeSupport70_suffix_001, ridgeSupport70_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 241
    ridgeSupport70_rest_001 ridgeSupport70_rest_002 ridgeSupport70_rest_010
    ridgeSupport70_001 ridgeSupport70_suffix_002 ridgeSupport70_001_decode ridgeSupport70_suffix_decode_002
theorem ridgeSupport70_suffix_decode_000 : PackedRawNatGrowth.readList 13 305 ridgeSupport70_rest_000 =
    (ridgeSupport70_suffix_000, ridgeSupport70_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 273
    ridgeSupport70_rest_000 ridgeSupport70_rest_001 ridgeSupport70_rest_010
    ridgeSupport70_000 ridgeSupport70_suffix_001 ridgeSupport70_000_decode ridgeSupport70_suffix_decode_001
theorem ridgeSupport70_eq : candidateRows 70 = ridgeSupport70_suffix_000 := by
  change candidateSupports 70 = ridgeSupport70_suffix_000
  rw [ridgeSupport70_source]
  exact congrArg Prod.fst ridgeSupport70_suffix_decode_000
theorem ridgeTest_large_70 : ridgeTest 70 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport70_eq]
    simp only [ridgeSupport70_suffix_000, ridgeSupport70_suffix_001, ridgeSupport70_suffix_002, ridgeSupport70_suffix_003, ridgeSupport70_suffix_004, ridgeSupport70_suffix_005, ridgeSupport70_suffix_006, ridgeSupport70_suffix_007, ridgeSupport70_suffix_008, ridgeSupport70_suffix_009, ridgeSupport70_suffix_010, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport70_000_mask, ridgeSupport70_001_mask, ridgeSupport70_002_mask, ridgeSupport70_003_mask, ridgeSupport70_004_mask, ridgeSupport70_005_mask, ridgeSupport70_006_mask, ridgeSupport70_007_mask, ridgeSupport70_008_mask, ridgeSupport70_009_mask]
    decide +kernel
  · rw [ridgeSupport70_eq]
    simp only [ridgeSupport70_suffix_000, ridgeSupport70_suffix_001, ridgeSupport70_suffix_002, ridgeSupport70_suffix_003, ridgeSupport70_suffix_004, ridgeSupport70_suffix_005, ridgeSupport70_suffix_006, ridgeSupport70_suffix_007, ridgeSupport70_suffix_008, ridgeSupport70_suffix_009, ridgeSupport70_suffix_010, List.all_append, List.all_nil, ridgeSupport70_000_checked, ridgeSupport70_001_checked, ridgeSupport70_002_checked, ridgeSupport70_003_checked, ridgeSupport70_004_checked, ridgeSupport70_005_checked, ridgeSupport70_006_checked, ridgeSupport70_007_checked, ridgeSupport70_008_checked, ridgeSupport70_009_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase02
