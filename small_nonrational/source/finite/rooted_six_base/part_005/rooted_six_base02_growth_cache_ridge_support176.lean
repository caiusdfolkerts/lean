module
prelude
public import RootedSixBase02GrowthCacheRidgeSupport176Part000
public import RootedSixBase02GrowthCacheRidgeSupport176Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase02
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport176_suffix_decode_010 : PackedRawNatGrowth.readList 13 0 ridgeSupport176_rest_010 =
    (ridgeSupport176_suffix_010, ridgeSupport176_rest_010) := by rfl
theorem ridgeSupport176_suffix_decode_009 : PackedRawNatGrowth.readList 13 17 ridgeSupport176_rest_009 =
    (ridgeSupport176_suffix_009, ridgeSupport176_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 13 17 0
    ridgeSupport176_rest_009 ridgeSupport176_rest_010 ridgeSupport176_rest_010
    ridgeSupport176_009 ridgeSupport176_suffix_010 ridgeSupport176_009_decode ridgeSupport176_suffix_decode_010
theorem ridgeSupport176_suffix_decode_008 : PackedRawNatGrowth.readList 13 49 ridgeSupport176_rest_008 =
    (ridgeSupport176_suffix_008, ridgeSupport176_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 17
    ridgeSupport176_rest_008 ridgeSupport176_rest_009 ridgeSupport176_rest_010
    ridgeSupport176_008 ridgeSupport176_suffix_009 ridgeSupport176_008_decode ridgeSupport176_suffix_decode_009
theorem ridgeSupport176_suffix_decode_007 : PackedRawNatGrowth.readList 13 81 ridgeSupport176_rest_007 =
    (ridgeSupport176_suffix_007, ridgeSupport176_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 49
    ridgeSupport176_rest_007 ridgeSupport176_rest_008 ridgeSupport176_rest_010
    ridgeSupport176_007 ridgeSupport176_suffix_008 ridgeSupport176_007_decode ridgeSupport176_suffix_decode_008
theorem ridgeSupport176_suffix_decode_006 : PackedRawNatGrowth.readList 13 113 ridgeSupport176_rest_006 =
    (ridgeSupport176_suffix_006, ridgeSupport176_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 81
    ridgeSupport176_rest_006 ridgeSupport176_rest_007 ridgeSupport176_rest_010
    ridgeSupport176_006 ridgeSupport176_suffix_007 ridgeSupport176_006_decode ridgeSupport176_suffix_decode_007
theorem ridgeSupport176_suffix_decode_005 : PackedRawNatGrowth.readList 13 145 ridgeSupport176_rest_005 =
    (ridgeSupport176_suffix_005, ridgeSupport176_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 113
    ridgeSupport176_rest_005 ridgeSupport176_rest_006 ridgeSupport176_rest_010
    ridgeSupport176_005 ridgeSupport176_suffix_006 ridgeSupport176_005_decode ridgeSupport176_suffix_decode_006
theorem ridgeSupport176_suffix_decode_004 : PackedRawNatGrowth.readList 13 177 ridgeSupport176_rest_004 =
    (ridgeSupport176_suffix_004, ridgeSupport176_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 145
    ridgeSupport176_rest_004 ridgeSupport176_rest_005 ridgeSupport176_rest_010
    ridgeSupport176_004 ridgeSupport176_suffix_005 ridgeSupport176_004_decode ridgeSupport176_suffix_decode_005
theorem ridgeSupport176_suffix_decode_003 : PackedRawNatGrowth.readList 13 209 ridgeSupport176_rest_003 =
    (ridgeSupport176_suffix_003, ridgeSupport176_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 177
    ridgeSupport176_rest_003 ridgeSupport176_rest_004 ridgeSupport176_rest_010
    ridgeSupport176_003 ridgeSupport176_suffix_004 ridgeSupport176_003_decode ridgeSupport176_suffix_decode_004
theorem ridgeSupport176_suffix_decode_002 : PackedRawNatGrowth.readList 13 241 ridgeSupport176_rest_002 =
    (ridgeSupport176_suffix_002, ridgeSupport176_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 209
    ridgeSupport176_rest_002 ridgeSupport176_rest_003 ridgeSupport176_rest_010
    ridgeSupport176_002 ridgeSupport176_suffix_003 ridgeSupport176_002_decode ridgeSupport176_suffix_decode_003
theorem ridgeSupport176_suffix_decode_001 : PackedRawNatGrowth.readList 13 273 ridgeSupport176_rest_001 =
    (ridgeSupport176_suffix_001, ridgeSupport176_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 241
    ridgeSupport176_rest_001 ridgeSupport176_rest_002 ridgeSupport176_rest_010
    ridgeSupport176_001 ridgeSupport176_suffix_002 ridgeSupport176_001_decode ridgeSupport176_suffix_decode_002
theorem ridgeSupport176_suffix_decode_000 : PackedRawNatGrowth.readList 13 305 ridgeSupport176_rest_000 =
    (ridgeSupport176_suffix_000, ridgeSupport176_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 273
    ridgeSupport176_rest_000 ridgeSupport176_rest_001 ridgeSupport176_rest_010
    ridgeSupport176_000 ridgeSupport176_suffix_001 ridgeSupport176_000_decode ridgeSupport176_suffix_decode_001
theorem ridgeSupport176_eq : candidateRows 176 = ridgeSupport176_suffix_000 := by
  change candidateSupports 176 = ridgeSupport176_suffix_000
  rw [ridgeSupport176_source]
  exact congrArg Prod.fst ridgeSupport176_suffix_decode_000
theorem ridgeTest_large_176 : ridgeTest 176 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport176_eq]
    simp only [ridgeSupport176_suffix_000, ridgeSupport176_suffix_001, ridgeSupport176_suffix_002, ridgeSupport176_suffix_003, ridgeSupport176_suffix_004, ridgeSupport176_suffix_005, ridgeSupport176_suffix_006, ridgeSupport176_suffix_007, ridgeSupport176_suffix_008, ridgeSupport176_suffix_009, ridgeSupport176_suffix_010, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport176_000_mask, ridgeSupport176_001_mask, ridgeSupport176_002_mask, ridgeSupport176_003_mask, ridgeSupport176_004_mask, ridgeSupport176_005_mask, ridgeSupport176_006_mask, ridgeSupport176_007_mask, ridgeSupport176_008_mask, ridgeSupport176_009_mask]
    decide +kernel
  · rw [ridgeSupport176_eq]
    simp only [ridgeSupport176_suffix_000, ridgeSupport176_suffix_001, ridgeSupport176_suffix_002, ridgeSupport176_suffix_003, ridgeSupport176_suffix_004, ridgeSupport176_suffix_005, ridgeSupport176_suffix_006, ridgeSupport176_suffix_007, ridgeSupport176_suffix_008, ridgeSupport176_suffix_009, ridgeSupport176_suffix_010, List.all_append, List.all_nil, ridgeSupport176_000_checked, ridgeSupport176_001_checked, ridgeSupport176_002_checked, ridgeSupport176_003_checked, ridgeSupport176_004_checked, ridgeSupport176_005_checked, ridgeSupport176_006_checked, ridgeSupport176_007_checked, ridgeSupport176_008_checked, ridgeSupport176_009_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase02
