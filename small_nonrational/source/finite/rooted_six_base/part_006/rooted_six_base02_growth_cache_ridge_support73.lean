module
prelude
public import RootedSixBase02GrowthCacheRidgeSupport73Part000
public import RootedSixBase02GrowthCacheRidgeSupport73Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase02
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport73_suffix_decode_010 : PackedRawNatGrowth.readList 13 0 ridgeSupport73_rest_010 =
    (ridgeSupport73_suffix_010, ridgeSupport73_rest_010) := by rfl
theorem ridgeSupport73_suffix_decode_009 : PackedRawNatGrowth.readList 13 17 ridgeSupport73_rest_009 =
    (ridgeSupport73_suffix_009, ridgeSupport73_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 13 17 0
    ridgeSupport73_rest_009 ridgeSupport73_rest_010 ridgeSupport73_rest_010
    ridgeSupport73_009 ridgeSupport73_suffix_010 ridgeSupport73_009_decode ridgeSupport73_suffix_decode_010
theorem ridgeSupport73_suffix_decode_008 : PackedRawNatGrowth.readList 13 49 ridgeSupport73_rest_008 =
    (ridgeSupport73_suffix_008, ridgeSupport73_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 17
    ridgeSupport73_rest_008 ridgeSupport73_rest_009 ridgeSupport73_rest_010
    ridgeSupport73_008 ridgeSupport73_suffix_009 ridgeSupport73_008_decode ridgeSupport73_suffix_decode_009
theorem ridgeSupport73_suffix_decode_007 : PackedRawNatGrowth.readList 13 81 ridgeSupport73_rest_007 =
    (ridgeSupport73_suffix_007, ridgeSupport73_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 49
    ridgeSupport73_rest_007 ridgeSupport73_rest_008 ridgeSupport73_rest_010
    ridgeSupport73_007 ridgeSupport73_suffix_008 ridgeSupport73_007_decode ridgeSupport73_suffix_decode_008
theorem ridgeSupport73_suffix_decode_006 : PackedRawNatGrowth.readList 13 113 ridgeSupport73_rest_006 =
    (ridgeSupport73_suffix_006, ridgeSupport73_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 81
    ridgeSupport73_rest_006 ridgeSupport73_rest_007 ridgeSupport73_rest_010
    ridgeSupport73_006 ridgeSupport73_suffix_007 ridgeSupport73_006_decode ridgeSupport73_suffix_decode_007
theorem ridgeSupport73_suffix_decode_005 : PackedRawNatGrowth.readList 13 145 ridgeSupport73_rest_005 =
    (ridgeSupport73_suffix_005, ridgeSupport73_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 113
    ridgeSupport73_rest_005 ridgeSupport73_rest_006 ridgeSupport73_rest_010
    ridgeSupport73_005 ridgeSupport73_suffix_006 ridgeSupport73_005_decode ridgeSupport73_suffix_decode_006
theorem ridgeSupport73_suffix_decode_004 : PackedRawNatGrowth.readList 13 177 ridgeSupport73_rest_004 =
    (ridgeSupport73_suffix_004, ridgeSupport73_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 145
    ridgeSupport73_rest_004 ridgeSupport73_rest_005 ridgeSupport73_rest_010
    ridgeSupport73_004 ridgeSupport73_suffix_005 ridgeSupport73_004_decode ridgeSupport73_suffix_decode_005
theorem ridgeSupport73_suffix_decode_003 : PackedRawNatGrowth.readList 13 209 ridgeSupport73_rest_003 =
    (ridgeSupport73_suffix_003, ridgeSupport73_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 177
    ridgeSupport73_rest_003 ridgeSupport73_rest_004 ridgeSupport73_rest_010
    ridgeSupport73_003 ridgeSupport73_suffix_004 ridgeSupport73_003_decode ridgeSupport73_suffix_decode_004
theorem ridgeSupport73_suffix_decode_002 : PackedRawNatGrowth.readList 13 241 ridgeSupport73_rest_002 =
    (ridgeSupport73_suffix_002, ridgeSupport73_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 209
    ridgeSupport73_rest_002 ridgeSupport73_rest_003 ridgeSupport73_rest_010
    ridgeSupport73_002 ridgeSupport73_suffix_003 ridgeSupport73_002_decode ridgeSupport73_suffix_decode_003
theorem ridgeSupport73_suffix_decode_001 : PackedRawNatGrowth.readList 13 273 ridgeSupport73_rest_001 =
    (ridgeSupport73_suffix_001, ridgeSupport73_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 241
    ridgeSupport73_rest_001 ridgeSupport73_rest_002 ridgeSupport73_rest_010
    ridgeSupport73_001 ridgeSupport73_suffix_002 ridgeSupport73_001_decode ridgeSupport73_suffix_decode_002
theorem ridgeSupport73_suffix_decode_000 : PackedRawNatGrowth.readList 13 305 ridgeSupport73_rest_000 =
    (ridgeSupport73_suffix_000, ridgeSupport73_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 273
    ridgeSupport73_rest_000 ridgeSupport73_rest_001 ridgeSupport73_rest_010
    ridgeSupport73_000 ridgeSupport73_suffix_001 ridgeSupport73_000_decode ridgeSupport73_suffix_decode_001
theorem ridgeSupport73_eq : candidateRows 73 = ridgeSupport73_suffix_000 := by
  change candidateSupports 73 = ridgeSupport73_suffix_000
  rw [ridgeSupport73_source]
  exact congrArg Prod.fst ridgeSupport73_suffix_decode_000
theorem ridgeTest_large_73 : ridgeTest 73 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport73_eq]
    simp only [ridgeSupport73_suffix_000, ridgeSupport73_suffix_001, ridgeSupport73_suffix_002, ridgeSupport73_suffix_003, ridgeSupport73_suffix_004, ridgeSupport73_suffix_005, ridgeSupport73_suffix_006, ridgeSupport73_suffix_007, ridgeSupport73_suffix_008, ridgeSupport73_suffix_009, ridgeSupport73_suffix_010, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport73_000_mask, ridgeSupport73_001_mask, ridgeSupport73_002_mask, ridgeSupport73_003_mask, ridgeSupport73_004_mask, ridgeSupport73_005_mask, ridgeSupport73_006_mask, ridgeSupport73_007_mask, ridgeSupport73_008_mask, ridgeSupport73_009_mask]
    decide +kernel
  · rw [ridgeSupport73_eq]
    simp only [ridgeSupport73_suffix_000, ridgeSupport73_suffix_001, ridgeSupport73_suffix_002, ridgeSupport73_suffix_003, ridgeSupport73_suffix_004, ridgeSupport73_suffix_005, ridgeSupport73_suffix_006, ridgeSupport73_suffix_007, ridgeSupport73_suffix_008, ridgeSupport73_suffix_009, ridgeSupport73_suffix_010, List.all_append, List.all_nil, ridgeSupport73_000_checked, ridgeSupport73_001_checked, ridgeSupport73_002_checked, ridgeSupport73_003_checked, ridgeSupport73_004_checked, ridgeSupport73_005_checked, ridgeSupport73_006_checked, ridgeSupport73_007_checked, ridgeSupport73_008_checked, ridgeSupport73_009_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase02
