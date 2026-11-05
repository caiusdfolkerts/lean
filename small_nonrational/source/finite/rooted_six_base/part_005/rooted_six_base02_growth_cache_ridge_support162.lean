module
prelude
public import RootedSixBase02GrowthCacheRidgeSupport162Part000
public import RootedSixBase02GrowthCacheRidgeSupport162Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase02
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport162_suffix_decode_010 : PackedRawNatGrowth.readList 13 0 ridgeSupport162_rest_010 =
    (ridgeSupport162_suffix_010, ridgeSupport162_rest_010) := by rfl
theorem ridgeSupport162_suffix_decode_009 : PackedRawNatGrowth.readList 13 17 ridgeSupport162_rest_009 =
    (ridgeSupport162_suffix_009, ridgeSupport162_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 13 17 0
    ridgeSupport162_rest_009 ridgeSupport162_rest_010 ridgeSupport162_rest_010
    ridgeSupport162_009 ridgeSupport162_suffix_010 ridgeSupport162_009_decode ridgeSupport162_suffix_decode_010
theorem ridgeSupport162_suffix_decode_008 : PackedRawNatGrowth.readList 13 49 ridgeSupport162_rest_008 =
    (ridgeSupport162_suffix_008, ridgeSupport162_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 17
    ridgeSupport162_rest_008 ridgeSupport162_rest_009 ridgeSupport162_rest_010
    ridgeSupport162_008 ridgeSupport162_suffix_009 ridgeSupport162_008_decode ridgeSupport162_suffix_decode_009
theorem ridgeSupport162_suffix_decode_007 : PackedRawNatGrowth.readList 13 81 ridgeSupport162_rest_007 =
    (ridgeSupport162_suffix_007, ridgeSupport162_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 49
    ridgeSupport162_rest_007 ridgeSupport162_rest_008 ridgeSupport162_rest_010
    ridgeSupport162_007 ridgeSupport162_suffix_008 ridgeSupport162_007_decode ridgeSupport162_suffix_decode_008
theorem ridgeSupport162_suffix_decode_006 : PackedRawNatGrowth.readList 13 113 ridgeSupport162_rest_006 =
    (ridgeSupport162_suffix_006, ridgeSupport162_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 81
    ridgeSupport162_rest_006 ridgeSupport162_rest_007 ridgeSupport162_rest_010
    ridgeSupport162_006 ridgeSupport162_suffix_007 ridgeSupport162_006_decode ridgeSupport162_suffix_decode_007
theorem ridgeSupport162_suffix_decode_005 : PackedRawNatGrowth.readList 13 145 ridgeSupport162_rest_005 =
    (ridgeSupport162_suffix_005, ridgeSupport162_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 113
    ridgeSupport162_rest_005 ridgeSupport162_rest_006 ridgeSupport162_rest_010
    ridgeSupport162_005 ridgeSupport162_suffix_006 ridgeSupport162_005_decode ridgeSupport162_suffix_decode_006
theorem ridgeSupport162_suffix_decode_004 : PackedRawNatGrowth.readList 13 177 ridgeSupport162_rest_004 =
    (ridgeSupport162_suffix_004, ridgeSupport162_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 145
    ridgeSupport162_rest_004 ridgeSupport162_rest_005 ridgeSupport162_rest_010
    ridgeSupport162_004 ridgeSupport162_suffix_005 ridgeSupport162_004_decode ridgeSupport162_suffix_decode_005
theorem ridgeSupport162_suffix_decode_003 : PackedRawNatGrowth.readList 13 209 ridgeSupport162_rest_003 =
    (ridgeSupport162_suffix_003, ridgeSupport162_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 177
    ridgeSupport162_rest_003 ridgeSupport162_rest_004 ridgeSupport162_rest_010
    ridgeSupport162_003 ridgeSupport162_suffix_004 ridgeSupport162_003_decode ridgeSupport162_suffix_decode_004
theorem ridgeSupport162_suffix_decode_002 : PackedRawNatGrowth.readList 13 241 ridgeSupport162_rest_002 =
    (ridgeSupport162_suffix_002, ridgeSupport162_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 209
    ridgeSupport162_rest_002 ridgeSupport162_rest_003 ridgeSupport162_rest_010
    ridgeSupport162_002 ridgeSupport162_suffix_003 ridgeSupport162_002_decode ridgeSupport162_suffix_decode_003
theorem ridgeSupport162_suffix_decode_001 : PackedRawNatGrowth.readList 13 273 ridgeSupport162_rest_001 =
    (ridgeSupport162_suffix_001, ridgeSupport162_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 241
    ridgeSupport162_rest_001 ridgeSupport162_rest_002 ridgeSupport162_rest_010
    ridgeSupport162_001 ridgeSupport162_suffix_002 ridgeSupport162_001_decode ridgeSupport162_suffix_decode_002
theorem ridgeSupport162_suffix_decode_000 : PackedRawNatGrowth.readList 13 305 ridgeSupport162_rest_000 =
    (ridgeSupport162_suffix_000, ridgeSupport162_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 273
    ridgeSupport162_rest_000 ridgeSupport162_rest_001 ridgeSupport162_rest_010
    ridgeSupport162_000 ridgeSupport162_suffix_001 ridgeSupport162_000_decode ridgeSupport162_suffix_decode_001
theorem ridgeSupport162_eq : candidateRows 162 = ridgeSupport162_suffix_000 := by
  change candidateSupports 162 = ridgeSupport162_suffix_000
  rw [ridgeSupport162_source]
  exact congrArg Prod.fst ridgeSupport162_suffix_decode_000
theorem ridgeTest_large_162 : ridgeTest 162 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport162_eq]
    simp only [ridgeSupport162_suffix_000, ridgeSupport162_suffix_001, ridgeSupport162_suffix_002, ridgeSupport162_suffix_003, ridgeSupport162_suffix_004, ridgeSupport162_suffix_005, ridgeSupport162_suffix_006, ridgeSupport162_suffix_007, ridgeSupport162_suffix_008, ridgeSupport162_suffix_009, ridgeSupport162_suffix_010, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport162_000_mask, ridgeSupport162_001_mask, ridgeSupport162_002_mask, ridgeSupport162_003_mask, ridgeSupport162_004_mask, ridgeSupport162_005_mask, ridgeSupport162_006_mask, ridgeSupport162_007_mask, ridgeSupport162_008_mask, ridgeSupport162_009_mask]
    decide +kernel
  · rw [ridgeSupport162_eq]
    simp only [ridgeSupport162_suffix_000, ridgeSupport162_suffix_001, ridgeSupport162_suffix_002, ridgeSupport162_suffix_003, ridgeSupport162_suffix_004, ridgeSupport162_suffix_005, ridgeSupport162_suffix_006, ridgeSupport162_suffix_007, ridgeSupport162_suffix_008, ridgeSupport162_suffix_009, ridgeSupport162_suffix_010, List.all_append, List.all_nil, ridgeSupport162_000_checked, ridgeSupport162_001_checked, ridgeSupport162_002_checked, ridgeSupport162_003_checked, ridgeSupport162_004_checked, ridgeSupport162_005_checked, ridgeSupport162_006_checked, ridgeSupport162_007_checked, ridgeSupport162_008_checked, ridgeSupport162_009_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase02
