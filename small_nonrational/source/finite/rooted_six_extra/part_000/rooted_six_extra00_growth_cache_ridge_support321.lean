module
prelude
public import RootedSixExtra00GrowthCacheRidgeSupport321Part000
public import RootedSixExtra00GrowthCacheRidgeSupport321Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra00
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport321_suffix_decode_010 : PackedRawNatGrowth.readList 14 0 ridgeSupport321_rest_010 =
    (ridgeSupport321_suffix_010, ridgeSupport321_rest_010) := by rfl
theorem ridgeSupport321_suffix_decode_009 : PackedRawNatGrowth.readList 14 17 ridgeSupport321_rest_009 =
    (ridgeSupport321_suffix_009, ridgeSupport321_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 14 17 0
    ridgeSupport321_rest_009 ridgeSupport321_rest_010 ridgeSupport321_rest_010
    ridgeSupport321_009 ridgeSupport321_suffix_010 ridgeSupport321_009_decode ridgeSupport321_suffix_decode_010
theorem ridgeSupport321_suffix_decode_008 : PackedRawNatGrowth.readList 14 49 ridgeSupport321_rest_008 =
    (ridgeSupport321_suffix_008, ridgeSupport321_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 17
    ridgeSupport321_rest_008 ridgeSupport321_rest_009 ridgeSupport321_rest_010
    ridgeSupport321_008 ridgeSupport321_suffix_009 ridgeSupport321_008_decode ridgeSupport321_suffix_decode_009
theorem ridgeSupport321_suffix_decode_007 : PackedRawNatGrowth.readList 14 81 ridgeSupport321_rest_007 =
    (ridgeSupport321_suffix_007, ridgeSupport321_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 49
    ridgeSupport321_rest_007 ridgeSupport321_rest_008 ridgeSupport321_rest_010
    ridgeSupport321_007 ridgeSupport321_suffix_008 ridgeSupport321_007_decode ridgeSupport321_suffix_decode_008
theorem ridgeSupport321_suffix_decode_006 : PackedRawNatGrowth.readList 14 113 ridgeSupport321_rest_006 =
    (ridgeSupport321_suffix_006, ridgeSupport321_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 81
    ridgeSupport321_rest_006 ridgeSupport321_rest_007 ridgeSupport321_rest_010
    ridgeSupport321_006 ridgeSupport321_suffix_007 ridgeSupport321_006_decode ridgeSupport321_suffix_decode_007
theorem ridgeSupport321_suffix_decode_005 : PackedRawNatGrowth.readList 14 145 ridgeSupport321_rest_005 =
    (ridgeSupport321_suffix_005, ridgeSupport321_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 113
    ridgeSupport321_rest_005 ridgeSupport321_rest_006 ridgeSupport321_rest_010
    ridgeSupport321_005 ridgeSupport321_suffix_006 ridgeSupport321_005_decode ridgeSupport321_suffix_decode_006
theorem ridgeSupport321_suffix_decode_004 : PackedRawNatGrowth.readList 14 177 ridgeSupport321_rest_004 =
    (ridgeSupport321_suffix_004, ridgeSupport321_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 145
    ridgeSupport321_rest_004 ridgeSupport321_rest_005 ridgeSupport321_rest_010
    ridgeSupport321_004 ridgeSupport321_suffix_005 ridgeSupport321_004_decode ridgeSupport321_suffix_decode_005
theorem ridgeSupport321_suffix_decode_003 : PackedRawNatGrowth.readList 14 209 ridgeSupport321_rest_003 =
    (ridgeSupport321_suffix_003, ridgeSupport321_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 177
    ridgeSupport321_rest_003 ridgeSupport321_rest_004 ridgeSupport321_rest_010
    ridgeSupport321_003 ridgeSupport321_suffix_004 ridgeSupport321_003_decode ridgeSupport321_suffix_decode_004
theorem ridgeSupport321_suffix_decode_002 : PackedRawNatGrowth.readList 14 241 ridgeSupport321_rest_002 =
    (ridgeSupport321_suffix_002, ridgeSupport321_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 209
    ridgeSupport321_rest_002 ridgeSupport321_rest_003 ridgeSupport321_rest_010
    ridgeSupport321_002 ridgeSupport321_suffix_003 ridgeSupport321_002_decode ridgeSupport321_suffix_decode_003
theorem ridgeSupport321_suffix_decode_001 : PackedRawNatGrowth.readList 14 273 ridgeSupport321_rest_001 =
    (ridgeSupport321_suffix_001, ridgeSupport321_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 241
    ridgeSupport321_rest_001 ridgeSupport321_rest_002 ridgeSupport321_rest_010
    ridgeSupport321_001 ridgeSupport321_suffix_002 ridgeSupport321_001_decode ridgeSupport321_suffix_decode_002
theorem ridgeSupport321_suffix_decode_000 : PackedRawNatGrowth.readList 14 305 ridgeSupport321_rest_000 =
    (ridgeSupport321_suffix_000, ridgeSupport321_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 273
    ridgeSupport321_rest_000 ridgeSupport321_rest_001 ridgeSupport321_rest_010
    ridgeSupport321_000 ridgeSupport321_suffix_001 ridgeSupport321_000_decode ridgeSupport321_suffix_decode_001
theorem ridgeSupport321_eq : candidateRows 321 = ridgeSupport321_suffix_000 := by
  change candidateSupports 321 = ridgeSupport321_suffix_000
  rw [ridgeSupport321_source]
  exact congrArg Prod.fst ridgeSupport321_suffix_decode_000
theorem ridgeTest_large_321 : ridgeTest 321 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport321_eq]
    simp only [ridgeSupport321_suffix_000, ridgeSupport321_suffix_001, ridgeSupport321_suffix_002, ridgeSupport321_suffix_003, ridgeSupport321_suffix_004, ridgeSupport321_suffix_005, ridgeSupport321_suffix_006, ridgeSupport321_suffix_007, ridgeSupport321_suffix_008, ridgeSupport321_suffix_009, ridgeSupport321_suffix_010, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport321_000_mask, ridgeSupport321_001_mask, ridgeSupport321_002_mask, ridgeSupport321_003_mask, ridgeSupport321_004_mask, ridgeSupport321_005_mask, ridgeSupport321_006_mask, ridgeSupport321_007_mask, ridgeSupport321_008_mask, ridgeSupport321_009_mask]
    decide +kernel
  · rw [ridgeSupport321_eq]
    simp only [ridgeSupport321_suffix_000, ridgeSupport321_suffix_001, ridgeSupport321_suffix_002, ridgeSupport321_suffix_003, ridgeSupport321_suffix_004, ridgeSupport321_suffix_005, ridgeSupport321_suffix_006, ridgeSupport321_suffix_007, ridgeSupport321_suffix_008, ridgeSupport321_suffix_009, ridgeSupport321_suffix_010, List.all_append, List.all_nil, ridgeSupport321_000_checked, ridgeSupport321_001_checked, ridgeSupport321_002_checked, ridgeSupport321_003_checked, ridgeSupport321_004_checked, ridgeSupport321_005_checked, ridgeSupport321_006_checked, ridgeSupport321_007_checked, ridgeSupport321_008_checked, ridgeSupport321_009_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixExtra00
