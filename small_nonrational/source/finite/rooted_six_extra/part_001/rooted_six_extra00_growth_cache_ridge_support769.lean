module
prelude
public import RootedSixExtra00GrowthCacheRidgeSupport769Part000
public import RootedSixExtra00GrowthCacheRidgeSupport769Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra00
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport769_suffix_decode_010 : PackedRawNatGrowth.readList 14 0 ridgeSupport769_rest_010 =
    (ridgeSupport769_suffix_010, ridgeSupport769_rest_010) := by rfl
theorem ridgeSupport769_suffix_decode_009 : PackedRawNatGrowth.readList 14 17 ridgeSupport769_rest_009 =
    (ridgeSupport769_suffix_009, ridgeSupport769_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 14 17 0
    ridgeSupport769_rest_009 ridgeSupport769_rest_010 ridgeSupport769_rest_010
    ridgeSupport769_009 ridgeSupport769_suffix_010 ridgeSupport769_009_decode ridgeSupport769_suffix_decode_010
theorem ridgeSupport769_suffix_decode_008 : PackedRawNatGrowth.readList 14 49 ridgeSupport769_rest_008 =
    (ridgeSupport769_suffix_008, ridgeSupport769_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 17
    ridgeSupport769_rest_008 ridgeSupport769_rest_009 ridgeSupport769_rest_010
    ridgeSupport769_008 ridgeSupport769_suffix_009 ridgeSupport769_008_decode ridgeSupport769_suffix_decode_009
theorem ridgeSupport769_suffix_decode_007 : PackedRawNatGrowth.readList 14 81 ridgeSupport769_rest_007 =
    (ridgeSupport769_suffix_007, ridgeSupport769_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 49
    ridgeSupport769_rest_007 ridgeSupport769_rest_008 ridgeSupport769_rest_010
    ridgeSupport769_007 ridgeSupport769_suffix_008 ridgeSupport769_007_decode ridgeSupport769_suffix_decode_008
theorem ridgeSupport769_suffix_decode_006 : PackedRawNatGrowth.readList 14 113 ridgeSupport769_rest_006 =
    (ridgeSupport769_suffix_006, ridgeSupport769_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 81
    ridgeSupport769_rest_006 ridgeSupport769_rest_007 ridgeSupport769_rest_010
    ridgeSupport769_006 ridgeSupport769_suffix_007 ridgeSupport769_006_decode ridgeSupport769_suffix_decode_007
theorem ridgeSupport769_suffix_decode_005 : PackedRawNatGrowth.readList 14 145 ridgeSupport769_rest_005 =
    (ridgeSupport769_suffix_005, ridgeSupport769_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 113
    ridgeSupport769_rest_005 ridgeSupport769_rest_006 ridgeSupport769_rest_010
    ridgeSupport769_005 ridgeSupport769_suffix_006 ridgeSupport769_005_decode ridgeSupport769_suffix_decode_006
theorem ridgeSupport769_suffix_decode_004 : PackedRawNatGrowth.readList 14 177 ridgeSupport769_rest_004 =
    (ridgeSupport769_suffix_004, ridgeSupport769_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 145
    ridgeSupport769_rest_004 ridgeSupport769_rest_005 ridgeSupport769_rest_010
    ridgeSupport769_004 ridgeSupport769_suffix_005 ridgeSupport769_004_decode ridgeSupport769_suffix_decode_005
theorem ridgeSupport769_suffix_decode_003 : PackedRawNatGrowth.readList 14 209 ridgeSupport769_rest_003 =
    (ridgeSupport769_suffix_003, ridgeSupport769_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 177
    ridgeSupport769_rest_003 ridgeSupport769_rest_004 ridgeSupport769_rest_010
    ridgeSupport769_003 ridgeSupport769_suffix_004 ridgeSupport769_003_decode ridgeSupport769_suffix_decode_004
theorem ridgeSupport769_suffix_decode_002 : PackedRawNatGrowth.readList 14 241 ridgeSupport769_rest_002 =
    (ridgeSupport769_suffix_002, ridgeSupport769_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 209
    ridgeSupport769_rest_002 ridgeSupport769_rest_003 ridgeSupport769_rest_010
    ridgeSupport769_002 ridgeSupport769_suffix_003 ridgeSupport769_002_decode ridgeSupport769_suffix_decode_003
theorem ridgeSupport769_suffix_decode_001 : PackedRawNatGrowth.readList 14 273 ridgeSupport769_rest_001 =
    (ridgeSupport769_suffix_001, ridgeSupport769_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 241
    ridgeSupport769_rest_001 ridgeSupport769_rest_002 ridgeSupport769_rest_010
    ridgeSupport769_001 ridgeSupport769_suffix_002 ridgeSupport769_001_decode ridgeSupport769_suffix_decode_002
theorem ridgeSupport769_suffix_decode_000 : PackedRawNatGrowth.readList 14 305 ridgeSupport769_rest_000 =
    (ridgeSupport769_suffix_000, ridgeSupport769_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 273
    ridgeSupport769_rest_000 ridgeSupport769_rest_001 ridgeSupport769_rest_010
    ridgeSupport769_000 ridgeSupport769_suffix_001 ridgeSupport769_000_decode ridgeSupport769_suffix_decode_001
theorem ridgeSupport769_eq : candidateRows 769 = ridgeSupport769_suffix_000 := by
  change candidateSupports 769 = ridgeSupport769_suffix_000
  rw [ridgeSupport769_source]
  exact congrArg Prod.fst ridgeSupport769_suffix_decode_000
theorem ridgeTest_large_769 : ridgeTest 769 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport769_eq]
    simp only [ridgeSupport769_suffix_000, ridgeSupport769_suffix_001, ridgeSupport769_suffix_002, ridgeSupport769_suffix_003, ridgeSupport769_suffix_004, ridgeSupport769_suffix_005, ridgeSupport769_suffix_006, ridgeSupport769_suffix_007, ridgeSupport769_suffix_008, ridgeSupport769_suffix_009, ridgeSupport769_suffix_010, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport769_000_mask, ridgeSupport769_001_mask, ridgeSupport769_002_mask, ridgeSupport769_003_mask, ridgeSupport769_004_mask, ridgeSupport769_005_mask, ridgeSupport769_006_mask, ridgeSupport769_007_mask, ridgeSupport769_008_mask, ridgeSupport769_009_mask]
    decide +kernel
  · rw [ridgeSupport769_eq]
    simp only [ridgeSupport769_suffix_000, ridgeSupport769_suffix_001, ridgeSupport769_suffix_002, ridgeSupport769_suffix_003, ridgeSupport769_suffix_004, ridgeSupport769_suffix_005, ridgeSupport769_suffix_006, ridgeSupport769_suffix_007, ridgeSupport769_suffix_008, ridgeSupport769_suffix_009, ridgeSupport769_suffix_010, List.all_append, List.all_nil, ridgeSupport769_000_checked, ridgeSupport769_001_checked, ridgeSupport769_002_checked, ridgeSupport769_003_checked, ridgeSupport769_004_checked, ridgeSupport769_005_checked, ridgeSupport769_006_checked, ridgeSupport769_007_checked, ridgeSupport769_008_checked, ridgeSupport769_009_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixExtra00
