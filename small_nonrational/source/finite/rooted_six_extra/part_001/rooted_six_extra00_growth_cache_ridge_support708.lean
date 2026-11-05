module
prelude
public import RootedSixExtra00GrowthCacheRidgeSupport708Part000
public import RootedSixExtra00GrowthCacheRidgeSupport708Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra00
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport708_suffix_decode_009 : PackedRawNatGrowth.readList 14 0 ridgeSupport708_rest_009 =
    (ridgeSupport708_suffix_009, ridgeSupport708_rest_009) := by rfl
theorem ridgeSupport708_suffix_decode_008 : PackedRawNatGrowth.readList 14 2 ridgeSupport708_rest_008 =
    (ridgeSupport708_suffix_008, ridgeSupport708_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 2 0
    ridgeSupport708_rest_008 ridgeSupport708_rest_009 ridgeSupport708_rest_009
    ridgeSupport708_008 ridgeSupport708_suffix_009 ridgeSupport708_008_decode ridgeSupport708_suffix_decode_009
theorem ridgeSupport708_suffix_decode_007 : PackedRawNatGrowth.readList 14 34 ridgeSupport708_rest_007 =
    (ridgeSupport708_suffix_007, ridgeSupport708_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 2
    ridgeSupport708_rest_007 ridgeSupport708_rest_008 ridgeSupport708_rest_009
    ridgeSupport708_007 ridgeSupport708_suffix_008 ridgeSupport708_007_decode ridgeSupport708_suffix_decode_008
theorem ridgeSupport708_suffix_decode_006 : PackedRawNatGrowth.readList 14 66 ridgeSupport708_rest_006 =
    (ridgeSupport708_suffix_006, ridgeSupport708_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 34
    ridgeSupport708_rest_006 ridgeSupport708_rest_007 ridgeSupport708_rest_009
    ridgeSupport708_006 ridgeSupport708_suffix_007 ridgeSupport708_006_decode ridgeSupport708_suffix_decode_007
theorem ridgeSupport708_suffix_decode_005 : PackedRawNatGrowth.readList 14 98 ridgeSupport708_rest_005 =
    (ridgeSupport708_suffix_005, ridgeSupport708_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 66
    ridgeSupport708_rest_005 ridgeSupport708_rest_006 ridgeSupport708_rest_009
    ridgeSupport708_005 ridgeSupport708_suffix_006 ridgeSupport708_005_decode ridgeSupport708_suffix_decode_006
theorem ridgeSupport708_suffix_decode_004 : PackedRawNatGrowth.readList 14 130 ridgeSupport708_rest_004 =
    (ridgeSupport708_suffix_004, ridgeSupport708_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 98
    ridgeSupport708_rest_004 ridgeSupport708_rest_005 ridgeSupport708_rest_009
    ridgeSupport708_004 ridgeSupport708_suffix_005 ridgeSupport708_004_decode ridgeSupport708_suffix_decode_005
theorem ridgeSupport708_suffix_decode_003 : PackedRawNatGrowth.readList 14 162 ridgeSupport708_rest_003 =
    (ridgeSupport708_suffix_003, ridgeSupport708_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 130
    ridgeSupport708_rest_003 ridgeSupport708_rest_004 ridgeSupport708_rest_009
    ridgeSupport708_003 ridgeSupport708_suffix_004 ridgeSupport708_003_decode ridgeSupport708_suffix_decode_004
theorem ridgeSupport708_suffix_decode_002 : PackedRawNatGrowth.readList 14 194 ridgeSupport708_rest_002 =
    (ridgeSupport708_suffix_002, ridgeSupport708_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 162
    ridgeSupport708_rest_002 ridgeSupport708_rest_003 ridgeSupport708_rest_009
    ridgeSupport708_002 ridgeSupport708_suffix_003 ridgeSupport708_002_decode ridgeSupport708_suffix_decode_003
theorem ridgeSupport708_suffix_decode_001 : PackedRawNatGrowth.readList 14 226 ridgeSupport708_rest_001 =
    (ridgeSupport708_suffix_001, ridgeSupport708_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 194
    ridgeSupport708_rest_001 ridgeSupport708_rest_002 ridgeSupport708_rest_009
    ridgeSupport708_001 ridgeSupport708_suffix_002 ridgeSupport708_001_decode ridgeSupport708_suffix_decode_002
theorem ridgeSupport708_suffix_decode_000 : PackedRawNatGrowth.readList 14 258 ridgeSupport708_rest_000 =
    (ridgeSupport708_suffix_000, ridgeSupport708_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 226
    ridgeSupport708_rest_000 ridgeSupport708_rest_001 ridgeSupport708_rest_009
    ridgeSupport708_000 ridgeSupport708_suffix_001 ridgeSupport708_000_decode ridgeSupport708_suffix_decode_001
theorem ridgeSupport708_eq : candidateRows 708 = ridgeSupport708_suffix_000 := by
  change candidateSupports 708 = ridgeSupport708_suffix_000
  rw [ridgeSupport708_source]
  exact congrArg Prod.fst ridgeSupport708_suffix_decode_000
theorem ridgeTest_large_708 : ridgeTest 708 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport708_eq]
    simp only [ridgeSupport708_suffix_000, ridgeSupport708_suffix_001, ridgeSupport708_suffix_002, ridgeSupport708_suffix_003, ridgeSupport708_suffix_004, ridgeSupport708_suffix_005, ridgeSupport708_suffix_006, ridgeSupport708_suffix_007, ridgeSupport708_suffix_008, ridgeSupport708_suffix_009, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport708_000_mask, ridgeSupport708_001_mask, ridgeSupport708_002_mask, ridgeSupport708_003_mask, ridgeSupport708_004_mask, ridgeSupport708_005_mask, ridgeSupport708_006_mask, ridgeSupport708_007_mask, ridgeSupport708_008_mask]
    decide +kernel
  · rw [ridgeSupport708_eq]
    simp only [ridgeSupport708_suffix_000, ridgeSupport708_suffix_001, ridgeSupport708_suffix_002, ridgeSupport708_suffix_003, ridgeSupport708_suffix_004, ridgeSupport708_suffix_005, ridgeSupport708_suffix_006, ridgeSupport708_suffix_007, ridgeSupport708_suffix_008, ridgeSupport708_suffix_009, List.all_append, List.all_nil, ridgeSupport708_000_checked, ridgeSupport708_001_checked, ridgeSupport708_002_checked, ridgeSupport708_003_checked, ridgeSupport708_004_checked, ridgeSupport708_005_checked, ridgeSupport708_006_checked, ridgeSupport708_007_checked, ridgeSupport708_008_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixExtra00
