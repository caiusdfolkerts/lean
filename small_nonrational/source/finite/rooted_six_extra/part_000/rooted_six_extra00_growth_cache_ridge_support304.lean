module
prelude
public import RootedSixExtra00GrowthCacheRidgeSupport304Part000
public import RootedSixExtra00GrowthCacheRidgeSupport304Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra00
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport304_suffix_decode_009 : PackedRawNatGrowth.readList 14 0 ridgeSupport304_rest_009 =
    (ridgeSupport304_suffix_009, ridgeSupport304_rest_009) := by rfl
theorem ridgeSupport304_suffix_decode_008 : PackedRawNatGrowth.readList 14 7 ridgeSupport304_rest_008 =
    (ridgeSupport304_suffix_008, ridgeSupport304_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 7 0
    ridgeSupport304_rest_008 ridgeSupport304_rest_009 ridgeSupport304_rest_009
    ridgeSupport304_008 ridgeSupport304_suffix_009 ridgeSupport304_008_decode ridgeSupport304_suffix_decode_009
theorem ridgeSupport304_suffix_decode_007 : PackedRawNatGrowth.readList 14 39 ridgeSupport304_rest_007 =
    (ridgeSupport304_suffix_007, ridgeSupport304_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 7
    ridgeSupport304_rest_007 ridgeSupport304_rest_008 ridgeSupport304_rest_009
    ridgeSupport304_007 ridgeSupport304_suffix_008 ridgeSupport304_007_decode ridgeSupport304_suffix_decode_008
theorem ridgeSupport304_suffix_decode_006 : PackedRawNatGrowth.readList 14 71 ridgeSupport304_rest_006 =
    (ridgeSupport304_suffix_006, ridgeSupport304_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 39
    ridgeSupport304_rest_006 ridgeSupport304_rest_007 ridgeSupport304_rest_009
    ridgeSupport304_006 ridgeSupport304_suffix_007 ridgeSupport304_006_decode ridgeSupport304_suffix_decode_007
theorem ridgeSupport304_suffix_decode_005 : PackedRawNatGrowth.readList 14 103 ridgeSupport304_rest_005 =
    (ridgeSupport304_suffix_005, ridgeSupport304_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 71
    ridgeSupport304_rest_005 ridgeSupport304_rest_006 ridgeSupport304_rest_009
    ridgeSupport304_005 ridgeSupport304_suffix_006 ridgeSupport304_005_decode ridgeSupport304_suffix_decode_006
theorem ridgeSupport304_suffix_decode_004 : PackedRawNatGrowth.readList 14 135 ridgeSupport304_rest_004 =
    (ridgeSupport304_suffix_004, ridgeSupport304_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 103
    ridgeSupport304_rest_004 ridgeSupport304_rest_005 ridgeSupport304_rest_009
    ridgeSupport304_004 ridgeSupport304_suffix_005 ridgeSupport304_004_decode ridgeSupport304_suffix_decode_005
theorem ridgeSupport304_suffix_decode_003 : PackedRawNatGrowth.readList 14 167 ridgeSupport304_rest_003 =
    (ridgeSupport304_suffix_003, ridgeSupport304_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 135
    ridgeSupport304_rest_003 ridgeSupport304_rest_004 ridgeSupport304_rest_009
    ridgeSupport304_003 ridgeSupport304_suffix_004 ridgeSupport304_003_decode ridgeSupport304_suffix_decode_004
theorem ridgeSupport304_suffix_decode_002 : PackedRawNatGrowth.readList 14 199 ridgeSupport304_rest_002 =
    (ridgeSupport304_suffix_002, ridgeSupport304_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 167
    ridgeSupport304_rest_002 ridgeSupport304_rest_003 ridgeSupport304_rest_009
    ridgeSupport304_002 ridgeSupport304_suffix_003 ridgeSupport304_002_decode ridgeSupport304_suffix_decode_003
theorem ridgeSupport304_suffix_decode_001 : PackedRawNatGrowth.readList 14 231 ridgeSupport304_rest_001 =
    (ridgeSupport304_suffix_001, ridgeSupport304_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 199
    ridgeSupport304_rest_001 ridgeSupport304_rest_002 ridgeSupport304_rest_009
    ridgeSupport304_001 ridgeSupport304_suffix_002 ridgeSupport304_001_decode ridgeSupport304_suffix_decode_002
theorem ridgeSupport304_suffix_decode_000 : PackedRawNatGrowth.readList 14 263 ridgeSupport304_rest_000 =
    (ridgeSupport304_suffix_000, ridgeSupport304_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 231
    ridgeSupport304_rest_000 ridgeSupport304_rest_001 ridgeSupport304_rest_009
    ridgeSupport304_000 ridgeSupport304_suffix_001 ridgeSupport304_000_decode ridgeSupport304_suffix_decode_001
theorem ridgeSupport304_eq : candidateRows 304 = ridgeSupport304_suffix_000 := by
  change candidateSupports 304 = ridgeSupport304_suffix_000
  rw [ridgeSupport304_source]
  exact congrArg Prod.fst ridgeSupport304_suffix_decode_000
theorem ridgeTest_large_304 : ridgeTest 304 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport304_eq]
    simp only [ridgeSupport304_suffix_000, ridgeSupport304_suffix_001, ridgeSupport304_suffix_002, ridgeSupport304_suffix_003, ridgeSupport304_suffix_004, ridgeSupport304_suffix_005, ridgeSupport304_suffix_006, ridgeSupport304_suffix_007, ridgeSupport304_suffix_008, ridgeSupport304_suffix_009, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport304_000_mask, ridgeSupport304_001_mask, ridgeSupport304_002_mask, ridgeSupport304_003_mask, ridgeSupport304_004_mask, ridgeSupport304_005_mask, ridgeSupport304_006_mask, ridgeSupport304_007_mask, ridgeSupport304_008_mask]
    decide +kernel
  · rw [ridgeSupport304_eq]
    simp only [ridgeSupport304_suffix_000, ridgeSupport304_suffix_001, ridgeSupport304_suffix_002, ridgeSupport304_suffix_003, ridgeSupport304_suffix_004, ridgeSupport304_suffix_005, ridgeSupport304_suffix_006, ridgeSupport304_suffix_007, ridgeSupport304_suffix_008, ridgeSupport304_suffix_009, List.all_append, List.all_nil, ridgeSupport304_000_checked, ridgeSupport304_001_checked, ridgeSupport304_002_checked, ridgeSupport304_003_checked, ridgeSupport304_004_checked, ridgeSupport304_005_checked, ridgeSupport304_006_checked, ridgeSupport304_007_checked, ridgeSupport304_008_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixExtra00
