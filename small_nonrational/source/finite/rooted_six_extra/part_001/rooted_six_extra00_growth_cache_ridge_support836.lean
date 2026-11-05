module
prelude
public import RootedSixExtra00GrowthCacheRidgeSupport836Part000
public import RootedSixExtra00GrowthCacheRidgeSupport836Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra00
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport836_suffix_decode_009 : PackedRawNatGrowth.readList 14 0 ridgeSupport836_rest_009 =
    (ridgeSupport836_suffix_009, ridgeSupport836_rest_009) := by rfl
theorem ridgeSupport836_suffix_decode_008 : PackedRawNatGrowth.readList 14 2 ridgeSupport836_rest_008 =
    (ridgeSupport836_suffix_008, ridgeSupport836_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 2 0
    ridgeSupport836_rest_008 ridgeSupport836_rest_009 ridgeSupport836_rest_009
    ridgeSupport836_008 ridgeSupport836_suffix_009 ridgeSupport836_008_decode ridgeSupport836_suffix_decode_009
theorem ridgeSupport836_suffix_decode_007 : PackedRawNatGrowth.readList 14 34 ridgeSupport836_rest_007 =
    (ridgeSupport836_suffix_007, ridgeSupport836_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 2
    ridgeSupport836_rest_007 ridgeSupport836_rest_008 ridgeSupport836_rest_009
    ridgeSupport836_007 ridgeSupport836_suffix_008 ridgeSupport836_007_decode ridgeSupport836_suffix_decode_008
theorem ridgeSupport836_suffix_decode_006 : PackedRawNatGrowth.readList 14 66 ridgeSupport836_rest_006 =
    (ridgeSupport836_suffix_006, ridgeSupport836_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 34
    ridgeSupport836_rest_006 ridgeSupport836_rest_007 ridgeSupport836_rest_009
    ridgeSupport836_006 ridgeSupport836_suffix_007 ridgeSupport836_006_decode ridgeSupport836_suffix_decode_007
theorem ridgeSupport836_suffix_decode_005 : PackedRawNatGrowth.readList 14 98 ridgeSupport836_rest_005 =
    (ridgeSupport836_suffix_005, ridgeSupport836_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 66
    ridgeSupport836_rest_005 ridgeSupport836_rest_006 ridgeSupport836_rest_009
    ridgeSupport836_005 ridgeSupport836_suffix_006 ridgeSupport836_005_decode ridgeSupport836_suffix_decode_006
theorem ridgeSupport836_suffix_decode_004 : PackedRawNatGrowth.readList 14 130 ridgeSupport836_rest_004 =
    (ridgeSupport836_suffix_004, ridgeSupport836_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 98
    ridgeSupport836_rest_004 ridgeSupport836_rest_005 ridgeSupport836_rest_009
    ridgeSupport836_004 ridgeSupport836_suffix_005 ridgeSupport836_004_decode ridgeSupport836_suffix_decode_005
theorem ridgeSupport836_suffix_decode_003 : PackedRawNatGrowth.readList 14 162 ridgeSupport836_rest_003 =
    (ridgeSupport836_suffix_003, ridgeSupport836_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 130
    ridgeSupport836_rest_003 ridgeSupport836_rest_004 ridgeSupport836_rest_009
    ridgeSupport836_003 ridgeSupport836_suffix_004 ridgeSupport836_003_decode ridgeSupport836_suffix_decode_004
theorem ridgeSupport836_suffix_decode_002 : PackedRawNatGrowth.readList 14 194 ridgeSupport836_rest_002 =
    (ridgeSupport836_suffix_002, ridgeSupport836_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 162
    ridgeSupport836_rest_002 ridgeSupport836_rest_003 ridgeSupport836_rest_009
    ridgeSupport836_002 ridgeSupport836_suffix_003 ridgeSupport836_002_decode ridgeSupport836_suffix_decode_003
theorem ridgeSupport836_suffix_decode_001 : PackedRawNatGrowth.readList 14 226 ridgeSupport836_rest_001 =
    (ridgeSupport836_suffix_001, ridgeSupport836_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 194
    ridgeSupport836_rest_001 ridgeSupport836_rest_002 ridgeSupport836_rest_009
    ridgeSupport836_001 ridgeSupport836_suffix_002 ridgeSupport836_001_decode ridgeSupport836_suffix_decode_002
theorem ridgeSupport836_suffix_decode_000 : PackedRawNatGrowth.readList 14 258 ridgeSupport836_rest_000 =
    (ridgeSupport836_suffix_000, ridgeSupport836_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 226
    ridgeSupport836_rest_000 ridgeSupport836_rest_001 ridgeSupport836_rest_009
    ridgeSupport836_000 ridgeSupport836_suffix_001 ridgeSupport836_000_decode ridgeSupport836_suffix_decode_001
theorem ridgeSupport836_eq : candidateRows 836 = ridgeSupport836_suffix_000 := by
  change candidateSupports 836 = ridgeSupport836_suffix_000
  rw [ridgeSupport836_source]
  exact congrArg Prod.fst ridgeSupport836_suffix_decode_000
theorem ridgeTest_large_836 : ridgeTest 836 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport836_eq]
    simp only [ridgeSupport836_suffix_000, ridgeSupport836_suffix_001, ridgeSupport836_suffix_002, ridgeSupport836_suffix_003, ridgeSupport836_suffix_004, ridgeSupport836_suffix_005, ridgeSupport836_suffix_006, ridgeSupport836_suffix_007, ridgeSupport836_suffix_008, ridgeSupport836_suffix_009, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport836_000_mask, ridgeSupport836_001_mask, ridgeSupport836_002_mask, ridgeSupport836_003_mask, ridgeSupport836_004_mask, ridgeSupport836_005_mask, ridgeSupport836_006_mask, ridgeSupport836_007_mask, ridgeSupport836_008_mask]
    decide +kernel
  · rw [ridgeSupport836_eq]
    simp only [ridgeSupport836_suffix_000, ridgeSupport836_suffix_001, ridgeSupport836_suffix_002, ridgeSupport836_suffix_003, ridgeSupport836_suffix_004, ridgeSupport836_suffix_005, ridgeSupport836_suffix_006, ridgeSupport836_suffix_007, ridgeSupport836_suffix_008, ridgeSupport836_suffix_009, List.all_append, List.all_nil, ridgeSupport836_000_checked, ridgeSupport836_001_checked, ridgeSupport836_002_checked, ridgeSupport836_003_checked, ridgeSupport836_004_checked, ridgeSupport836_005_checked, ridgeSupport836_006_checked, ridgeSupport836_007_checked, ridgeSupport836_008_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixExtra00
