module
prelude
public import RootedSixExtra00GrowthCacheRidgeSupport840Part000
public import RootedSixExtra00GrowthCacheRidgeSupport840Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra00
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport840_suffix_decode_009 : PackedRawNatGrowth.readList 14 0 ridgeSupport840_rest_009 =
    (ridgeSupport840_suffix_009, ridgeSupport840_rest_009) := by rfl
theorem ridgeSupport840_suffix_decode_008 : PackedRawNatGrowth.readList 14 2 ridgeSupport840_rest_008 =
    (ridgeSupport840_suffix_008, ridgeSupport840_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 2 0
    ridgeSupport840_rest_008 ridgeSupport840_rest_009 ridgeSupport840_rest_009
    ridgeSupport840_008 ridgeSupport840_suffix_009 ridgeSupport840_008_decode ridgeSupport840_suffix_decode_009
theorem ridgeSupport840_suffix_decode_007 : PackedRawNatGrowth.readList 14 34 ridgeSupport840_rest_007 =
    (ridgeSupport840_suffix_007, ridgeSupport840_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 2
    ridgeSupport840_rest_007 ridgeSupport840_rest_008 ridgeSupport840_rest_009
    ridgeSupport840_007 ridgeSupport840_suffix_008 ridgeSupport840_007_decode ridgeSupport840_suffix_decode_008
theorem ridgeSupport840_suffix_decode_006 : PackedRawNatGrowth.readList 14 66 ridgeSupport840_rest_006 =
    (ridgeSupport840_suffix_006, ridgeSupport840_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 34
    ridgeSupport840_rest_006 ridgeSupport840_rest_007 ridgeSupport840_rest_009
    ridgeSupport840_006 ridgeSupport840_suffix_007 ridgeSupport840_006_decode ridgeSupport840_suffix_decode_007
theorem ridgeSupport840_suffix_decode_005 : PackedRawNatGrowth.readList 14 98 ridgeSupport840_rest_005 =
    (ridgeSupport840_suffix_005, ridgeSupport840_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 66
    ridgeSupport840_rest_005 ridgeSupport840_rest_006 ridgeSupport840_rest_009
    ridgeSupport840_005 ridgeSupport840_suffix_006 ridgeSupport840_005_decode ridgeSupport840_suffix_decode_006
theorem ridgeSupport840_suffix_decode_004 : PackedRawNatGrowth.readList 14 130 ridgeSupport840_rest_004 =
    (ridgeSupport840_suffix_004, ridgeSupport840_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 98
    ridgeSupport840_rest_004 ridgeSupport840_rest_005 ridgeSupport840_rest_009
    ridgeSupport840_004 ridgeSupport840_suffix_005 ridgeSupport840_004_decode ridgeSupport840_suffix_decode_005
theorem ridgeSupport840_suffix_decode_003 : PackedRawNatGrowth.readList 14 162 ridgeSupport840_rest_003 =
    (ridgeSupport840_suffix_003, ridgeSupport840_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 130
    ridgeSupport840_rest_003 ridgeSupport840_rest_004 ridgeSupport840_rest_009
    ridgeSupport840_003 ridgeSupport840_suffix_004 ridgeSupport840_003_decode ridgeSupport840_suffix_decode_004
theorem ridgeSupport840_suffix_decode_002 : PackedRawNatGrowth.readList 14 194 ridgeSupport840_rest_002 =
    (ridgeSupport840_suffix_002, ridgeSupport840_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 162
    ridgeSupport840_rest_002 ridgeSupport840_rest_003 ridgeSupport840_rest_009
    ridgeSupport840_002 ridgeSupport840_suffix_003 ridgeSupport840_002_decode ridgeSupport840_suffix_decode_003
theorem ridgeSupport840_suffix_decode_001 : PackedRawNatGrowth.readList 14 226 ridgeSupport840_rest_001 =
    (ridgeSupport840_suffix_001, ridgeSupport840_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 194
    ridgeSupport840_rest_001 ridgeSupport840_rest_002 ridgeSupport840_rest_009
    ridgeSupport840_001 ridgeSupport840_suffix_002 ridgeSupport840_001_decode ridgeSupport840_suffix_decode_002
theorem ridgeSupport840_suffix_decode_000 : PackedRawNatGrowth.readList 14 258 ridgeSupport840_rest_000 =
    (ridgeSupport840_suffix_000, ridgeSupport840_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 226
    ridgeSupport840_rest_000 ridgeSupport840_rest_001 ridgeSupport840_rest_009
    ridgeSupport840_000 ridgeSupport840_suffix_001 ridgeSupport840_000_decode ridgeSupport840_suffix_decode_001
theorem ridgeSupport840_eq : candidateRows 840 = ridgeSupport840_suffix_000 := by
  change candidateSupports 840 = ridgeSupport840_suffix_000
  rw [ridgeSupport840_source]
  exact congrArg Prod.fst ridgeSupport840_suffix_decode_000
theorem ridgeTest_large_840 : ridgeTest 840 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport840_eq]
    simp only [ridgeSupport840_suffix_000, ridgeSupport840_suffix_001, ridgeSupport840_suffix_002, ridgeSupport840_suffix_003, ridgeSupport840_suffix_004, ridgeSupport840_suffix_005, ridgeSupport840_suffix_006, ridgeSupport840_suffix_007, ridgeSupport840_suffix_008, ridgeSupport840_suffix_009, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport840_000_mask, ridgeSupport840_001_mask, ridgeSupport840_002_mask, ridgeSupport840_003_mask, ridgeSupport840_004_mask, ridgeSupport840_005_mask, ridgeSupport840_006_mask, ridgeSupport840_007_mask, ridgeSupport840_008_mask]
    decide +kernel
  · rw [ridgeSupport840_eq]
    simp only [ridgeSupport840_suffix_000, ridgeSupport840_suffix_001, ridgeSupport840_suffix_002, ridgeSupport840_suffix_003, ridgeSupport840_suffix_004, ridgeSupport840_suffix_005, ridgeSupport840_suffix_006, ridgeSupport840_suffix_007, ridgeSupport840_suffix_008, ridgeSupport840_suffix_009, List.all_append, List.all_nil, ridgeSupport840_000_checked, ridgeSupport840_001_checked, ridgeSupport840_002_checked, ridgeSupport840_003_checked, ridgeSupport840_004_checked, ridgeSupport840_005_checked, ridgeSupport840_006_checked, ridgeSupport840_007_checked, ridgeSupport840_008_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixExtra00
