module
prelude
public import RootedSixExtra00GrowthCacheRidgeSupport672Part000
public import RootedSixExtra00GrowthCacheRidgeSupport672Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra00
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport672_suffix_decode_010 : PackedRawNatGrowth.readList 14 0 ridgeSupport672_rest_010 =
    (ridgeSupport672_suffix_010, ridgeSupport672_rest_010) := by rfl
theorem ridgeSupport672_suffix_decode_009 : PackedRawNatGrowth.readList 14 17 ridgeSupport672_rest_009 =
    (ridgeSupport672_suffix_009, ridgeSupport672_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 14 17 0
    ridgeSupport672_rest_009 ridgeSupport672_rest_010 ridgeSupport672_rest_010
    ridgeSupport672_009 ridgeSupport672_suffix_010 ridgeSupport672_009_decode ridgeSupport672_suffix_decode_010
theorem ridgeSupport672_suffix_decode_008 : PackedRawNatGrowth.readList 14 49 ridgeSupport672_rest_008 =
    (ridgeSupport672_suffix_008, ridgeSupport672_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 17
    ridgeSupport672_rest_008 ridgeSupport672_rest_009 ridgeSupport672_rest_010
    ridgeSupport672_008 ridgeSupport672_suffix_009 ridgeSupport672_008_decode ridgeSupport672_suffix_decode_009
theorem ridgeSupport672_suffix_decode_007 : PackedRawNatGrowth.readList 14 81 ridgeSupport672_rest_007 =
    (ridgeSupport672_suffix_007, ridgeSupport672_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 49
    ridgeSupport672_rest_007 ridgeSupport672_rest_008 ridgeSupport672_rest_010
    ridgeSupport672_007 ridgeSupport672_suffix_008 ridgeSupport672_007_decode ridgeSupport672_suffix_decode_008
theorem ridgeSupport672_suffix_decode_006 : PackedRawNatGrowth.readList 14 113 ridgeSupport672_rest_006 =
    (ridgeSupport672_suffix_006, ridgeSupport672_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 81
    ridgeSupport672_rest_006 ridgeSupport672_rest_007 ridgeSupport672_rest_010
    ridgeSupport672_006 ridgeSupport672_suffix_007 ridgeSupport672_006_decode ridgeSupport672_suffix_decode_007
theorem ridgeSupport672_suffix_decode_005 : PackedRawNatGrowth.readList 14 145 ridgeSupport672_rest_005 =
    (ridgeSupport672_suffix_005, ridgeSupport672_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 113
    ridgeSupport672_rest_005 ridgeSupport672_rest_006 ridgeSupport672_rest_010
    ridgeSupport672_005 ridgeSupport672_suffix_006 ridgeSupport672_005_decode ridgeSupport672_suffix_decode_006
theorem ridgeSupport672_suffix_decode_004 : PackedRawNatGrowth.readList 14 177 ridgeSupport672_rest_004 =
    (ridgeSupport672_suffix_004, ridgeSupport672_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 145
    ridgeSupport672_rest_004 ridgeSupport672_rest_005 ridgeSupport672_rest_010
    ridgeSupport672_004 ridgeSupport672_suffix_005 ridgeSupport672_004_decode ridgeSupport672_suffix_decode_005
theorem ridgeSupport672_suffix_decode_003 : PackedRawNatGrowth.readList 14 209 ridgeSupport672_rest_003 =
    (ridgeSupport672_suffix_003, ridgeSupport672_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 177
    ridgeSupport672_rest_003 ridgeSupport672_rest_004 ridgeSupport672_rest_010
    ridgeSupport672_003 ridgeSupport672_suffix_004 ridgeSupport672_003_decode ridgeSupport672_suffix_decode_004
theorem ridgeSupport672_suffix_decode_002 : PackedRawNatGrowth.readList 14 241 ridgeSupport672_rest_002 =
    (ridgeSupport672_suffix_002, ridgeSupport672_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 209
    ridgeSupport672_rest_002 ridgeSupport672_rest_003 ridgeSupport672_rest_010
    ridgeSupport672_002 ridgeSupport672_suffix_003 ridgeSupport672_002_decode ridgeSupport672_suffix_decode_003
theorem ridgeSupport672_suffix_decode_001 : PackedRawNatGrowth.readList 14 273 ridgeSupport672_rest_001 =
    (ridgeSupport672_suffix_001, ridgeSupport672_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 241
    ridgeSupport672_rest_001 ridgeSupport672_rest_002 ridgeSupport672_rest_010
    ridgeSupport672_001 ridgeSupport672_suffix_002 ridgeSupport672_001_decode ridgeSupport672_suffix_decode_002
theorem ridgeSupport672_suffix_decode_000 : PackedRawNatGrowth.readList 14 305 ridgeSupport672_rest_000 =
    (ridgeSupport672_suffix_000, ridgeSupport672_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 273
    ridgeSupport672_rest_000 ridgeSupport672_rest_001 ridgeSupport672_rest_010
    ridgeSupport672_000 ridgeSupport672_suffix_001 ridgeSupport672_000_decode ridgeSupport672_suffix_decode_001
theorem ridgeSupport672_eq : candidateRows 672 = ridgeSupport672_suffix_000 := by
  change candidateSupports 672 = ridgeSupport672_suffix_000
  rw [ridgeSupport672_source]
  exact congrArg Prod.fst ridgeSupport672_suffix_decode_000
theorem ridgeTest_large_672 : ridgeTest 672 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport672_eq]
    simp only [ridgeSupport672_suffix_000, ridgeSupport672_suffix_001, ridgeSupport672_suffix_002, ridgeSupport672_suffix_003, ridgeSupport672_suffix_004, ridgeSupport672_suffix_005, ridgeSupport672_suffix_006, ridgeSupport672_suffix_007, ridgeSupport672_suffix_008, ridgeSupport672_suffix_009, ridgeSupport672_suffix_010, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport672_000_mask, ridgeSupport672_001_mask, ridgeSupport672_002_mask, ridgeSupport672_003_mask, ridgeSupport672_004_mask, ridgeSupport672_005_mask, ridgeSupport672_006_mask, ridgeSupport672_007_mask, ridgeSupport672_008_mask, ridgeSupport672_009_mask]
    decide +kernel
  · rw [ridgeSupport672_eq]
    simp only [ridgeSupport672_suffix_000, ridgeSupport672_suffix_001, ridgeSupport672_suffix_002, ridgeSupport672_suffix_003, ridgeSupport672_suffix_004, ridgeSupport672_suffix_005, ridgeSupport672_suffix_006, ridgeSupport672_suffix_007, ridgeSupport672_suffix_008, ridgeSupport672_suffix_009, ridgeSupport672_suffix_010, List.all_append, List.all_nil, ridgeSupport672_000_checked, ridgeSupport672_001_checked, ridgeSupport672_002_checked, ridgeSupport672_003_checked, ridgeSupport672_004_checked, ridgeSupport672_005_checked, ridgeSupport672_006_checked, ridgeSupport672_007_checked, ridgeSupport672_008_checked, ridgeSupport672_009_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixExtra00
