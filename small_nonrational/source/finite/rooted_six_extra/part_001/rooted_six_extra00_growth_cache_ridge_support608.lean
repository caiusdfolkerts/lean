module
prelude
public import RootedSixExtra00GrowthCacheRidgeSupport608Part000
public import RootedSixExtra00GrowthCacheRidgeSupport608Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra00
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport608_suffix_decode_010 : PackedRawNatGrowth.readList 14 0 ridgeSupport608_rest_010 =
    (ridgeSupport608_suffix_010, ridgeSupport608_rest_010) := by rfl
theorem ridgeSupport608_suffix_decode_009 : PackedRawNatGrowth.readList 14 17 ridgeSupport608_rest_009 =
    (ridgeSupport608_suffix_009, ridgeSupport608_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 14 17 0
    ridgeSupport608_rest_009 ridgeSupport608_rest_010 ridgeSupport608_rest_010
    ridgeSupport608_009 ridgeSupport608_suffix_010 ridgeSupport608_009_decode ridgeSupport608_suffix_decode_010
theorem ridgeSupport608_suffix_decode_008 : PackedRawNatGrowth.readList 14 49 ridgeSupport608_rest_008 =
    (ridgeSupport608_suffix_008, ridgeSupport608_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 17
    ridgeSupport608_rest_008 ridgeSupport608_rest_009 ridgeSupport608_rest_010
    ridgeSupport608_008 ridgeSupport608_suffix_009 ridgeSupport608_008_decode ridgeSupport608_suffix_decode_009
theorem ridgeSupport608_suffix_decode_007 : PackedRawNatGrowth.readList 14 81 ridgeSupport608_rest_007 =
    (ridgeSupport608_suffix_007, ridgeSupport608_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 49
    ridgeSupport608_rest_007 ridgeSupport608_rest_008 ridgeSupport608_rest_010
    ridgeSupport608_007 ridgeSupport608_suffix_008 ridgeSupport608_007_decode ridgeSupport608_suffix_decode_008
theorem ridgeSupport608_suffix_decode_006 : PackedRawNatGrowth.readList 14 113 ridgeSupport608_rest_006 =
    (ridgeSupport608_suffix_006, ridgeSupport608_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 81
    ridgeSupport608_rest_006 ridgeSupport608_rest_007 ridgeSupport608_rest_010
    ridgeSupport608_006 ridgeSupport608_suffix_007 ridgeSupport608_006_decode ridgeSupport608_suffix_decode_007
theorem ridgeSupport608_suffix_decode_005 : PackedRawNatGrowth.readList 14 145 ridgeSupport608_rest_005 =
    (ridgeSupport608_suffix_005, ridgeSupport608_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 113
    ridgeSupport608_rest_005 ridgeSupport608_rest_006 ridgeSupport608_rest_010
    ridgeSupport608_005 ridgeSupport608_suffix_006 ridgeSupport608_005_decode ridgeSupport608_suffix_decode_006
theorem ridgeSupport608_suffix_decode_004 : PackedRawNatGrowth.readList 14 177 ridgeSupport608_rest_004 =
    (ridgeSupport608_suffix_004, ridgeSupport608_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 145
    ridgeSupport608_rest_004 ridgeSupport608_rest_005 ridgeSupport608_rest_010
    ridgeSupport608_004 ridgeSupport608_suffix_005 ridgeSupport608_004_decode ridgeSupport608_suffix_decode_005
theorem ridgeSupport608_suffix_decode_003 : PackedRawNatGrowth.readList 14 209 ridgeSupport608_rest_003 =
    (ridgeSupport608_suffix_003, ridgeSupport608_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 177
    ridgeSupport608_rest_003 ridgeSupport608_rest_004 ridgeSupport608_rest_010
    ridgeSupport608_003 ridgeSupport608_suffix_004 ridgeSupport608_003_decode ridgeSupport608_suffix_decode_004
theorem ridgeSupport608_suffix_decode_002 : PackedRawNatGrowth.readList 14 241 ridgeSupport608_rest_002 =
    (ridgeSupport608_suffix_002, ridgeSupport608_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 209
    ridgeSupport608_rest_002 ridgeSupport608_rest_003 ridgeSupport608_rest_010
    ridgeSupport608_002 ridgeSupport608_suffix_003 ridgeSupport608_002_decode ridgeSupport608_suffix_decode_003
theorem ridgeSupport608_suffix_decode_001 : PackedRawNatGrowth.readList 14 273 ridgeSupport608_rest_001 =
    (ridgeSupport608_suffix_001, ridgeSupport608_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 241
    ridgeSupport608_rest_001 ridgeSupport608_rest_002 ridgeSupport608_rest_010
    ridgeSupport608_001 ridgeSupport608_suffix_002 ridgeSupport608_001_decode ridgeSupport608_suffix_decode_002
theorem ridgeSupport608_suffix_decode_000 : PackedRawNatGrowth.readList 14 305 ridgeSupport608_rest_000 =
    (ridgeSupport608_suffix_000, ridgeSupport608_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 273
    ridgeSupport608_rest_000 ridgeSupport608_rest_001 ridgeSupport608_rest_010
    ridgeSupport608_000 ridgeSupport608_suffix_001 ridgeSupport608_000_decode ridgeSupport608_suffix_decode_001
theorem ridgeSupport608_eq : candidateRows 608 = ridgeSupport608_suffix_000 := by
  change candidateSupports 608 = ridgeSupport608_suffix_000
  rw [ridgeSupport608_source]
  exact congrArg Prod.fst ridgeSupport608_suffix_decode_000
theorem ridgeTest_large_608 : ridgeTest 608 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport608_eq]
    simp only [ridgeSupport608_suffix_000, ridgeSupport608_suffix_001, ridgeSupport608_suffix_002, ridgeSupport608_suffix_003, ridgeSupport608_suffix_004, ridgeSupport608_suffix_005, ridgeSupport608_suffix_006, ridgeSupport608_suffix_007, ridgeSupport608_suffix_008, ridgeSupport608_suffix_009, ridgeSupport608_suffix_010, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport608_000_mask, ridgeSupport608_001_mask, ridgeSupport608_002_mask, ridgeSupport608_003_mask, ridgeSupport608_004_mask, ridgeSupport608_005_mask, ridgeSupport608_006_mask, ridgeSupport608_007_mask, ridgeSupport608_008_mask, ridgeSupport608_009_mask]
    decide +kernel
  · rw [ridgeSupport608_eq]
    simp only [ridgeSupport608_suffix_000, ridgeSupport608_suffix_001, ridgeSupport608_suffix_002, ridgeSupport608_suffix_003, ridgeSupport608_suffix_004, ridgeSupport608_suffix_005, ridgeSupport608_suffix_006, ridgeSupport608_suffix_007, ridgeSupport608_suffix_008, ridgeSupport608_suffix_009, ridgeSupport608_suffix_010, List.all_append, List.all_nil, ridgeSupport608_000_checked, ridgeSupport608_001_checked, ridgeSupport608_002_checked, ridgeSupport608_003_checked, ridgeSupport608_004_checked, ridgeSupport608_005_checked, ridgeSupport608_006_checked, ridgeSupport608_007_checked, ridgeSupport608_008_checked, ridgeSupport608_009_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixExtra00
