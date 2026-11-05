module
prelude
public import RootedSixExtra00GrowthCacheRidgeSupport641Part000
public import RootedSixExtra00GrowthCacheRidgeSupport641Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra00
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport641_suffix_decode_010 : PackedRawNatGrowth.readList 14 0 ridgeSupport641_rest_010 =
    (ridgeSupport641_suffix_010, ridgeSupport641_rest_010) := by rfl
theorem ridgeSupport641_suffix_decode_009 : PackedRawNatGrowth.readList 14 17 ridgeSupport641_rest_009 =
    (ridgeSupport641_suffix_009, ridgeSupport641_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 14 17 0
    ridgeSupport641_rest_009 ridgeSupport641_rest_010 ridgeSupport641_rest_010
    ridgeSupport641_009 ridgeSupport641_suffix_010 ridgeSupport641_009_decode ridgeSupport641_suffix_decode_010
theorem ridgeSupport641_suffix_decode_008 : PackedRawNatGrowth.readList 14 49 ridgeSupport641_rest_008 =
    (ridgeSupport641_suffix_008, ridgeSupport641_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 17
    ridgeSupport641_rest_008 ridgeSupport641_rest_009 ridgeSupport641_rest_010
    ridgeSupport641_008 ridgeSupport641_suffix_009 ridgeSupport641_008_decode ridgeSupport641_suffix_decode_009
theorem ridgeSupport641_suffix_decode_007 : PackedRawNatGrowth.readList 14 81 ridgeSupport641_rest_007 =
    (ridgeSupport641_suffix_007, ridgeSupport641_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 49
    ridgeSupport641_rest_007 ridgeSupport641_rest_008 ridgeSupport641_rest_010
    ridgeSupport641_007 ridgeSupport641_suffix_008 ridgeSupport641_007_decode ridgeSupport641_suffix_decode_008
theorem ridgeSupport641_suffix_decode_006 : PackedRawNatGrowth.readList 14 113 ridgeSupport641_rest_006 =
    (ridgeSupport641_suffix_006, ridgeSupport641_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 81
    ridgeSupport641_rest_006 ridgeSupport641_rest_007 ridgeSupport641_rest_010
    ridgeSupport641_006 ridgeSupport641_suffix_007 ridgeSupport641_006_decode ridgeSupport641_suffix_decode_007
theorem ridgeSupport641_suffix_decode_005 : PackedRawNatGrowth.readList 14 145 ridgeSupport641_rest_005 =
    (ridgeSupport641_suffix_005, ridgeSupport641_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 113
    ridgeSupport641_rest_005 ridgeSupport641_rest_006 ridgeSupport641_rest_010
    ridgeSupport641_005 ridgeSupport641_suffix_006 ridgeSupport641_005_decode ridgeSupport641_suffix_decode_006
theorem ridgeSupport641_suffix_decode_004 : PackedRawNatGrowth.readList 14 177 ridgeSupport641_rest_004 =
    (ridgeSupport641_suffix_004, ridgeSupport641_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 145
    ridgeSupport641_rest_004 ridgeSupport641_rest_005 ridgeSupport641_rest_010
    ridgeSupport641_004 ridgeSupport641_suffix_005 ridgeSupport641_004_decode ridgeSupport641_suffix_decode_005
theorem ridgeSupport641_suffix_decode_003 : PackedRawNatGrowth.readList 14 209 ridgeSupport641_rest_003 =
    (ridgeSupport641_suffix_003, ridgeSupport641_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 177
    ridgeSupport641_rest_003 ridgeSupport641_rest_004 ridgeSupport641_rest_010
    ridgeSupport641_003 ridgeSupport641_suffix_004 ridgeSupport641_003_decode ridgeSupport641_suffix_decode_004
theorem ridgeSupport641_suffix_decode_002 : PackedRawNatGrowth.readList 14 241 ridgeSupport641_rest_002 =
    (ridgeSupport641_suffix_002, ridgeSupport641_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 209
    ridgeSupport641_rest_002 ridgeSupport641_rest_003 ridgeSupport641_rest_010
    ridgeSupport641_002 ridgeSupport641_suffix_003 ridgeSupport641_002_decode ridgeSupport641_suffix_decode_003
theorem ridgeSupport641_suffix_decode_001 : PackedRawNatGrowth.readList 14 273 ridgeSupport641_rest_001 =
    (ridgeSupport641_suffix_001, ridgeSupport641_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 241
    ridgeSupport641_rest_001 ridgeSupport641_rest_002 ridgeSupport641_rest_010
    ridgeSupport641_001 ridgeSupport641_suffix_002 ridgeSupport641_001_decode ridgeSupport641_suffix_decode_002
theorem ridgeSupport641_suffix_decode_000 : PackedRawNatGrowth.readList 14 305 ridgeSupport641_rest_000 =
    (ridgeSupport641_suffix_000, ridgeSupport641_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 273
    ridgeSupport641_rest_000 ridgeSupport641_rest_001 ridgeSupport641_rest_010
    ridgeSupport641_000 ridgeSupport641_suffix_001 ridgeSupport641_000_decode ridgeSupport641_suffix_decode_001
theorem ridgeSupport641_eq : candidateRows 641 = ridgeSupport641_suffix_000 := by
  change candidateSupports 641 = ridgeSupport641_suffix_000
  rw [ridgeSupport641_source]
  exact congrArg Prod.fst ridgeSupport641_suffix_decode_000
theorem ridgeTest_large_641 : ridgeTest 641 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport641_eq]
    simp only [ridgeSupport641_suffix_000, ridgeSupport641_suffix_001, ridgeSupport641_suffix_002, ridgeSupport641_suffix_003, ridgeSupport641_suffix_004, ridgeSupport641_suffix_005, ridgeSupport641_suffix_006, ridgeSupport641_suffix_007, ridgeSupport641_suffix_008, ridgeSupport641_suffix_009, ridgeSupport641_suffix_010, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport641_000_mask, ridgeSupport641_001_mask, ridgeSupport641_002_mask, ridgeSupport641_003_mask, ridgeSupport641_004_mask, ridgeSupport641_005_mask, ridgeSupport641_006_mask, ridgeSupport641_007_mask, ridgeSupport641_008_mask, ridgeSupport641_009_mask]
    decide +kernel
  · rw [ridgeSupport641_eq]
    simp only [ridgeSupport641_suffix_000, ridgeSupport641_suffix_001, ridgeSupport641_suffix_002, ridgeSupport641_suffix_003, ridgeSupport641_suffix_004, ridgeSupport641_suffix_005, ridgeSupport641_suffix_006, ridgeSupport641_suffix_007, ridgeSupport641_suffix_008, ridgeSupport641_suffix_009, ridgeSupport641_suffix_010, List.all_append, List.all_nil, ridgeSupport641_000_checked, ridgeSupport641_001_checked, ridgeSupport641_002_checked, ridgeSupport641_003_checked, ridgeSupport641_004_checked, ridgeSupport641_005_checked, ridgeSupport641_006_checked, ridgeSupport641_007_checked, ridgeSupport641_008_checked, ridgeSupport641_009_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixExtra00
