module
prelude
public import RootedSixExtra00GrowthCacheRidgeSupport385Part000
public import RootedSixExtra00GrowthCacheRidgeSupport385Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra00
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport385_suffix_decode_010 : PackedRawNatGrowth.readList 14 0 ridgeSupport385_rest_010 =
    (ridgeSupport385_suffix_010, ridgeSupport385_rest_010) := by rfl
theorem ridgeSupport385_suffix_decode_009 : PackedRawNatGrowth.readList 14 17 ridgeSupport385_rest_009 =
    (ridgeSupport385_suffix_009, ridgeSupport385_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 14 17 0
    ridgeSupport385_rest_009 ridgeSupport385_rest_010 ridgeSupport385_rest_010
    ridgeSupport385_009 ridgeSupport385_suffix_010 ridgeSupport385_009_decode ridgeSupport385_suffix_decode_010
theorem ridgeSupport385_suffix_decode_008 : PackedRawNatGrowth.readList 14 49 ridgeSupport385_rest_008 =
    (ridgeSupport385_suffix_008, ridgeSupport385_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 17
    ridgeSupport385_rest_008 ridgeSupport385_rest_009 ridgeSupport385_rest_010
    ridgeSupport385_008 ridgeSupport385_suffix_009 ridgeSupport385_008_decode ridgeSupport385_suffix_decode_009
theorem ridgeSupport385_suffix_decode_007 : PackedRawNatGrowth.readList 14 81 ridgeSupport385_rest_007 =
    (ridgeSupport385_suffix_007, ridgeSupport385_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 49
    ridgeSupport385_rest_007 ridgeSupport385_rest_008 ridgeSupport385_rest_010
    ridgeSupport385_007 ridgeSupport385_suffix_008 ridgeSupport385_007_decode ridgeSupport385_suffix_decode_008
theorem ridgeSupport385_suffix_decode_006 : PackedRawNatGrowth.readList 14 113 ridgeSupport385_rest_006 =
    (ridgeSupport385_suffix_006, ridgeSupport385_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 81
    ridgeSupport385_rest_006 ridgeSupport385_rest_007 ridgeSupport385_rest_010
    ridgeSupport385_006 ridgeSupport385_suffix_007 ridgeSupport385_006_decode ridgeSupport385_suffix_decode_007
theorem ridgeSupport385_suffix_decode_005 : PackedRawNatGrowth.readList 14 145 ridgeSupport385_rest_005 =
    (ridgeSupport385_suffix_005, ridgeSupport385_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 113
    ridgeSupport385_rest_005 ridgeSupport385_rest_006 ridgeSupport385_rest_010
    ridgeSupport385_005 ridgeSupport385_suffix_006 ridgeSupport385_005_decode ridgeSupport385_suffix_decode_006
theorem ridgeSupport385_suffix_decode_004 : PackedRawNatGrowth.readList 14 177 ridgeSupport385_rest_004 =
    (ridgeSupport385_suffix_004, ridgeSupport385_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 145
    ridgeSupport385_rest_004 ridgeSupport385_rest_005 ridgeSupport385_rest_010
    ridgeSupport385_004 ridgeSupport385_suffix_005 ridgeSupport385_004_decode ridgeSupport385_suffix_decode_005
theorem ridgeSupport385_suffix_decode_003 : PackedRawNatGrowth.readList 14 209 ridgeSupport385_rest_003 =
    (ridgeSupport385_suffix_003, ridgeSupport385_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 177
    ridgeSupport385_rest_003 ridgeSupport385_rest_004 ridgeSupport385_rest_010
    ridgeSupport385_003 ridgeSupport385_suffix_004 ridgeSupport385_003_decode ridgeSupport385_suffix_decode_004
theorem ridgeSupport385_suffix_decode_002 : PackedRawNatGrowth.readList 14 241 ridgeSupport385_rest_002 =
    (ridgeSupport385_suffix_002, ridgeSupport385_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 209
    ridgeSupport385_rest_002 ridgeSupport385_rest_003 ridgeSupport385_rest_010
    ridgeSupport385_002 ridgeSupport385_suffix_003 ridgeSupport385_002_decode ridgeSupport385_suffix_decode_003
theorem ridgeSupport385_suffix_decode_001 : PackedRawNatGrowth.readList 14 273 ridgeSupport385_rest_001 =
    (ridgeSupport385_suffix_001, ridgeSupport385_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 241
    ridgeSupport385_rest_001 ridgeSupport385_rest_002 ridgeSupport385_rest_010
    ridgeSupport385_001 ridgeSupport385_suffix_002 ridgeSupport385_001_decode ridgeSupport385_suffix_decode_002
theorem ridgeSupport385_suffix_decode_000 : PackedRawNatGrowth.readList 14 305 ridgeSupport385_rest_000 =
    (ridgeSupport385_suffix_000, ridgeSupport385_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 273
    ridgeSupport385_rest_000 ridgeSupport385_rest_001 ridgeSupport385_rest_010
    ridgeSupport385_000 ridgeSupport385_suffix_001 ridgeSupport385_000_decode ridgeSupport385_suffix_decode_001
theorem ridgeSupport385_eq : candidateRows 385 = ridgeSupport385_suffix_000 := by
  change candidateSupports 385 = ridgeSupport385_suffix_000
  rw [ridgeSupport385_source]
  exact congrArg Prod.fst ridgeSupport385_suffix_decode_000
theorem ridgeTest_large_385 : ridgeTest 385 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport385_eq]
    simp only [ridgeSupport385_suffix_000, ridgeSupport385_suffix_001, ridgeSupport385_suffix_002, ridgeSupport385_suffix_003, ridgeSupport385_suffix_004, ridgeSupport385_suffix_005, ridgeSupport385_suffix_006, ridgeSupport385_suffix_007, ridgeSupport385_suffix_008, ridgeSupport385_suffix_009, ridgeSupport385_suffix_010, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport385_000_mask, ridgeSupport385_001_mask, ridgeSupport385_002_mask, ridgeSupport385_003_mask, ridgeSupport385_004_mask, ridgeSupport385_005_mask, ridgeSupport385_006_mask, ridgeSupport385_007_mask, ridgeSupport385_008_mask, ridgeSupport385_009_mask]
    decide +kernel
  · rw [ridgeSupport385_eq]
    simp only [ridgeSupport385_suffix_000, ridgeSupport385_suffix_001, ridgeSupport385_suffix_002, ridgeSupport385_suffix_003, ridgeSupport385_suffix_004, ridgeSupport385_suffix_005, ridgeSupport385_suffix_006, ridgeSupport385_suffix_007, ridgeSupport385_suffix_008, ridgeSupport385_suffix_009, ridgeSupport385_suffix_010, List.all_append, List.all_nil, ridgeSupport385_000_checked, ridgeSupport385_001_checked, ridgeSupport385_002_checked, ridgeSupport385_003_checked, ridgeSupport385_004_checked, ridgeSupport385_005_checked, ridgeSupport385_006_checked, ridgeSupport385_007_checked, ridgeSupport385_008_checked, ridgeSupport385_009_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixExtra00
