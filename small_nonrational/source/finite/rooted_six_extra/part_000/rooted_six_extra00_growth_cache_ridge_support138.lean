module
prelude
public import RootedSixExtra00GrowthCacheRidgeSupport138Part000
public import RootedSixExtra00GrowthCacheRidgeSupport138Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra00
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport138_suffix_decode_009 : PackedRawNatGrowth.readList 14 0 ridgeSupport138_rest_009 =
    (ridgeSupport138_suffix_009, ridgeSupport138_rest_009) := by rfl
theorem ridgeSupport138_suffix_decode_008 : PackedRawNatGrowth.readList 14 7 ridgeSupport138_rest_008 =
    (ridgeSupport138_suffix_008, ridgeSupport138_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 7 0
    ridgeSupport138_rest_008 ridgeSupport138_rest_009 ridgeSupport138_rest_009
    ridgeSupport138_008 ridgeSupport138_suffix_009 ridgeSupport138_008_decode ridgeSupport138_suffix_decode_009
theorem ridgeSupport138_suffix_decode_007 : PackedRawNatGrowth.readList 14 39 ridgeSupport138_rest_007 =
    (ridgeSupport138_suffix_007, ridgeSupport138_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 7
    ridgeSupport138_rest_007 ridgeSupport138_rest_008 ridgeSupport138_rest_009
    ridgeSupport138_007 ridgeSupport138_suffix_008 ridgeSupport138_007_decode ridgeSupport138_suffix_decode_008
theorem ridgeSupport138_suffix_decode_006 : PackedRawNatGrowth.readList 14 71 ridgeSupport138_rest_006 =
    (ridgeSupport138_suffix_006, ridgeSupport138_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 39
    ridgeSupport138_rest_006 ridgeSupport138_rest_007 ridgeSupport138_rest_009
    ridgeSupport138_006 ridgeSupport138_suffix_007 ridgeSupport138_006_decode ridgeSupport138_suffix_decode_007
theorem ridgeSupport138_suffix_decode_005 : PackedRawNatGrowth.readList 14 103 ridgeSupport138_rest_005 =
    (ridgeSupport138_suffix_005, ridgeSupport138_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 71
    ridgeSupport138_rest_005 ridgeSupport138_rest_006 ridgeSupport138_rest_009
    ridgeSupport138_005 ridgeSupport138_suffix_006 ridgeSupport138_005_decode ridgeSupport138_suffix_decode_006
theorem ridgeSupport138_suffix_decode_004 : PackedRawNatGrowth.readList 14 135 ridgeSupport138_rest_004 =
    (ridgeSupport138_suffix_004, ridgeSupport138_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 103
    ridgeSupport138_rest_004 ridgeSupport138_rest_005 ridgeSupport138_rest_009
    ridgeSupport138_004 ridgeSupport138_suffix_005 ridgeSupport138_004_decode ridgeSupport138_suffix_decode_005
theorem ridgeSupport138_suffix_decode_003 : PackedRawNatGrowth.readList 14 167 ridgeSupport138_rest_003 =
    (ridgeSupport138_suffix_003, ridgeSupport138_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 135
    ridgeSupport138_rest_003 ridgeSupport138_rest_004 ridgeSupport138_rest_009
    ridgeSupport138_003 ridgeSupport138_suffix_004 ridgeSupport138_003_decode ridgeSupport138_suffix_decode_004
theorem ridgeSupport138_suffix_decode_002 : PackedRawNatGrowth.readList 14 199 ridgeSupport138_rest_002 =
    (ridgeSupport138_suffix_002, ridgeSupport138_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 167
    ridgeSupport138_rest_002 ridgeSupport138_rest_003 ridgeSupport138_rest_009
    ridgeSupport138_002 ridgeSupport138_suffix_003 ridgeSupport138_002_decode ridgeSupport138_suffix_decode_003
theorem ridgeSupport138_suffix_decode_001 : PackedRawNatGrowth.readList 14 231 ridgeSupport138_rest_001 =
    (ridgeSupport138_suffix_001, ridgeSupport138_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 199
    ridgeSupport138_rest_001 ridgeSupport138_rest_002 ridgeSupport138_rest_009
    ridgeSupport138_001 ridgeSupport138_suffix_002 ridgeSupport138_001_decode ridgeSupport138_suffix_decode_002
theorem ridgeSupport138_suffix_decode_000 : PackedRawNatGrowth.readList 14 263 ridgeSupport138_rest_000 =
    (ridgeSupport138_suffix_000, ridgeSupport138_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 231
    ridgeSupport138_rest_000 ridgeSupport138_rest_001 ridgeSupport138_rest_009
    ridgeSupport138_000 ridgeSupport138_suffix_001 ridgeSupport138_000_decode ridgeSupport138_suffix_decode_001
theorem ridgeSupport138_eq : candidateRows 138 = ridgeSupport138_suffix_000 := by
  change candidateSupports 138 = ridgeSupport138_suffix_000
  rw [ridgeSupport138_source]
  exact congrArg Prod.fst ridgeSupport138_suffix_decode_000
theorem ridgeTest_large_138 : ridgeTest 138 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport138_eq]
    simp only [ridgeSupport138_suffix_000, ridgeSupport138_suffix_001, ridgeSupport138_suffix_002, ridgeSupport138_suffix_003, ridgeSupport138_suffix_004, ridgeSupport138_suffix_005, ridgeSupport138_suffix_006, ridgeSupport138_suffix_007, ridgeSupport138_suffix_008, ridgeSupport138_suffix_009, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport138_000_mask, ridgeSupport138_001_mask, ridgeSupport138_002_mask, ridgeSupport138_003_mask, ridgeSupport138_004_mask, ridgeSupport138_005_mask, ridgeSupport138_006_mask, ridgeSupport138_007_mask, ridgeSupport138_008_mask]
    decide +kernel
  · rw [ridgeSupport138_eq]
    simp only [ridgeSupport138_suffix_000, ridgeSupport138_suffix_001, ridgeSupport138_suffix_002, ridgeSupport138_suffix_003, ridgeSupport138_suffix_004, ridgeSupport138_suffix_005, ridgeSupport138_suffix_006, ridgeSupport138_suffix_007, ridgeSupport138_suffix_008, ridgeSupport138_suffix_009, List.all_append, List.all_nil, ridgeSupport138_000_checked, ridgeSupport138_001_checked, ridgeSupport138_002_checked, ridgeSupport138_003_checked, ridgeSupport138_004_checked, ridgeSupport138_005_checked, ridgeSupport138_006_checked, ridgeSupport138_007_checked, ridgeSupport138_008_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixExtra00
