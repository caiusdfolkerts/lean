module
prelude
public import RootedSixExtra00GrowthCacheRidgeSupport67Part000
public import RootedSixExtra00GrowthCacheRidgeSupport67Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra00
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport67_suffix_decode_009 : PackedRawNatGrowth.readList 14 0 ridgeSupport67_rest_009 =
    (ridgeSupport67_suffix_009, ridgeSupport67_rest_009) := by rfl
theorem ridgeSupport67_suffix_decode_008 : PackedRawNatGrowth.readList 14 7 ridgeSupport67_rest_008 =
    (ridgeSupport67_suffix_008, ridgeSupport67_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 7 0
    ridgeSupport67_rest_008 ridgeSupport67_rest_009 ridgeSupport67_rest_009
    ridgeSupport67_008 ridgeSupport67_suffix_009 ridgeSupport67_008_decode ridgeSupport67_suffix_decode_009
theorem ridgeSupport67_suffix_decode_007 : PackedRawNatGrowth.readList 14 39 ridgeSupport67_rest_007 =
    (ridgeSupport67_suffix_007, ridgeSupport67_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 7
    ridgeSupport67_rest_007 ridgeSupport67_rest_008 ridgeSupport67_rest_009
    ridgeSupport67_007 ridgeSupport67_suffix_008 ridgeSupport67_007_decode ridgeSupport67_suffix_decode_008
theorem ridgeSupport67_suffix_decode_006 : PackedRawNatGrowth.readList 14 71 ridgeSupport67_rest_006 =
    (ridgeSupport67_suffix_006, ridgeSupport67_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 39
    ridgeSupport67_rest_006 ridgeSupport67_rest_007 ridgeSupport67_rest_009
    ridgeSupport67_006 ridgeSupport67_suffix_007 ridgeSupport67_006_decode ridgeSupport67_suffix_decode_007
theorem ridgeSupport67_suffix_decode_005 : PackedRawNatGrowth.readList 14 103 ridgeSupport67_rest_005 =
    (ridgeSupport67_suffix_005, ridgeSupport67_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 71
    ridgeSupport67_rest_005 ridgeSupport67_rest_006 ridgeSupport67_rest_009
    ridgeSupport67_005 ridgeSupport67_suffix_006 ridgeSupport67_005_decode ridgeSupport67_suffix_decode_006
theorem ridgeSupport67_suffix_decode_004 : PackedRawNatGrowth.readList 14 135 ridgeSupport67_rest_004 =
    (ridgeSupport67_suffix_004, ridgeSupport67_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 103
    ridgeSupport67_rest_004 ridgeSupport67_rest_005 ridgeSupport67_rest_009
    ridgeSupport67_004 ridgeSupport67_suffix_005 ridgeSupport67_004_decode ridgeSupport67_suffix_decode_005
theorem ridgeSupport67_suffix_decode_003 : PackedRawNatGrowth.readList 14 167 ridgeSupport67_rest_003 =
    (ridgeSupport67_suffix_003, ridgeSupport67_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 135
    ridgeSupport67_rest_003 ridgeSupport67_rest_004 ridgeSupport67_rest_009
    ridgeSupport67_003 ridgeSupport67_suffix_004 ridgeSupport67_003_decode ridgeSupport67_suffix_decode_004
theorem ridgeSupport67_suffix_decode_002 : PackedRawNatGrowth.readList 14 199 ridgeSupport67_rest_002 =
    (ridgeSupport67_suffix_002, ridgeSupport67_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 167
    ridgeSupport67_rest_002 ridgeSupport67_rest_003 ridgeSupport67_rest_009
    ridgeSupport67_002 ridgeSupport67_suffix_003 ridgeSupport67_002_decode ridgeSupport67_suffix_decode_003
theorem ridgeSupport67_suffix_decode_001 : PackedRawNatGrowth.readList 14 231 ridgeSupport67_rest_001 =
    (ridgeSupport67_suffix_001, ridgeSupport67_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 199
    ridgeSupport67_rest_001 ridgeSupport67_rest_002 ridgeSupport67_rest_009
    ridgeSupport67_001 ridgeSupport67_suffix_002 ridgeSupport67_001_decode ridgeSupport67_suffix_decode_002
theorem ridgeSupport67_suffix_decode_000 : PackedRawNatGrowth.readList 14 263 ridgeSupport67_rest_000 =
    (ridgeSupport67_suffix_000, ridgeSupport67_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 231
    ridgeSupport67_rest_000 ridgeSupport67_rest_001 ridgeSupport67_rest_009
    ridgeSupport67_000 ridgeSupport67_suffix_001 ridgeSupport67_000_decode ridgeSupport67_suffix_decode_001
theorem ridgeSupport67_eq : candidateRows 67 = ridgeSupport67_suffix_000 := by
  change candidateSupports 67 = ridgeSupport67_suffix_000
  rw [ridgeSupport67_source]
  exact congrArg Prod.fst ridgeSupport67_suffix_decode_000
theorem ridgeTest_large_67 : ridgeTest 67 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport67_eq]
    simp only [ridgeSupport67_suffix_000, ridgeSupport67_suffix_001, ridgeSupport67_suffix_002, ridgeSupport67_suffix_003, ridgeSupport67_suffix_004, ridgeSupport67_suffix_005, ridgeSupport67_suffix_006, ridgeSupport67_suffix_007, ridgeSupport67_suffix_008, ridgeSupport67_suffix_009, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport67_000_mask, ridgeSupport67_001_mask, ridgeSupport67_002_mask, ridgeSupport67_003_mask, ridgeSupport67_004_mask, ridgeSupport67_005_mask, ridgeSupport67_006_mask, ridgeSupport67_007_mask, ridgeSupport67_008_mask]
    decide +kernel
  · rw [ridgeSupport67_eq]
    simp only [ridgeSupport67_suffix_000, ridgeSupport67_suffix_001, ridgeSupport67_suffix_002, ridgeSupport67_suffix_003, ridgeSupport67_suffix_004, ridgeSupport67_suffix_005, ridgeSupport67_suffix_006, ridgeSupport67_suffix_007, ridgeSupport67_suffix_008, ridgeSupport67_suffix_009, List.all_append, List.all_nil, ridgeSupport67_000_checked, ridgeSupport67_001_checked, ridgeSupport67_002_checked, ridgeSupport67_003_checked, ridgeSupport67_004_checked, ridgeSupport67_005_checked, ridgeSupport67_006_checked, ridgeSupport67_007_checked, ridgeSupport67_008_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixExtra00
