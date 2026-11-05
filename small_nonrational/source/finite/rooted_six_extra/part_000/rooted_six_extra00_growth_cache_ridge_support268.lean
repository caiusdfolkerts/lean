module
prelude
public import RootedSixExtra00GrowthCacheRidgeSupport268Part000
public import RootedSixExtra00GrowthCacheRidgeSupport268Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra00
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport268_suffix_decode_009 : PackedRawNatGrowth.readList 14 0 ridgeSupport268_rest_009 =
    (ridgeSupport268_suffix_009, ridgeSupport268_rest_009) := by rfl
theorem ridgeSupport268_suffix_decode_008 : PackedRawNatGrowth.readList 14 7 ridgeSupport268_rest_008 =
    (ridgeSupport268_suffix_008, ridgeSupport268_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 7 0
    ridgeSupport268_rest_008 ridgeSupport268_rest_009 ridgeSupport268_rest_009
    ridgeSupport268_008 ridgeSupport268_suffix_009 ridgeSupport268_008_decode ridgeSupport268_suffix_decode_009
theorem ridgeSupport268_suffix_decode_007 : PackedRawNatGrowth.readList 14 39 ridgeSupport268_rest_007 =
    (ridgeSupport268_suffix_007, ridgeSupport268_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 7
    ridgeSupport268_rest_007 ridgeSupport268_rest_008 ridgeSupport268_rest_009
    ridgeSupport268_007 ridgeSupport268_suffix_008 ridgeSupport268_007_decode ridgeSupport268_suffix_decode_008
theorem ridgeSupport268_suffix_decode_006 : PackedRawNatGrowth.readList 14 71 ridgeSupport268_rest_006 =
    (ridgeSupport268_suffix_006, ridgeSupport268_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 39
    ridgeSupport268_rest_006 ridgeSupport268_rest_007 ridgeSupport268_rest_009
    ridgeSupport268_006 ridgeSupport268_suffix_007 ridgeSupport268_006_decode ridgeSupport268_suffix_decode_007
theorem ridgeSupport268_suffix_decode_005 : PackedRawNatGrowth.readList 14 103 ridgeSupport268_rest_005 =
    (ridgeSupport268_suffix_005, ridgeSupport268_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 71
    ridgeSupport268_rest_005 ridgeSupport268_rest_006 ridgeSupport268_rest_009
    ridgeSupport268_005 ridgeSupport268_suffix_006 ridgeSupport268_005_decode ridgeSupport268_suffix_decode_006
theorem ridgeSupport268_suffix_decode_004 : PackedRawNatGrowth.readList 14 135 ridgeSupport268_rest_004 =
    (ridgeSupport268_suffix_004, ridgeSupport268_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 103
    ridgeSupport268_rest_004 ridgeSupport268_rest_005 ridgeSupport268_rest_009
    ridgeSupport268_004 ridgeSupport268_suffix_005 ridgeSupport268_004_decode ridgeSupport268_suffix_decode_005
theorem ridgeSupport268_suffix_decode_003 : PackedRawNatGrowth.readList 14 167 ridgeSupport268_rest_003 =
    (ridgeSupport268_suffix_003, ridgeSupport268_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 135
    ridgeSupport268_rest_003 ridgeSupport268_rest_004 ridgeSupport268_rest_009
    ridgeSupport268_003 ridgeSupport268_suffix_004 ridgeSupport268_003_decode ridgeSupport268_suffix_decode_004
theorem ridgeSupport268_suffix_decode_002 : PackedRawNatGrowth.readList 14 199 ridgeSupport268_rest_002 =
    (ridgeSupport268_suffix_002, ridgeSupport268_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 167
    ridgeSupport268_rest_002 ridgeSupport268_rest_003 ridgeSupport268_rest_009
    ridgeSupport268_002 ridgeSupport268_suffix_003 ridgeSupport268_002_decode ridgeSupport268_suffix_decode_003
theorem ridgeSupport268_suffix_decode_001 : PackedRawNatGrowth.readList 14 231 ridgeSupport268_rest_001 =
    (ridgeSupport268_suffix_001, ridgeSupport268_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 199
    ridgeSupport268_rest_001 ridgeSupport268_rest_002 ridgeSupport268_rest_009
    ridgeSupport268_001 ridgeSupport268_suffix_002 ridgeSupport268_001_decode ridgeSupport268_suffix_decode_002
theorem ridgeSupport268_suffix_decode_000 : PackedRawNatGrowth.readList 14 263 ridgeSupport268_rest_000 =
    (ridgeSupport268_suffix_000, ridgeSupport268_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 231
    ridgeSupport268_rest_000 ridgeSupport268_rest_001 ridgeSupport268_rest_009
    ridgeSupport268_000 ridgeSupport268_suffix_001 ridgeSupport268_000_decode ridgeSupport268_suffix_decode_001
theorem ridgeSupport268_eq : candidateRows 268 = ridgeSupport268_suffix_000 := by
  change candidateSupports 268 = ridgeSupport268_suffix_000
  rw [ridgeSupport268_source]
  exact congrArg Prod.fst ridgeSupport268_suffix_decode_000
theorem ridgeTest_large_268 : ridgeTest 268 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport268_eq]
    simp only [ridgeSupport268_suffix_000, ridgeSupport268_suffix_001, ridgeSupport268_suffix_002, ridgeSupport268_suffix_003, ridgeSupport268_suffix_004, ridgeSupport268_suffix_005, ridgeSupport268_suffix_006, ridgeSupport268_suffix_007, ridgeSupport268_suffix_008, ridgeSupport268_suffix_009, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport268_000_mask, ridgeSupport268_001_mask, ridgeSupport268_002_mask, ridgeSupport268_003_mask, ridgeSupport268_004_mask, ridgeSupport268_005_mask, ridgeSupport268_006_mask, ridgeSupport268_007_mask, ridgeSupport268_008_mask]
    decide +kernel
  · rw [ridgeSupport268_eq]
    simp only [ridgeSupport268_suffix_000, ridgeSupport268_suffix_001, ridgeSupport268_suffix_002, ridgeSupport268_suffix_003, ridgeSupport268_suffix_004, ridgeSupport268_suffix_005, ridgeSupport268_suffix_006, ridgeSupport268_suffix_007, ridgeSupport268_suffix_008, ridgeSupport268_suffix_009, List.all_append, List.all_nil, ridgeSupport268_000_checked, ridgeSupport268_001_checked, ridgeSupport268_002_checked, ridgeSupport268_003_checked, ridgeSupport268_004_checked, ridgeSupport268_005_checked, ridgeSupport268_006_checked, ridgeSupport268_007_checked, ridgeSupport268_008_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixExtra00
