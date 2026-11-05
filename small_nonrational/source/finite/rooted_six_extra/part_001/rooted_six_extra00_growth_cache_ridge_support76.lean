module
prelude
public import RootedSixExtra00GrowthCacheRidgeSupport76Part000
public import RootedSixExtra00GrowthCacheRidgeSupport76Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra00
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport76_suffix_decode_009 : PackedRawNatGrowth.readList 14 0 ridgeSupport76_rest_009 =
    (ridgeSupport76_suffix_009, ridgeSupport76_rest_009) := by rfl
theorem ridgeSupport76_suffix_decode_008 : PackedRawNatGrowth.readList 14 7 ridgeSupport76_rest_008 =
    (ridgeSupport76_suffix_008, ridgeSupport76_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 7 0
    ridgeSupport76_rest_008 ridgeSupport76_rest_009 ridgeSupport76_rest_009
    ridgeSupport76_008 ridgeSupport76_suffix_009 ridgeSupport76_008_decode ridgeSupport76_suffix_decode_009
theorem ridgeSupport76_suffix_decode_007 : PackedRawNatGrowth.readList 14 39 ridgeSupport76_rest_007 =
    (ridgeSupport76_suffix_007, ridgeSupport76_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 7
    ridgeSupport76_rest_007 ridgeSupport76_rest_008 ridgeSupport76_rest_009
    ridgeSupport76_007 ridgeSupport76_suffix_008 ridgeSupport76_007_decode ridgeSupport76_suffix_decode_008
theorem ridgeSupport76_suffix_decode_006 : PackedRawNatGrowth.readList 14 71 ridgeSupport76_rest_006 =
    (ridgeSupport76_suffix_006, ridgeSupport76_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 39
    ridgeSupport76_rest_006 ridgeSupport76_rest_007 ridgeSupport76_rest_009
    ridgeSupport76_006 ridgeSupport76_suffix_007 ridgeSupport76_006_decode ridgeSupport76_suffix_decode_007
theorem ridgeSupport76_suffix_decode_005 : PackedRawNatGrowth.readList 14 103 ridgeSupport76_rest_005 =
    (ridgeSupport76_suffix_005, ridgeSupport76_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 71
    ridgeSupport76_rest_005 ridgeSupport76_rest_006 ridgeSupport76_rest_009
    ridgeSupport76_005 ridgeSupport76_suffix_006 ridgeSupport76_005_decode ridgeSupport76_suffix_decode_006
theorem ridgeSupport76_suffix_decode_004 : PackedRawNatGrowth.readList 14 135 ridgeSupport76_rest_004 =
    (ridgeSupport76_suffix_004, ridgeSupport76_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 103
    ridgeSupport76_rest_004 ridgeSupport76_rest_005 ridgeSupport76_rest_009
    ridgeSupport76_004 ridgeSupport76_suffix_005 ridgeSupport76_004_decode ridgeSupport76_suffix_decode_005
theorem ridgeSupport76_suffix_decode_003 : PackedRawNatGrowth.readList 14 167 ridgeSupport76_rest_003 =
    (ridgeSupport76_suffix_003, ridgeSupport76_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 135
    ridgeSupport76_rest_003 ridgeSupport76_rest_004 ridgeSupport76_rest_009
    ridgeSupport76_003 ridgeSupport76_suffix_004 ridgeSupport76_003_decode ridgeSupport76_suffix_decode_004
theorem ridgeSupport76_suffix_decode_002 : PackedRawNatGrowth.readList 14 199 ridgeSupport76_rest_002 =
    (ridgeSupport76_suffix_002, ridgeSupport76_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 167
    ridgeSupport76_rest_002 ridgeSupport76_rest_003 ridgeSupport76_rest_009
    ridgeSupport76_002 ridgeSupport76_suffix_003 ridgeSupport76_002_decode ridgeSupport76_suffix_decode_003
theorem ridgeSupport76_suffix_decode_001 : PackedRawNatGrowth.readList 14 231 ridgeSupport76_rest_001 =
    (ridgeSupport76_suffix_001, ridgeSupport76_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 199
    ridgeSupport76_rest_001 ridgeSupport76_rest_002 ridgeSupport76_rest_009
    ridgeSupport76_001 ridgeSupport76_suffix_002 ridgeSupport76_001_decode ridgeSupport76_suffix_decode_002
theorem ridgeSupport76_suffix_decode_000 : PackedRawNatGrowth.readList 14 263 ridgeSupport76_rest_000 =
    (ridgeSupport76_suffix_000, ridgeSupport76_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 231
    ridgeSupport76_rest_000 ridgeSupport76_rest_001 ridgeSupport76_rest_009
    ridgeSupport76_000 ridgeSupport76_suffix_001 ridgeSupport76_000_decode ridgeSupport76_suffix_decode_001
theorem ridgeSupport76_eq : candidateRows 76 = ridgeSupport76_suffix_000 := by
  change candidateSupports 76 = ridgeSupport76_suffix_000
  rw [ridgeSupport76_source]
  exact congrArg Prod.fst ridgeSupport76_suffix_decode_000
theorem ridgeTest_large_76 : ridgeTest 76 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport76_eq]
    simp only [ridgeSupport76_suffix_000, ridgeSupport76_suffix_001, ridgeSupport76_suffix_002, ridgeSupport76_suffix_003, ridgeSupport76_suffix_004, ridgeSupport76_suffix_005, ridgeSupport76_suffix_006, ridgeSupport76_suffix_007, ridgeSupport76_suffix_008, ridgeSupport76_suffix_009, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport76_000_mask, ridgeSupport76_001_mask, ridgeSupport76_002_mask, ridgeSupport76_003_mask, ridgeSupport76_004_mask, ridgeSupport76_005_mask, ridgeSupport76_006_mask, ridgeSupport76_007_mask, ridgeSupport76_008_mask]
    decide +kernel
  · rw [ridgeSupport76_eq]
    simp only [ridgeSupport76_suffix_000, ridgeSupport76_suffix_001, ridgeSupport76_suffix_002, ridgeSupport76_suffix_003, ridgeSupport76_suffix_004, ridgeSupport76_suffix_005, ridgeSupport76_suffix_006, ridgeSupport76_suffix_007, ridgeSupport76_suffix_008, ridgeSupport76_suffix_009, List.all_append, List.all_nil, ridgeSupport76_000_checked, ridgeSupport76_001_checked, ridgeSupport76_002_checked, ridgeSupport76_003_checked, ridgeSupport76_004_checked, ridgeSupport76_005_checked, ridgeSupport76_006_checked, ridgeSupport76_007_checked, ridgeSupport76_008_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixExtra00
