module
prelude
public import RootedSixExtra00GrowthCacheRidgeSupport521Part000
public import RootedSixExtra00GrowthCacheRidgeSupport521Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra00
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport521_suffix_decode_009 : PackedRawNatGrowth.readList 14 0 ridgeSupport521_rest_009 =
    (ridgeSupport521_suffix_009, ridgeSupport521_rest_009) := by rfl
theorem ridgeSupport521_suffix_decode_008 : PackedRawNatGrowth.readList 14 7 ridgeSupport521_rest_008 =
    (ridgeSupport521_suffix_008, ridgeSupport521_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 7 0
    ridgeSupport521_rest_008 ridgeSupport521_rest_009 ridgeSupport521_rest_009
    ridgeSupport521_008 ridgeSupport521_suffix_009 ridgeSupport521_008_decode ridgeSupport521_suffix_decode_009
theorem ridgeSupport521_suffix_decode_007 : PackedRawNatGrowth.readList 14 39 ridgeSupport521_rest_007 =
    (ridgeSupport521_suffix_007, ridgeSupport521_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 7
    ridgeSupport521_rest_007 ridgeSupport521_rest_008 ridgeSupport521_rest_009
    ridgeSupport521_007 ridgeSupport521_suffix_008 ridgeSupport521_007_decode ridgeSupport521_suffix_decode_008
theorem ridgeSupport521_suffix_decode_006 : PackedRawNatGrowth.readList 14 71 ridgeSupport521_rest_006 =
    (ridgeSupport521_suffix_006, ridgeSupport521_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 39
    ridgeSupport521_rest_006 ridgeSupport521_rest_007 ridgeSupport521_rest_009
    ridgeSupport521_006 ridgeSupport521_suffix_007 ridgeSupport521_006_decode ridgeSupport521_suffix_decode_007
theorem ridgeSupport521_suffix_decode_005 : PackedRawNatGrowth.readList 14 103 ridgeSupport521_rest_005 =
    (ridgeSupport521_suffix_005, ridgeSupport521_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 71
    ridgeSupport521_rest_005 ridgeSupport521_rest_006 ridgeSupport521_rest_009
    ridgeSupport521_005 ridgeSupport521_suffix_006 ridgeSupport521_005_decode ridgeSupport521_suffix_decode_006
theorem ridgeSupport521_suffix_decode_004 : PackedRawNatGrowth.readList 14 135 ridgeSupport521_rest_004 =
    (ridgeSupport521_suffix_004, ridgeSupport521_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 103
    ridgeSupport521_rest_004 ridgeSupport521_rest_005 ridgeSupport521_rest_009
    ridgeSupport521_004 ridgeSupport521_suffix_005 ridgeSupport521_004_decode ridgeSupport521_suffix_decode_005
theorem ridgeSupport521_suffix_decode_003 : PackedRawNatGrowth.readList 14 167 ridgeSupport521_rest_003 =
    (ridgeSupport521_suffix_003, ridgeSupport521_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 135
    ridgeSupport521_rest_003 ridgeSupport521_rest_004 ridgeSupport521_rest_009
    ridgeSupport521_003 ridgeSupport521_suffix_004 ridgeSupport521_003_decode ridgeSupport521_suffix_decode_004
theorem ridgeSupport521_suffix_decode_002 : PackedRawNatGrowth.readList 14 199 ridgeSupport521_rest_002 =
    (ridgeSupport521_suffix_002, ridgeSupport521_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 167
    ridgeSupport521_rest_002 ridgeSupport521_rest_003 ridgeSupport521_rest_009
    ridgeSupport521_002 ridgeSupport521_suffix_003 ridgeSupport521_002_decode ridgeSupport521_suffix_decode_003
theorem ridgeSupport521_suffix_decode_001 : PackedRawNatGrowth.readList 14 231 ridgeSupport521_rest_001 =
    (ridgeSupport521_suffix_001, ridgeSupport521_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 199
    ridgeSupport521_rest_001 ridgeSupport521_rest_002 ridgeSupport521_rest_009
    ridgeSupport521_001 ridgeSupport521_suffix_002 ridgeSupport521_001_decode ridgeSupport521_suffix_decode_002
theorem ridgeSupport521_suffix_decode_000 : PackedRawNatGrowth.readList 14 263 ridgeSupport521_rest_000 =
    (ridgeSupport521_suffix_000, ridgeSupport521_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 231
    ridgeSupport521_rest_000 ridgeSupport521_rest_001 ridgeSupport521_rest_009
    ridgeSupport521_000 ridgeSupport521_suffix_001 ridgeSupport521_000_decode ridgeSupport521_suffix_decode_001
theorem ridgeSupport521_eq : candidateRows 521 = ridgeSupport521_suffix_000 := by
  change candidateSupports 521 = ridgeSupport521_suffix_000
  rw [ridgeSupport521_source]
  exact congrArg Prod.fst ridgeSupport521_suffix_decode_000
theorem ridgeTest_large_521 : ridgeTest 521 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport521_eq]
    simp only [ridgeSupport521_suffix_000, ridgeSupport521_suffix_001, ridgeSupport521_suffix_002, ridgeSupport521_suffix_003, ridgeSupport521_suffix_004, ridgeSupport521_suffix_005, ridgeSupport521_suffix_006, ridgeSupport521_suffix_007, ridgeSupport521_suffix_008, ridgeSupport521_suffix_009, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport521_000_mask, ridgeSupport521_001_mask, ridgeSupport521_002_mask, ridgeSupport521_003_mask, ridgeSupport521_004_mask, ridgeSupport521_005_mask, ridgeSupport521_006_mask, ridgeSupport521_007_mask, ridgeSupport521_008_mask]
    decide +kernel
  · rw [ridgeSupport521_eq]
    simp only [ridgeSupport521_suffix_000, ridgeSupport521_suffix_001, ridgeSupport521_suffix_002, ridgeSupport521_suffix_003, ridgeSupport521_suffix_004, ridgeSupport521_suffix_005, ridgeSupport521_suffix_006, ridgeSupport521_suffix_007, ridgeSupport521_suffix_008, ridgeSupport521_suffix_009, List.all_append, List.all_nil, ridgeSupport521_000_checked, ridgeSupport521_001_checked, ridgeSupport521_002_checked, ridgeSupport521_003_checked, ridgeSupport521_004_checked, ridgeSupport521_005_checked, ridgeSupport521_006_checked, ridgeSupport521_007_checked, ridgeSupport521_008_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixExtra00
