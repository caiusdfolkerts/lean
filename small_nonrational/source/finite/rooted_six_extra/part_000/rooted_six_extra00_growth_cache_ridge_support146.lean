module
prelude
public import RootedSixExtra00GrowthCacheRidgeSupport146Part000
public import RootedSixExtra00GrowthCacheRidgeSupport146Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra00
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport146_suffix_decode_009 : PackedRawNatGrowth.readList 14 0 ridgeSupport146_rest_009 =
    (ridgeSupport146_suffix_009, ridgeSupport146_rest_009) := by rfl
theorem ridgeSupport146_suffix_decode_008 : PackedRawNatGrowth.readList 14 7 ridgeSupport146_rest_008 =
    (ridgeSupport146_suffix_008, ridgeSupport146_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 7 0
    ridgeSupport146_rest_008 ridgeSupport146_rest_009 ridgeSupport146_rest_009
    ridgeSupport146_008 ridgeSupport146_suffix_009 ridgeSupport146_008_decode ridgeSupport146_suffix_decode_009
theorem ridgeSupport146_suffix_decode_007 : PackedRawNatGrowth.readList 14 39 ridgeSupport146_rest_007 =
    (ridgeSupport146_suffix_007, ridgeSupport146_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 7
    ridgeSupport146_rest_007 ridgeSupport146_rest_008 ridgeSupport146_rest_009
    ridgeSupport146_007 ridgeSupport146_suffix_008 ridgeSupport146_007_decode ridgeSupport146_suffix_decode_008
theorem ridgeSupport146_suffix_decode_006 : PackedRawNatGrowth.readList 14 71 ridgeSupport146_rest_006 =
    (ridgeSupport146_suffix_006, ridgeSupport146_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 39
    ridgeSupport146_rest_006 ridgeSupport146_rest_007 ridgeSupport146_rest_009
    ridgeSupport146_006 ridgeSupport146_suffix_007 ridgeSupport146_006_decode ridgeSupport146_suffix_decode_007
theorem ridgeSupport146_suffix_decode_005 : PackedRawNatGrowth.readList 14 103 ridgeSupport146_rest_005 =
    (ridgeSupport146_suffix_005, ridgeSupport146_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 71
    ridgeSupport146_rest_005 ridgeSupport146_rest_006 ridgeSupport146_rest_009
    ridgeSupport146_005 ridgeSupport146_suffix_006 ridgeSupport146_005_decode ridgeSupport146_suffix_decode_006
theorem ridgeSupport146_suffix_decode_004 : PackedRawNatGrowth.readList 14 135 ridgeSupport146_rest_004 =
    (ridgeSupport146_suffix_004, ridgeSupport146_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 103
    ridgeSupport146_rest_004 ridgeSupport146_rest_005 ridgeSupport146_rest_009
    ridgeSupport146_004 ridgeSupport146_suffix_005 ridgeSupport146_004_decode ridgeSupport146_suffix_decode_005
theorem ridgeSupport146_suffix_decode_003 : PackedRawNatGrowth.readList 14 167 ridgeSupport146_rest_003 =
    (ridgeSupport146_suffix_003, ridgeSupport146_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 135
    ridgeSupport146_rest_003 ridgeSupport146_rest_004 ridgeSupport146_rest_009
    ridgeSupport146_003 ridgeSupport146_suffix_004 ridgeSupport146_003_decode ridgeSupport146_suffix_decode_004
theorem ridgeSupport146_suffix_decode_002 : PackedRawNatGrowth.readList 14 199 ridgeSupport146_rest_002 =
    (ridgeSupport146_suffix_002, ridgeSupport146_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 167
    ridgeSupport146_rest_002 ridgeSupport146_rest_003 ridgeSupport146_rest_009
    ridgeSupport146_002 ridgeSupport146_suffix_003 ridgeSupport146_002_decode ridgeSupport146_suffix_decode_003
theorem ridgeSupport146_suffix_decode_001 : PackedRawNatGrowth.readList 14 231 ridgeSupport146_rest_001 =
    (ridgeSupport146_suffix_001, ridgeSupport146_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 199
    ridgeSupport146_rest_001 ridgeSupport146_rest_002 ridgeSupport146_rest_009
    ridgeSupport146_001 ridgeSupport146_suffix_002 ridgeSupport146_001_decode ridgeSupport146_suffix_decode_002
theorem ridgeSupport146_suffix_decode_000 : PackedRawNatGrowth.readList 14 263 ridgeSupport146_rest_000 =
    (ridgeSupport146_suffix_000, ridgeSupport146_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 231
    ridgeSupport146_rest_000 ridgeSupport146_rest_001 ridgeSupport146_rest_009
    ridgeSupport146_000 ridgeSupport146_suffix_001 ridgeSupport146_000_decode ridgeSupport146_suffix_decode_001
theorem ridgeSupport146_eq : candidateRows 146 = ridgeSupport146_suffix_000 := by
  change candidateSupports 146 = ridgeSupport146_suffix_000
  rw [ridgeSupport146_source]
  exact congrArg Prod.fst ridgeSupport146_suffix_decode_000
theorem ridgeTest_large_146 : ridgeTest 146 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport146_eq]
    simp only [ridgeSupport146_suffix_000, ridgeSupport146_suffix_001, ridgeSupport146_suffix_002, ridgeSupport146_suffix_003, ridgeSupport146_suffix_004, ridgeSupport146_suffix_005, ridgeSupport146_suffix_006, ridgeSupport146_suffix_007, ridgeSupport146_suffix_008, ridgeSupport146_suffix_009, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport146_000_mask, ridgeSupport146_001_mask, ridgeSupport146_002_mask, ridgeSupport146_003_mask, ridgeSupport146_004_mask, ridgeSupport146_005_mask, ridgeSupport146_006_mask, ridgeSupport146_007_mask, ridgeSupport146_008_mask]
    decide +kernel
  · rw [ridgeSupport146_eq]
    simp only [ridgeSupport146_suffix_000, ridgeSupport146_suffix_001, ridgeSupport146_suffix_002, ridgeSupport146_suffix_003, ridgeSupport146_suffix_004, ridgeSupport146_suffix_005, ridgeSupport146_suffix_006, ridgeSupport146_suffix_007, ridgeSupport146_suffix_008, ridgeSupport146_suffix_009, List.all_append, List.all_nil, ridgeSupport146_000_checked, ridgeSupport146_001_checked, ridgeSupport146_002_checked, ridgeSupport146_003_checked, ridgeSupport146_004_checked, ridgeSupport146_005_checked, ridgeSupport146_006_checked, ridgeSupport146_007_checked, ridgeSupport146_008_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixExtra00
