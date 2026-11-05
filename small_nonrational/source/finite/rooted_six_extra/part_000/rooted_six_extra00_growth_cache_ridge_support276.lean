module
prelude
public import RootedSixExtra00GrowthCacheRidgeSupport276Part000
public import RootedSixExtra00GrowthCacheRidgeSupport276Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra00
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport276_suffix_decode_009 : PackedRawNatGrowth.readList 14 0 ridgeSupport276_rest_009 =
    (ridgeSupport276_suffix_009, ridgeSupport276_rest_009) := by rfl
theorem ridgeSupport276_suffix_decode_008 : PackedRawNatGrowth.readList 14 7 ridgeSupport276_rest_008 =
    (ridgeSupport276_suffix_008, ridgeSupport276_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 7 0
    ridgeSupport276_rest_008 ridgeSupport276_rest_009 ridgeSupport276_rest_009
    ridgeSupport276_008 ridgeSupport276_suffix_009 ridgeSupport276_008_decode ridgeSupport276_suffix_decode_009
theorem ridgeSupport276_suffix_decode_007 : PackedRawNatGrowth.readList 14 39 ridgeSupport276_rest_007 =
    (ridgeSupport276_suffix_007, ridgeSupport276_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 7
    ridgeSupport276_rest_007 ridgeSupport276_rest_008 ridgeSupport276_rest_009
    ridgeSupport276_007 ridgeSupport276_suffix_008 ridgeSupport276_007_decode ridgeSupport276_suffix_decode_008
theorem ridgeSupport276_suffix_decode_006 : PackedRawNatGrowth.readList 14 71 ridgeSupport276_rest_006 =
    (ridgeSupport276_suffix_006, ridgeSupport276_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 39
    ridgeSupport276_rest_006 ridgeSupport276_rest_007 ridgeSupport276_rest_009
    ridgeSupport276_006 ridgeSupport276_suffix_007 ridgeSupport276_006_decode ridgeSupport276_suffix_decode_007
theorem ridgeSupport276_suffix_decode_005 : PackedRawNatGrowth.readList 14 103 ridgeSupport276_rest_005 =
    (ridgeSupport276_suffix_005, ridgeSupport276_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 71
    ridgeSupport276_rest_005 ridgeSupport276_rest_006 ridgeSupport276_rest_009
    ridgeSupport276_005 ridgeSupport276_suffix_006 ridgeSupport276_005_decode ridgeSupport276_suffix_decode_006
theorem ridgeSupport276_suffix_decode_004 : PackedRawNatGrowth.readList 14 135 ridgeSupport276_rest_004 =
    (ridgeSupport276_suffix_004, ridgeSupport276_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 103
    ridgeSupport276_rest_004 ridgeSupport276_rest_005 ridgeSupport276_rest_009
    ridgeSupport276_004 ridgeSupport276_suffix_005 ridgeSupport276_004_decode ridgeSupport276_suffix_decode_005
theorem ridgeSupport276_suffix_decode_003 : PackedRawNatGrowth.readList 14 167 ridgeSupport276_rest_003 =
    (ridgeSupport276_suffix_003, ridgeSupport276_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 135
    ridgeSupport276_rest_003 ridgeSupport276_rest_004 ridgeSupport276_rest_009
    ridgeSupport276_003 ridgeSupport276_suffix_004 ridgeSupport276_003_decode ridgeSupport276_suffix_decode_004
theorem ridgeSupport276_suffix_decode_002 : PackedRawNatGrowth.readList 14 199 ridgeSupport276_rest_002 =
    (ridgeSupport276_suffix_002, ridgeSupport276_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 167
    ridgeSupport276_rest_002 ridgeSupport276_rest_003 ridgeSupport276_rest_009
    ridgeSupport276_002 ridgeSupport276_suffix_003 ridgeSupport276_002_decode ridgeSupport276_suffix_decode_003
theorem ridgeSupport276_suffix_decode_001 : PackedRawNatGrowth.readList 14 231 ridgeSupport276_rest_001 =
    (ridgeSupport276_suffix_001, ridgeSupport276_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 199
    ridgeSupport276_rest_001 ridgeSupport276_rest_002 ridgeSupport276_rest_009
    ridgeSupport276_001 ridgeSupport276_suffix_002 ridgeSupport276_001_decode ridgeSupport276_suffix_decode_002
theorem ridgeSupport276_suffix_decode_000 : PackedRawNatGrowth.readList 14 263 ridgeSupport276_rest_000 =
    (ridgeSupport276_suffix_000, ridgeSupport276_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 231
    ridgeSupport276_rest_000 ridgeSupport276_rest_001 ridgeSupport276_rest_009
    ridgeSupport276_000 ridgeSupport276_suffix_001 ridgeSupport276_000_decode ridgeSupport276_suffix_decode_001
theorem ridgeSupport276_eq : candidateRows 276 = ridgeSupport276_suffix_000 := by
  change candidateSupports 276 = ridgeSupport276_suffix_000
  rw [ridgeSupport276_source]
  exact congrArg Prod.fst ridgeSupport276_suffix_decode_000
theorem ridgeTest_large_276 : ridgeTest 276 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport276_eq]
    simp only [ridgeSupport276_suffix_000, ridgeSupport276_suffix_001, ridgeSupport276_suffix_002, ridgeSupport276_suffix_003, ridgeSupport276_suffix_004, ridgeSupport276_suffix_005, ridgeSupport276_suffix_006, ridgeSupport276_suffix_007, ridgeSupport276_suffix_008, ridgeSupport276_suffix_009, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport276_000_mask, ridgeSupport276_001_mask, ridgeSupport276_002_mask, ridgeSupport276_003_mask, ridgeSupport276_004_mask, ridgeSupport276_005_mask, ridgeSupport276_006_mask, ridgeSupport276_007_mask, ridgeSupport276_008_mask]
    decide +kernel
  · rw [ridgeSupport276_eq]
    simp only [ridgeSupport276_suffix_000, ridgeSupport276_suffix_001, ridgeSupport276_suffix_002, ridgeSupport276_suffix_003, ridgeSupport276_suffix_004, ridgeSupport276_suffix_005, ridgeSupport276_suffix_006, ridgeSupport276_suffix_007, ridgeSupport276_suffix_008, ridgeSupport276_suffix_009, List.all_append, List.all_nil, ridgeSupport276_000_checked, ridgeSupport276_001_checked, ridgeSupport276_002_checked, ridgeSupport276_003_checked, ridgeSupport276_004_checked, ridgeSupport276_005_checked, ridgeSupport276_006_checked, ridgeSupport276_007_checked, ridgeSupport276_008_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixExtra00
