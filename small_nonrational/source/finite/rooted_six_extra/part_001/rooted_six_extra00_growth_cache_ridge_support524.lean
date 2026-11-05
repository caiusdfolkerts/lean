module
prelude
public import RootedSixExtra00GrowthCacheRidgeSupport524Part000
public import RootedSixExtra00GrowthCacheRidgeSupport524Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra00
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport524_suffix_decode_009 : PackedRawNatGrowth.readList 14 0 ridgeSupport524_rest_009 =
    (ridgeSupport524_suffix_009, ridgeSupport524_rest_009) := by rfl
theorem ridgeSupport524_suffix_decode_008 : PackedRawNatGrowth.readList 14 7 ridgeSupport524_rest_008 =
    (ridgeSupport524_suffix_008, ridgeSupport524_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 7 0
    ridgeSupport524_rest_008 ridgeSupport524_rest_009 ridgeSupport524_rest_009
    ridgeSupport524_008 ridgeSupport524_suffix_009 ridgeSupport524_008_decode ridgeSupport524_suffix_decode_009
theorem ridgeSupport524_suffix_decode_007 : PackedRawNatGrowth.readList 14 39 ridgeSupport524_rest_007 =
    (ridgeSupport524_suffix_007, ridgeSupport524_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 7
    ridgeSupport524_rest_007 ridgeSupport524_rest_008 ridgeSupport524_rest_009
    ridgeSupport524_007 ridgeSupport524_suffix_008 ridgeSupport524_007_decode ridgeSupport524_suffix_decode_008
theorem ridgeSupport524_suffix_decode_006 : PackedRawNatGrowth.readList 14 71 ridgeSupport524_rest_006 =
    (ridgeSupport524_suffix_006, ridgeSupport524_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 39
    ridgeSupport524_rest_006 ridgeSupport524_rest_007 ridgeSupport524_rest_009
    ridgeSupport524_006 ridgeSupport524_suffix_007 ridgeSupport524_006_decode ridgeSupport524_suffix_decode_007
theorem ridgeSupport524_suffix_decode_005 : PackedRawNatGrowth.readList 14 103 ridgeSupport524_rest_005 =
    (ridgeSupport524_suffix_005, ridgeSupport524_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 71
    ridgeSupport524_rest_005 ridgeSupport524_rest_006 ridgeSupport524_rest_009
    ridgeSupport524_005 ridgeSupport524_suffix_006 ridgeSupport524_005_decode ridgeSupport524_suffix_decode_006
theorem ridgeSupport524_suffix_decode_004 : PackedRawNatGrowth.readList 14 135 ridgeSupport524_rest_004 =
    (ridgeSupport524_suffix_004, ridgeSupport524_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 103
    ridgeSupport524_rest_004 ridgeSupport524_rest_005 ridgeSupport524_rest_009
    ridgeSupport524_004 ridgeSupport524_suffix_005 ridgeSupport524_004_decode ridgeSupport524_suffix_decode_005
theorem ridgeSupport524_suffix_decode_003 : PackedRawNatGrowth.readList 14 167 ridgeSupport524_rest_003 =
    (ridgeSupport524_suffix_003, ridgeSupport524_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 135
    ridgeSupport524_rest_003 ridgeSupport524_rest_004 ridgeSupport524_rest_009
    ridgeSupport524_003 ridgeSupport524_suffix_004 ridgeSupport524_003_decode ridgeSupport524_suffix_decode_004
theorem ridgeSupport524_suffix_decode_002 : PackedRawNatGrowth.readList 14 199 ridgeSupport524_rest_002 =
    (ridgeSupport524_suffix_002, ridgeSupport524_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 167
    ridgeSupport524_rest_002 ridgeSupport524_rest_003 ridgeSupport524_rest_009
    ridgeSupport524_002 ridgeSupport524_suffix_003 ridgeSupport524_002_decode ridgeSupport524_suffix_decode_003
theorem ridgeSupport524_suffix_decode_001 : PackedRawNatGrowth.readList 14 231 ridgeSupport524_rest_001 =
    (ridgeSupport524_suffix_001, ridgeSupport524_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 199
    ridgeSupport524_rest_001 ridgeSupport524_rest_002 ridgeSupport524_rest_009
    ridgeSupport524_001 ridgeSupport524_suffix_002 ridgeSupport524_001_decode ridgeSupport524_suffix_decode_002
theorem ridgeSupport524_suffix_decode_000 : PackedRawNatGrowth.readList 14 263 ridgeSupport524_rest_000 =
    (ridgeSupport524_suffix_000, ridgeSupport524_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 231
    ridgeSupport524_rest_000 ridgeSupport524_rest_001 ridgeSupport524_rest_009
    ridgeSupport524_000 ridgeSupport524_suffix_001 ridgeSupport524_000_decode ridgeSupport524_suffix_decode_001
theorem ridgeSupport524_eq : candidateRows 524 = ridgeSupport524_suffix_000 := by
  change candidateSupports 524 = ridgeSupport524_suffix_000
  rw [ridgeSupport524_source]
  exact congrArg Prod.fst ridgeSupport524_suffix_decode_000
theorem ridgeTest_large_524 : ridgeTest 524 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport524_eq]
    simp only [ridgeSupport524_suffix_000, ridgeSupport524_suffix_001, ridgeSupport524_suffix_002, ridgeSupport524_suffix_003, ridgeSupport524_suffix_004, ridgeSupport524_suffix_005, ridgeSupport524_suffix_006, ridgeSupport524_suffix_007, ridgeSupport524_suffix_008, ridgeSupport524_suffix_009, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport524_000_mask, ridgeSupport524_001_mask, ridgeSupport524_002_mask, ridgeSupport524_003_mask, ridgeSupport524_004_mask, ridgeSupport524_005_mask, ridgeSupport524_006_mask, ridgeSupport524_007_mask, ridgeSupport524_008_mask]
    decide +kernel
  · rw [ridgeSupport524_eq]
    simp only [ridgeSupport524_suffix_000, ridgeSupport524_suffix_001, ridgeSupport524_suffix_002, ridgeSupport524_suffix_003, ridgeSupport524_suffix_004, ridgeSupport524_suffix_005, ridgeSupport524_suffix_006, ridgeSupport524_suffix_007, ridgeSupport524_suffix_008, ridgeSupport524_suffix_009, List.all_append, List.all_nil, ridgeSupport524_000_checked, ridgeSupport524_001_checked, ridgeSupport524_002_checked, ridgeSupport524_003_checked, ridgeSupport524_004_checked, ridgeSupport524_005_checked, ridgeSupport524_006_checked, ridgeSupport524_007_checked, ridgeSupport524_008_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixExtra00
