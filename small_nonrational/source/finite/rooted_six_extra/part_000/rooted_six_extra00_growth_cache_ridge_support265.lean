module
prelude
public import RootedSixExtra00GrowthCacheRidgeSupport265Part000
public import RootedSixExtra00GrowthCacheRidgeSupport265Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra00
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport265_suffix_decode_009 : PackedRawNatGrowth.readList 14 0 ridgeSupport265_rest_009 =
    (ridgeSupport265_suffix_009, ridgeSupport265_rest_009) := by rfl
theorem ridgeSupport265_suffix_decode_008 : PackedRawNatGrowth.readList 14 7 ridgeSupport265_rest_008 =
    (ridgeSupport265_suffix_008, ridgeSupport265_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 7 0
    ridgeSupport265_rest_008 ridgeSupport265_rest_009 ridgeSupport265_rest_009
    ridgeSupport265_008 ridgeSupport265_suffix_009 ridgeSupport265_008_decode ridgeSupport265_suffix_decode_009
theorem ridgeSupport265_suffix_decode_007 : PackedRawNatGrowth.readList 14 39 ridgeSupport265_rest_007 =
    (ridgeSupport265_suffix_007, ridgeSupport265_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 7
    ridgeSupport265_rest_007 ridgeSupport265_rest_008 ridgeSupport265_rest_009
    ridgeSupport265_007 ridgeSupport265_suffix_008 ridgeSupport265_007_decode ridgeSupport265_suffix_decode_008
theorem ridgeSupport265_suffix_decode_006 : PackedRawNatGrowth.readList 14 71 ridgeSupport265_rest_006 =
    (ridgeSupport265_suffix_006, ridgeSupport265_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 39
    ridgeSupport265_rest_006 ridgeSupport265_rest_007 ridgeSupport265_rest_009
    ridgeSupport265_006 ridgeSupport265_suffix_007 ridgeSupport265_006_decode ridgeSupport265_suffix_decode_007
theorem ridgeSupport265_suffix_decode_005 : PackedRawNatGrowth.readList 14 103 ridgeSupport265_rest_005 =
    (ridgeSupport265_suffix_005, ridgeSupport265_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 71
    ridgeSupport265_rest_005 ridgeSupport265_rest_006 ridgeSupport265_rest_009
    ridgeSupport265_005 ridgeSupport265_suffix_006 ridgeSupport265_005_decode ridgeSupport265_suffix_decode_006
theorem ridgeSupport265_suffix_decode_004 : PackedRawNatGrowth.readList 14 135 ridgeSupport265_rest_004 =
    (ridgeSupport265_suffix_004, ridgeSupport265_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 103
    ridgeSupport265_rest_004 ridgeSupport265_rest_005 ridgeSupport265_rest_009
    ridgeSupport265_004 ridgeSupport265_suffix_005 ridgeSupport265_004_decode ridgeSupport265_suffix_decode_005
theorem ridgeSupport265_suffix_decode_003 : PackedRawNatGrowth.readList 14 167 ridgeSupport265_rest_003 =
    (ridgeSupport265_suffix_003, ridgeSupport265_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 135
    ridgeSupport265_rest_003 ridgeSupport265_rest_004 ridgeSupport265_rest_009
    ridgeSupport265_003 ridgeSupport265_suffix_004 ridgeSupport265_003_decode ridgeSupport265_suffix_decode_004
theorem ridgeSupport265_suffix_decode_002 : PackedRawNatGrowth.readList 14 199 ridgeSupport265_rest_002 =
    (ridgeSupport265_suffix_002, ridgeSupport265_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 167
    ridgeSupport265_rest_002 ridgeSupport265_rest_003 ridgeSupport265_rest_009
    ridgeSupport265_002 ridgeSupport265_suffix_003 ridgeSupport265_002_decode ridgeSupport265_suffix_decode_003
theorem ridgeSupport265_suffix_decode_001 : PackedRawNatGrowth.readList 14 231 ridgeSupport265_rest_001 =
    (ridgeSupport265_suffix_001, ridgeSupport265_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 199
    ridgeSupport265_rest_001 ridgeSupport265_rest_002 ridgeSupport265_rest_009
    ridgeSupport265_001 ridgeSupport265_suffix_002 ridgeSupport265_001_decode ridgeSupport265_suffix_decode_002
theorem ridgeSupport265_suffix_decode_000 : PackedRawNatGrowth.readList 14 263 ridgeSupport265_rest_000 =
    (ridgeSupport265_suffix_000, ridgeSupport265_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 231
    ridgeSupport265_rest_000 ridgeSupport265_rest_001 ridgeSupport265_rest_009
    ridgeSupport265_000 ridgeSupport265_suffix_001 ridgeSupport265_000_decode ridgeSupport265_suffix_decode_001
theorem ridgeSupport265_eq : candidateRows 265 = ridgeSupport265_suffix_000 := by
  change candidateSupports 265 = ridgeSupport265_suffix_000
  rw [ridgeSupport265_source]
  exact congrArg Prod.fst ridgeSupport265_suffix_decode_000
theorem ridgeTest_large_265 : ridgeTest 265 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport265_eq]
    simp only [ridgeSupport265_suffix_000, ridgeSupport265_suffix_001, ridgeSupport265_suffix_002, ridgeSupport265_suffix_003, ridgeSupport265_suffix_004, ridgeSupport265_suffix_005, ridgeSupport265_suffix_006, ridgeSupport265_suffix_007, ridgeSupport265_suffix_008, ridgeSupport265_suffix_009, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport265_000_mask, ridgeSupport265_001_mask, ridgeSupport265_002_mask, ridgeSupport265_003_mask, ridgeSupport265_004_mask, ridgeSupport265_005_mask, ridgeSupport265_006_mask, ridgeSupport265_007_mask, ridgeSupport265_008_mask]
    decide +kernel
  · rw [ridgeSupport265_eq]
    simp only [ridgeSupport265_suffix_000, ridgeSupport265_suffix_001, ridgeSupport265_suffix_002, ridgeSupport265_suffix_003, ridgeSupport265_suffix_004, ridgeSupport265_suffix_005, ridgeSupport265_suffix_006, ridgeSupport265_suffix_007, ridgeSupport265_suffix_008, ridgeSupport265_suffix_009, List.all_append, List.all_nil, ridgeSupport265_000_checked, ridgeSupport265_001_checked, ridgeSupport265_002_checked, ridgeSupport265_003_checked, ridgeSupport265_004_checked, ridgeSupport265_005_checked, ridgeSupport265_006_checked, ridgeSupport265_007_checked, ridgeSupport265_008_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixExtra00
