module
prelude
public import RootedSixExtra00GrowthCacheRidgeSupport292Part000
public import RootedSixExtra00GrowthCacheRidgeSupport292Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra00
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport292_suffix_decode_009 : PackedRawNatGrowth.readList 14 0 ridgeSupport292_rest_009 =
    (ridgeSupport292_suffix_009, ridgeSupport292_rest_009) := by rfl
theorem ridgeSupport292_suffix_decode_008 : PackedRawNatGrowth.readList 14 7 ridgeSupport292_rest_008 =
    (ridgeSupport292_suffix_008, ridgeSupport292_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 7 0
    ridgeSupport292_rest_008 ridgeSupport292_rest_009 ridgeSupport292_rest_009
    ridgeSupport292_008 ridgeSupport292_suffix_009 ridgeSupport292_008_decode ridgeSupport292_suffix_decode_009
theorem ridgeSupport292_suffix_decode_007 : PackedRawNatGrowth.readList 14 39 ridgeSupport292_rest_007 =
    (ridgeSupport292_suffix_007, ridgeSupport292_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 7
    ridgeSupport292_rest_007 ridgeSupport292_rest_008 ridgeSupport292_rest_009
    ridgeSupport292_007 ridgeSupport292_suffix_008 ridgeSupport292_007_decode ridgeSupport292_suffix_decode_008
theorem ridgeSupport292_suffix_decode_006 : PackedRawNatGrowth.readList 14 71 ridgeSupport292_rest_006 =
    (ridgeSupport292_suffix_006, ridgeSupport292_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 39
    ridgeSupport292_rest_006 ridgeSupport292_rest_007 ridgeSupport292_rest_009
    ridgeSupport292_006 ridgeSupport292_suffix_007 ridgeSupport292_006_decode ridgeSupport292_suffix_decode_007
theorem ridgeSupport292_suffix_decode_005 : PackedRawNatGrowth.readList 14 103 ridgeSupport292_rest_005 =
    (ridgeSupport292_suffix_005, ridgeSupport292_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 71
    ridgeSupport292_rest_005 ridgeSupport292_rest_006 ridgeSupport292_rest_009
    ridgeSupport292_005 ridgeSupport292_suffix_006 ridgeSupport292_005_decode ridgeSupport292_suffix_decode_006
theorem ridgeSupport292_suffix_decode_004 : PackedRawNatGrowth.readList 14 135 ridgeSupport292_rest_004 =
    (ridgeSupport292_suffix_004, ridgeSupport292_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 103
    ridgeSupport292_rest_004 ridgeSupport292_rest_005 ridgeSupport292_rest_009
    ridgeSupport292_004 ridgeSupport292_suffix_005 ridgeSupport292_004_decode ridgeSupport292_suffix_decode_005
theorem ridgeSupport292_suffix_decode_003 : PackedRawNatGrowth.readList 14 167 ridgeSupport292_rest_003 =
    (ridgeSupport292_suffix_003, ridgeSupport292_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 135
    ridgeSupport292_rest_003 ridgeSupport292_rest_004 ridgeSupport292_rest_009
    ridgeSupport292_003 ridgeSupport292_suffix_004 ridgeSupport292_003_decode ridgeSupport292_suffix_decode_004
theorem ridgeSupport292_suffix_decode_002 : PackedRawNatGrowth.readList 14 199 ridgeSupport292_rest_002 =
    (ridgeSupport292_suffix_002, ridgeSupport292_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 167
    ridgeSupport292_rest_002 ridgeSupport292_rest_003 ridgeSupport292_rest_009
    ridgeSupport292_002 ridgeSupport292_suffix_003 ridgeSupport292_002_decode ridgeSupport292_suffix_decode_003
theorem ridgeSupport292_suffix_decode_001 : PackedRawNatGrowth.readList 14 231 ridgeSupport292_rest_001 =
    (ridgeSupport292_suffix_001, ridgeSupport292_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 199
    ridgeSupport292_rest_001 ridgeSupport292_rest_002 ridgeSupport292_rest_009
    ridgeSupport292_001 ridgeSupport292_suffix_002 ridgeSupport292_001_decode ridgeSupport292_suffix_decode_002
theorem ridgeSupport292_suffix_decode_000 : PackedRawNatGrowth.readList 14 263 ridgeSupport292_rest_000 =
    (ridgeSupport292_suffix_000, ridgeSupport292_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 231
    ridgeSupport292_rest_000 ridgeSupport292_rest_001 ridgeSupport292_rest_009
    ridgeSupport292_000 ridgeSupport292_suffix_001 ridgeSupport292_000_decode ridgeSupport292_suffix_decode_001
theorem ridgeSupport292_eq : candidateRows 292 = ridgeSupport292_suffix_000 := by
  change candidateSupports 292 = ridgeSupport292_suffix_000
  rw [ridgeSupport292_source]
  exact congrArg Prod.fst ridgeSupport292_suffix_decode_000
theorem ridgeTest_large_292 : ridgeTest 292 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport292_eq]
    simp only [ridgeSupport292_suffix_000, ridgeSupport292_suffix_001, ridgeSupport292_suffix_002, ridgeSupport292_suffix_003, ridgeSupport292_suffix_004, ridgeSupport292_suffix_005, ridgeSupport292_suffix_006, ridgeSupport292_suffix_007, ridgeSupport292_suffix_008, ridgeSupport292_suffix_009, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport292_000_mask, ridgeSupport292_001_mask, ridgeSupport292_002_mask, ridgeSupport292_003_mask, ridgeSupport292_004_mask, ridgeSupport292_005_mask, ridgeSupport292_006_mask, ridgeSupport292_007_mask, ridgeSupport292_008_mask]
    decide +kernel
  · rw [ridgeSupport292_eq]
    simp only [ridgeSupport292_suffix_000, ridgeSupport292_suffix_001, ridgeSupport292_suffix_002, ridgeSupport292_suffix_003, ridgeSupport292_suffix_004, ridgeSupport292_suffix_005, ridgeSupport292_suffix_006, ridgeSupport292_suffix_007, ridgeSupport292_suffix_008, ridgeSupport292_suffix_009, List.all_append, List.all_nil, ridgeSupport292_000_checked, ridgeSupport292_001_checked, ridgeSupport292_002_checked, ridgeSupport292_003_checked, ridgeSupport292_004_checked, ridgeSupport292_005_checked, ridgeSupport292_006_checked, ridgeSupport292_007_checked, ridgeSupport292_008_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixExtra00
