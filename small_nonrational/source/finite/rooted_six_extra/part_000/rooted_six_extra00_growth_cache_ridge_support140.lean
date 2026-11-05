module
prelude
public import RootedSixExtra00GrowthCacheRidgeSupport140Part000
public import RootedSixExtra00GrowthCacheRidgeSupport140Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra00
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport140_suffix_decode_009 : PackedRawNatGrowth.readList 14 0 ridgeSupport140_rest_009 =
    (ridgeSupport140_suffix_009, ridgeSupport140_rest_009) := by rfl
theorem ridgeSupport140_suffix_decode_008 : PackedRawNatGrowth.readList 14 7 ridgeSupport140_rest_008 =
    (ridgeSupport140_suffix_008, ridgeSupport140_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 7 0
    ridgeSupport140_rest_008 ridgeSupport140_rest_009 ridgeSupport140_rest_009
    ridgeSupport140_008 ridgeSupport140_suffix_009 ridgeSupport140_008_decode ridgeSupport140_suffix_decode_009
theorem ridgeSupport140_suffix_decode_007 : PackedRawNatGrowth.readList 14 39 ridgeSupport140_rest_007 =
    (ridgeSupport140_suffix_007, ridgeSupport140_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 7
    ridgeSupport140_rest_007 ridgeSupport140_rest_008 ridgeSupport140_rest_009
    ridgeSupport140_007 ridgeSupport140_suffix_008 ridgeSupport140_007_decode ridgeSupport140_suffix_decode_008
theorem ridgeSupport140_suffix_decode_006 : PackedRawNatGrowth.readList 14 71 ridgeSupport140_rest_006 =
    (ridgeSupport140_suffix_006, ridgeSupport140_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 39
    ridgeSupport140_rest_006 ridgeSupport140_rest_007 ridgeSupport140_rest_009
    ridgeSupport140_006 ridgeSupport140_suffix_007 ridgeSupport140_006_decode ridgeSupport140_suffix_decode_007
theorem ridgeSupport140_suffix_decode_005 : PackedRawNatGrowth.readList 14 103 ridgeSupport140_rest_005 =
    (ridgeSupport140_suffix_005, ridgeSupport140_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 71
    ridgeSupport140_rest_005 ridgeSupport140_rest_006 ridgeSupport140_rest_009
    ridgeSupport140_005 ridgeSupport140_suffix_006 ridgeSupport140_005_decode ridgeSupport140_suffix_decode_006
theorem ridgeSupport140_suffix_decode_004 : PackedRawNatGrowth.readList 14 135 ridgeSupport140_rest_004 =
    (ridgeSupport140_suffix_004, ridgeSupport140_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 103
    ridgeSupport140_rest_004 ridgeSupport140_rest_005 ridgeSupport140_rest_009
    ridgeSupport140_004 ridgeSupport140_suffix_005 ridgeSupport140_004_decode ridgeSupport140_suffix_decode_005
theorem ridgeSupport140_suffix_decode_003 : PackedRawNatGrowth.readList 14 167 ridgeSupport140_rest_003 =
    (ridgeSupport140_suffix_003, ridgeSupport140_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 135
    ridgeSupport140_rest_003 ridgeSupport140_rest_004 ridgeSupport140_rest_009
    ridgeSupport140_003 ridgeSupport140_suffix_004 ridgeSupport140_003_decode ridgeSupport140_suffix_decode_004
theorem ridgeSupport140_suffix_decode_002 : PackedRawNatGrowth.readList 14 199 ridgeSupport140_rest_002 =
    (ridgeSupport140_suffix_002, ridgeSupport140_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 167
    ridgeSupport140_rest_002 ridgeSupport140_rest_003 ridgeSupport140_rest_009
    ridgeSupport140_002 ridgeSupport140_suffix_003 ridgeSupport140_002_decode ridgeSupport140_suffix_decode_003
theorem ridgeSupport140_suffix_decode_001 : PackedRawNatGrowth.readList 14 231 ridgeSupport140_rest_001 =
    (ridgeSupport140_suffix_001, ridgeSupport140_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 199
    ridgeSupport140_rest_001 ridgeSupport140_rest_002 ridgeSupport140_rest_009
    ridgeSupport140_001 ridgeSupport140_suffix_002 ridgeSupport140_001_decode ridgeSupport140_suffix_decode_002
theorem ridgeSupport140_suffix_decode_000 : PackedRawNatGrowth.readList 14 263 ridgeSupport140_rest_000 =
    (ridgeSupport140_suffix_000, ridgeSupport140_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 231
    ridgeSupport140_rest_000 ridgeSupport140_rest_001 ridgeSupport140_rest_009
    ridgeSupport140_000 ridgeSupport140_suffix_001 ridgeSupport140_000_decode ridgeSupport140_suffix_decode_001
theorem ridgeSupport140_eq : candidateRows 140 = ridgeSupport140_suffix_000 := by
  change candidateSupports 140 = ridgeSupport140_suffix_000
  rw [ridgeSupport140_source]
  exact congrArg Prod.fst ridgeSupport140_suffix_decode_000
theorem ridgeTest_large_140 : ridgeTest 140 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport140_eq]
    simp only [ridgeSupport140_suffix_000, ridgeSupport140_suffix_001, ridgeSupport140_suffix_002, ridgeSupport140_suffix_003, ridgeSupport140_suffix_004, ridgeSupport140_suffix_005, ridgeSupport140_suffix_006, ridgeSupport140_suffix_007, ridgeSupport140_suffix_008, ridgeSupport140_suffix_009, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport140_000_mask, ridgeSupport140_001_mask, ridgeSupport140_002_mask, ridgeSupport140_003_mask, ridgeSupport140_004_mask, ridgeSupport140_005_mask, ridgeSupport140_006_mask, ridgeSupport140_007_mask, ridgeSupport140_008_mask]
    decide +kernel
  · rw [ridgeSupport140_eq]
    simp only [ridgeSupport140_suffix_000, ridgeSupport140_suffix_001, ridgeSupport140_suffix_002, ridgeSupport140_suffix_003, ridgeSupport140_suffix_004, ridgeSupport140_suffix_005, ridgeSupport140_suffix_006, ridgeSupport140_suffix_007, ridgeSupport140_suffix_008, ridgeSupport140_suffix_009, List.all_append, List.all_nil, ridgeSupport140_000_checked, ridgeSupport140_001_checked, ridgeSupport140_002_checked, ridgeSupport140_003_checked, ridgeSupport140_004_checked, ridgeSupport140_005_checked, ridgeSupport140_006_checked, ridgeSupport140_007_checked, ridgeSupport140_008_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixExtra00
