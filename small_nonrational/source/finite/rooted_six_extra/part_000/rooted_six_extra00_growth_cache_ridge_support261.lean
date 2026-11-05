module
prelude
public import RootedSixExtra00GrowthCacheRidgeSupport261Part000
public import RootedSixExtra00GrowthCacheRidgeSupport261Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra00
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport261_suffix_decode_009 : PackedRawNatGrowth.readList 14 0 ridgeSupport261_rest_009 =
    (ridgeSupport261_suffix_009, ridgeSupport261_rest_009) := by rfl
theorem ridgeSupport261_suffix_decode_008 : PackedRawNatGrowth.readList 14 7 ridgeSupport261_rest_008 =
    (ridgeSupport261_suffix_008, ridgeSupport261_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 7 0
    ridgeSupport261_rest_008 ridgeSupport261_rest_009 ridgeSupport261_rest_009
    ridgeSupport261_008 ridgeSupport261_suffix_009 ridgeSupport261_008_decode ridgeSupport261_suffix_decode_009
theorem ridgeSupport261_suffix_decode_007 : PackedRawNatGrowth.readList 14 39 ridgeSupport261_rest_007 =
    (ridgeSupport261_suffix_007, ridgeSupport261_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 7
    ridgeSupport261_rest_007 ridgeSupport261_rest_008 ridgeSupport261_rest_009
    ridgeSupport261_007 ridgeSupport261_suffix_008 ridgeSupport261_007_decode ridgeSupport261_suffix_decode_008
theorem ridgeSupport261_suffix_decode_006 : PackedRawNatGrowth.readList 14 71 ridgeSupport261_rest_006 =
    (ridgeSupport261_suffix_006, ridgeSupport261_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 39
    ridgeSupport261_rest_006 ridgeSupport261_rest_007 ridgeSupport261_rest_009
    ridgeSupport261_006 ridgeSupport261_suffix_007 ridgeSupport261_006_decode ridgeSupport261_suffix_decode_007
theorem ridgeSupport261_suffix_decode_005 : PackedRawNatGrowth.readList 14 103 ridgeSupport261_rest_005 =
    (ridgeSupport261_suffix_005, ridgeSupport261_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 71
    ridgeSupport261_rest_005 ridgeSupport261_rest_006 ridgeSupport261_rest_009
    ridgeSupport261_005 ridgeSupport261_suffix_006 ridgeSupport261_005_decode ridgeSupport261_suffix_decode_006
theorem ridgeSupport261_suffix_decode_004 : PackedRawNatGrowth.readList 14 135 ridgeSupport261_rest_004 =
    (ridgeSupport261_suffix_004, ridgeSupport261_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 103
    ridgeSupport261_rest_004 ridgeSupport261_rest_005 ridgeSupport261_rest_009
    ridgeSupport261_004 ridgeSupport261_suffix_005 ridgeSupport261_004_decode ridgeSupport261_suffix_decode_005
theorem ridgeSupport261_suffix_decode_003 : PackedRawNatGrowth.readList 14 167 ridgeSupport261_rest_003 =
    (ridgeSupport261_suffix_003, ridgeSupport261_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 135
    ridgeSupport261_rest_003 ridgeSupport261_rest_004 ridgeSupport261_rest_009
    ridgeSupport261_003 ridgeSupport261_suffix_004 ridgeSupport261_003_decode ridgeSupport261_suffix_decode_004
theorem ridgeSupport261_suffix_decode_002 : PackedRawNatGrowth.readList 14 199 ridgeSupport261_rest_002 =
    (ridgeSupport261_suffix_002, ridgeSupport261_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 167
    ridgeSupport261_rest_002 ridgeSupport261_rest_003 ridgeSupport261_rest_009
    ridgeSupport261_002 ridgeSupport261_suffix_003 ridgeSupport261_002_decode ridgeSupport261_suffix_decode_003
theorem ridgeSupport261_suffix_decode_001 : PackedRawNatGrowth.readList 14 231 ridgeSupport261_rest_001 =
    (ridgeSupport261_suffix_001, ridgeSupport261_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 199
    ridgeSupport261_rest_001 ridgeSupport261_rest_002 ridgeSupport261_rest_009
    ridgeSupport261_001 ridgeSupport261_suffix_002 ridgeSupport261_001_decode ridgeSupport261_suffix_decode_002
theorem ridgeSupport261_suffix_decode_000 : PackedRawNatGrowth.readList 14 263 ridgeSupport261_rest_000 =
    (ridgeSupport261_suffix_000, ridgeSupport261_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 231
    ridgeSupport261_rest_000 ridgeSupport261_rest_001 ridgeSupport261_rest_009
    ridgeSupport261_000 ridgeSupport261_suffix_001 ridgeSupport261_000_decode ridgeSupport261_suffix_decode_001
theorem ridgeSupport261_eq : candidateRows 261 = ridgeSupport261_suffix_000 := by
  change candidateSupports 261 = ridgeSupport261_suffix_000
  rw [ridgeSupport261_source]
  exact congrArg Prod.fst ridgeSupport261_suffix_decode_000
theorem ridgeTest_large_261 : ridgeTest 261 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport261_eq]
    simp only [ridgeSupport261_suffix_000, ridgeSupport261_suffix_001, ridgeSupport261_suffix_002, ridgeSupport261_suffix_003, ridgeSupport261_suffix_004, ridgeSupport261_suffix_005, ridgeSupport261_suffix_006, ridgeSupport261_suffix_007, ridgeSupport261_suffix_008, ridgeSupport261_suffix_009, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport261_000_mask, ridgeSupport261_001_mask, ridgeSupport261_002_mask, ridgeSupport261_003_mask, ridgeSupport261_004_mask, ridgeSupport261_005_mask, ridgeSupport261_006_mask, ridgeSupport261_007_mask, ridgeSupport261_008_mask]
    decide +kernel
  · rw [ridgeSupport261_eq]
    simp only [ridgeSupport261_suffix_000, ridgeSupport261_suffix_001, ridgeSupport261_suffix_002, ridgeSupport261_suffix_003, ridgeSupport261_suffix_004, ridgeSupport261_suffix_005, ridgeSupport261_suffix_006, ridgeSupport261_suffix_007, ridgeSupport261_suffix_008, ridgeSupport261_suffix_009, List.all_append, List.all_nil, ridgeSupport261_000_checked, ridgeSupport261_001_checked, ridgeSupport261_002_checked, ridgeSupport261_003_checked, ridgeSupport261_004_checked, ridgeSupport261_005_checked, ridgeSupport261_006_checked, ridgeSupport261_007_checked, ridgeSupport261_008_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixExtra00
