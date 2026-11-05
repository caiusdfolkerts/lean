module
prelude
public import RootedSixExtra00GrowthCacheRidgeSupport274Part000
public import RootedSixExtra00GrowthCacheRidgeSupport274Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra00
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport274_suffix_decode_009 : PackedRawNatGrowth.readList 14 0 ridgeSupport274_rest_009 =
    (ridgeSupport274_suffix_009, ridgeSupport274_rest_009) := by rfl
theorem ridgeSupport274_suffix_decode_008 : PackedRawNatGrowth.readList 14 7 ridgeSupport274_rest_008 =
    (ridgeSupport274_suffix_008, ridgeSupport274_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 7 0
    ridgeSupport274_rest_008 ridgeSupport274_rest_009 ridgeSupport274_rest_009
    ridgeSupport274_008 ridgeSupport274_suffix_009 ridgeSupport274_008_decode ridgeSupport274_suffix_decode_009
theorem ridgeSupport274_suffix_decode_007 : PackedRawNatGrowth.readList 14 39 ridgeSupport274_rest_007 =
    (ridgeSupport274_suffix_007, ridgeSupport274_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 7
    ridgeSupport274_rest_007 ridgeSupport274_rest_008 ridgeSupport274_rest_009
    ridgeSupport274_007 ridgeSupport274_suffix_008 ridgeSupport274_007_decode ridgeSupport274_suffix_decode_008
theorem ridgeSupport274_suffix_decode_006 : PackedRawNatGrowth.readList 14 71 ridgeSupport274_rest_006 =
    (ridgeSupport274_suffix_006, ridgeSupport274_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 39
    ridgeSupport274_rest_006 ridgeSupport274_rest_007 ridgeSupport274_rest_009
    ridgeSupport274_006 ridgeSupport274_suffix_007 ridgeSupport274_006_decode ridgeSupport274_suffix_decode_007
theorem ridgeSupport274_suffix_decode_005 : PackedRawNatGrowth.readList 14 103 ridgeSupport274_rest_005 =
    (ridgeSupport274_suffix_005, ridgeSupport274_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 71
    ridgeSupport274_rest_005 ridgeSupport274_rest_006 ridgeSupport274_rest_009
    ridgeSupport274_005 ridgeSupport274_suffix_006 ridgeSupport274_005_decode ridgeSupport274_suffix_decode_006
theorem ridgeSupport274_suffix_decode_004 : PackedRawNatGrowth.readList 14 135 ridgeSupport274_rest_004 =
    (ridgeSupport274_suffix_004, ridgeSupport274_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 103
    ridgeSupport274_rest_004 ridgeSupport274_rest_005 ridgeSupport274_rest_009
    ridgeSupport274_004 ridgeSupport274_suffix_005 ridgeSupport274_004_decode ridgeSupport274_suffix_decode_005
theorem ridgeSupport274_suffix_decode_003 : PackedRawNatGrowth.readList 14 167 ridgeSupport274_rest_003 =
    (ridgeSupport274_suffix_003, ridgeSupport274_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 135
    ridgeSupport274_rest_003 ridgeSupport274_rest_004 ridgeSupport274_rest_009
    ridgeSupport274_003 ridgeSupport274_suffix_004 ridgeSupport274_003_decode ridgeSupport274_suffix_decode_004
theorem ridgeSupport274_suffix_decode_002 : PackedRawNatGrowth.readList 14 199 ridgeSupport274_rest_002 =
    (ridgeSupport274_suffix_002, ridgeSupport274_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 167
    ridgeSupport274_rest_002 ridgeSupport274_rest_003 ridgeSupport274_rest_009
    ridgeSupport274_002 ridgeSupport274_suffix_003 ridgeSupport274_002_decode ridgeSupport274_suffix_decode_003
theorem ridgeSupport274_suffix_decode_001 : PackedRawNatGrowth.readList 14 231 ridgeSupport274_rest_001 =
    (ridgeSupport274_suffix_001, ridgeSupport274_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 199
    ridgeSupport274_rest_001 ridgeSupport274_rest_002 ridgeSupport274_rest_009
    ridgeSupport274_001 ridgeSupport274_suffix_002 ridgeSupport274_001_decode ridgeSupport274_suffix_decode_002
theorem ridgeSupport274_suffix_decode_000 : PackedRawNatGrowth.readList 14 263 ridgeSupport274_rest_000 =
    (ridgeSupport274_suffix_000, ridgeSupport274_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 231
    ridgeSupport274_rest_000 ridgeSupport274_rest_001 ridgeSupport274_rest_009
    ridgeSupport274_000 ridgeSupport274_suffix_001 ridgeSupport274_000_decode ridgeSupport274_suffix_decode_001
theorem ridgeSupport274_eq : candidateRows 274 = ridgeSupport274_suffix_000 := by
  change candidateSupports 274 = ridgeSupport274_suffix_000
  rw [ridgeSupport274_source]
  exact congrArg Prod.fst ridgeSupport274_suffix_decode_000
theorem ridgeTest_large_274 : ridgeTest 274 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport274_eq]
    simp only [ridgeSupport274_suffix_000, ridgeSupport274_suffix_001, ridgeSupport274_suffix_002, ridgeSupport274_suffix_003, ridgeSupport274_suffix_004, ridgeSupport274_suffix_005, ridgeSupport274_suffix_006, ridgeSupport274_suffix_007, ridgeSupport274_suffix_008, ridgeSupport274_suffix_009, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport274_000_mask, ridgeSupport274_001_mask, ridgeSupport274_002_mask, ridgeSupport274_003_mask, ridgeSupport274_004_mask, ridgeSupport274_005_mask, ridgeSupport274_006_mask, ridgeSupport274_007_mask, ridgeSupport274_008_mask]
    decide +kernel
  · rw [ridgeSupport274_eq]
    simp only [ridgeSupport274_suffix_000, ridgeSupport274_suffix_001, ridgeSupport274_suffix_002, ridgeSupport274_suffix_003, ridgeSupport274_suffix_004, ridgeSupport274_suffix_005, ridgeSupport274_suffix_006, ridgeSupport274_suffix_007, ridgeSupport274_suffix_008, ridgeSupport274_suffix_009, List.all_append, List.all_nil, ridgeSupport274_000_checked, ridgeSupport274_001_checked, ridgeSupport274_002_checked, ridgeSupport274_003_checked, ridgeSupport274_004_checked, ridgeSupport274_005_checked, ridgeSupport274_006_checked, ridgeSupport274_007_checked, ridgeSupport274_008_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixExtra00
