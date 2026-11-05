module
prelude
public import RootedSixExtra00GrowthCacheRidgeSupport530Part000
public import RootedSixExtra00GrowthCacheRidgeSupport530Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra00
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport530_suffix_decode_009 : PackedRawNatGrowth.readList 14 0 ridgeSupport530_rest_009 =
    (ridgeSupport530_suffix_009, ridgeSupport530_rest_009) := by rfl
theorem ridgeSupport530_suffix_decode_008 : PackedRawNatGrowth.readList 14 7 ridgeSupport530_rest_008 =
    (ridgeSupport530_suffix_008, ridgeSupport530_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 7 0
    ridgeSupport530_rest_008 ridgeSupport530_rest_009 ridgeSupport530_rest_009
    ridgeSupport530_008 ridgeSupport530_suffix_009 ridgeSupport530_008_decode ridgeSupport530_suffix_decode_009
theorem ridgeSupport530_suffix_decode_007 : PackedRawNatGrowth.readList 14 39 ridgeSupport530_rest_007 =
    (ridgeSupport530_suffix_007, ridgeSupport530_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 7
    ridgeSupport530_rest_007 ridgeSupport530_rest_008 ridgeSupport530_rest_009
    ridgeSupport530_007 ridgeSupport530_suffix_008 ridgeSupport530_007_decode ridgeSupport530_suffix_decode_008
theorem ridgeSupport530_suffix_decode_006 : PackedRawNatGrowth.readList 14 71 ridgeSupport530_rest_006 =
    (ridgeSupport530_suffix_006, ridgeSupport530_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 39
    ridgeSupport530_rest_006 ridgeSupport530_rest_007 ridgeSupport530_rest_009
    ridgeSupport530_006 ridgeSupport530_suffix_007 ridgeSupport530_006_decode ridgeSupport530_suffix_decode_007
theorem ridgeSupport530_suffix_decode_005 : PackedRawNatGrowth.readList 14 103 ridgeSupport530_rest_005 =
    (ridgeSupport530_suffix_005, ridgeSupport530_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 71
    ridgeSupport530_rest_005 ridgeSupport530_rest_006 ridgeSupport530_rest_009
    ridgeSupport530_005 ridgeSupport530_suffix_006 ridgeSupport530_005_decode ridgeSupport530_suffix_decode_006
theorem ridgeSupport530_suffix_decode_004 : PackedRawNatGrowth.readList 14 135 ridgeSupport530_rest_004 =
    (ridgeSupport530_suffix_004, ridgeSupport530_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 103
    ridgeSupport530_rest_004 ridgeSupport530_rest_005 ridgeSupport530_rest_009
    ridgeSupport530_004 ridgeSupport530_suffix_005 ridgeSupport530_004_decode ridgeSupport530_suffix_decode_005
theorem ridgeSupport530_suffix_decode_003 : PackedRawNatGrowth.readList 14 167 ridgeSupport530_rest_003 =
    (ridgeSupport530_suffix_003, ridgeSupport530_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 135
    ridgeSupport530_rest_003 ridgeSupport530_rest_004 ridgeSupport530_rest_009
    ridgeSupport530_003 ridgeSupport530_suffix_004 ridgeSupport530_003_decode ridgeSupport530_suffix_decode_004
theorem ridgeSupport530_suffix_decode_002 : PackedRawNatGrowth.readList 14 199 ridgeSupport530_rest_002 =
    (ridgeSupport530_suffix_002, ridgeSupport530_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 167
    ridgeSupport530_rest_002 ridgeSupport530_rest_003 ridgeSupport530_rest_009
    ridgeSupport530_002 ridgeSupport530_suffix_003 ridgeSupport530_002_decode ridgeSupport530_suffix_decode_003
theorem ridgeSupport530_suffix_decode_001 : PackedRawNatGrowth.readList 14 231 ridgeSupport530_rest_001 =
    (ridgeSupport530_suffix_001, ridgeSupport530_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 199
    ridgeSupport530_rest_001 ridgeSupport530_rest_002 ridgeSupport530_rest_009
    ridgeSupport530_001 ridgeSupport530_suffix_002 ridgeSupport530_001_decode ridgeSupport530_suffix_decode_002
theorem ridgeSupport530_suffix_decode_000 : PackedRawNatGrowth.readList 14 263 ridgeSupport530_rest_000 =
    (ridgeSupport530_suffix_000, ridgeSupport530_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 231
    ridgeSupport530_rest_000 ridgeSupport530_rest_001 ridgeSupport530_rest_009
    ridgeSupport530_000 ridgeSupport530_suffix_001 ridgeSupport530_000_decode ridgeSupport530_suffix_decode_001
theorem ridgeSupport530_eq : candidateRows 530 = ridgeSupport530_suffix_000 := by
  change candidateSupports 530 = ridgeSupport530_suffix_000
  rw [ridgeSupport530_source]
  exact congrArg Prod.fst ridgeSupport530_suffix_decode_000
theorem ridgeTest_large_530 : ridgeTest 530 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport530_eq]
    simp only [ridgeSupport530_suffix_000, ridgeSupport530_suffix_001, ridgeSupport530_suffix_002, ridgeSupport530_suffix_003, ridgeSupport530_suffix_004, ridgeSupport530_suffix_005, ridgeSupport530_suffix_006, ridgeSupport530_suffix_007, ridgeSupport530_suffix_008, ridgeSupport530_suffix_009, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport530_000_mask, ridgeSupport530_001_mask, ridgeSupport530_002_mask, ridgeSupport530_003_mask, ridgeSupport530_004_mask, ridgeSupport530_005_mask, ridgeSupport530_006_mask, ridgeSupport530_007_mask, ridgeSupport530_008_mask]
    decide +kernel
  · rw [ridgeSupport530_eq]
    simp only [ridgeSupport530_suffix_000, ridgeSupport530_suffix_001, ridgeSupport530_suffix_002, ridgeSupport530_suffix_003, ridgeSupport530_suffix_004, ridgeSupport530_suffix_005, ridgeSupport530_suffix_006, ridgeSupport530_suffix_007, ridgeSupport530_suffix_008, ridgeSupport530_suffix_009, List.all_append, List.all_nil, ridgeSupport530_000_checked, ridgeSupport530_001_checked, ridgeSupport530_002_checked, ridgeSupport530_003_checked, ridgeSupport530_004_checked, ridgeSupport530_005_checked, ridgeSupport530_006_checked, ridgeSupport530_007_checked, ridgeSupport530_008_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixExtra00
