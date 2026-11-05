module
prelude
public import RootedSixExtra00GrowthCacheRidgeSupport560Part000
public import RootedSixExtra00GrowthCacheRidgeSupport560Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra00
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport560_suffix_decode_009 : PackedRawNatGrowth.readList 14 0 ridgeSupport560_rest_009 =
    (ridgeSupport560_suffix_009, ridgeSupport560_rest_009) := by rfl
theorem ridgeSupport560_suffix_decode_008 : PackedRawNatGrowth.readList 14 7 ridgeSupport560_rest_008 =
    (ridgeSupport560_suffix_008, ridgeSupport560_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 7 0
    ridgeSupport560_rest_008 ridgeSupport560_rest_009 ridgeSupport560_rest_009
    ridgeSupport560_008 ridgeSupport560_suffix_009 ridgeSupport560_008_decode ridgeSupport560_suffix_decode_009
theorem ridgeSupport560_suffix_decode_007 : PackedRawNatGrowth.readList 14 39 ridgeSupport560_rest_007 =
    (ridgeSupport560_suffix_007, ridgeSupport560_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 7
    ridgeSupport560_rest_007 ridgeSupport560_rest_008 ridgeSupport560_rest_009
    ridgeSupport560_007 ridgeSupport560_suffix_008 ridgeSupport560_007_decode ridgeSupport560_suffix_decode_008
theorem ridgeSupport560_suffix_decode_006 : PackedRawNatGrowth.readList 14 71 ridgeSupport560_rest_006 =
    (ridgeSupport560_suffix_006, ridgeSupport560_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 39
    ridgeSupport560_rest_006 ridgeSupport560_rest_007 ridgeSupport560_rest_009
    ridgeSupport560_006 ridgeSupport560_suffix_007 ridgeSupport560_006_decode ridgeSupport560_suffix_decode_007
theorem ridgeSupport560_suffix_decode_005 : PackedRawNatGrowth.readList 14 103 ridgeSupport560_rest_005 =
    (ridgeSupport560_suffix_005, ridgeSupport560_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 71
    ridgeSupport560_rest_005 ridgeSupport560_rest_006 ridgeSupport560_rest_009
    ridgeSupport560_005 ridgeSupport560_suffix_006 ridgeSupport560_005_decode ridgeSupport560_suffix_decode_006
theorem ridgeSupport560_suffix_decode_004 : PackedRawNatGrowth.readList 14 135 ridgeSupport560_rest_004 =
    (ridgeSupport560_suffix_004, ridgeSupport560_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 103
    ridgeSupport560_rest_004 ridgeSupport560_rest_005 ridgeSupport560_rest_009
    ridgeSupport560_004 ridgeSupport560_suffix_005 ridgeSupport560_004_decode ridgeSupport560_suffix_decode_005
theorem ridgeSupport560_suffix_decode_003 : PackedRawNatGrowth.readList 14 167 ridgeSupport560_rest_003 =
    (ridgeSupport560_suffix_003, ridgeSupport560_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 135
    ridgeSupport560_rest_003 ridgeSupport560_rest_004 ridgeSupport560_rest_009
    ridgeSupport560_003 ridgeSupport560_suffix_004 ridgeSupport560_003_decode ridgeSupport560_suffix_decode_004
theorem ridgeSupport560_suffix_decode_002 : PackedRawNatGrowth.readList 14 199 ridgeSupport560_rest_002 =
    (ridgeSupport560_suffix_002, ridgeSupport560_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 167
    ridgeSupport560_rest_002 ridgeSupport560_rest_003 ridgeSupport560_rest_009
    ridgeSupport560_002 ridgeSupport560_suffix_003 ridgeSupport560_002_decode ridgeSupport560_suffix_decode_003
theorem ridgeSupport560_suffix_decode_001 : PackedRawNatGrowth.readList 14 231 ridgeSupport560_rest_001 =
    (ridgeSupport560_suffix_001, ridgeSupport560_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 199
    ridgeSupport560_rest_001 ridgeSupport560_rest_002 ridgeSupport560_rest_009
    ridgeSupport560_001 ridgeSupport560_suffix_002 ridgeSupport560_001_decode ridgeSupport560_suffix_decode_002
theorem ridgeSupport560_suffix_decode_000 : PackedRawNatGrowth.readList 14 263 ridgeSupport560_rest_000 =
    (ridgeSupport560_suffix_000, ridgeSupport560_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 231
    ridgeSupport560_rest_000 ridgeSupport560_rest_001 ridgeSupport560_rest_009
    ridgeSupport560_000 ridgeSupport560_suffix_001 ridgeSupport560_000_decode ridgeSupport560_suffix_decode_001
theorem ridgeSupport560_eq : candidateRows 560 = ridgeSupport560_suffix_000 := by
  change candidateSupports 560 = ridgeSupport560_suffix_000
  rw [ridgeSupport560_source]
  exact congrArg Prod.fst ridgeSupport560_suffix_decode_000
theorem ridgeTest_large_560 : ridgeTest 560 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport560_eq]
    simp only [ridgeSupport560_suffix_000, ridgeSupport560_suffix_001, ridgeSupport560_suffix_002, ridgeSupport560_suffix_003, ridgeSupport560_suffix_004, ridgeSupport560_suffix_005, ridgeSupport560_suffix_006, ridgeSupport560_suffix_007, ridgeSupport560_suffix_008, ridgeSupport560_suffix_009, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport560_000_mask, ridgeSupport560_001_mask, ridgeSupport560_002_mask, ridgeSupport560_003_mask, ridgeSupport560_004_mask, ridgeSupport560_005_mask, ridgeSupport560_006_mask, ridgeSupport560_007_mask, ridgeSupport560_008_mask]
    decide +kernel
  · rw [ridgeSupport560_eq]
    simp only [ridgeSupport560_suffix_000, ridgeSupport560_suffix_001, ridgeSupport560_suffix_002, ridgeSupport560_suffix_003, ridgeSupport560_suffix_004, ridgeSupport560_suffix_005, ridgeSupport560_suffix_006, ridgeSupport560_suffix_007, ridgeSupport560_suffix_008, ridgeSupport560_suffix_009, List.all_append, List.all_nil, ridgeSupport560_000_checked, ridgeSupport560_001_checked, ridgeSupport560_002_checked, ridgeSupport560_003_checked, ridgeSupport560_004_checked, ridgeSupport560_005_checked, ridgeSupport560_006_checked, ridgeSupport560_007_checked, ridgeSupport560_008_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixExtra00
