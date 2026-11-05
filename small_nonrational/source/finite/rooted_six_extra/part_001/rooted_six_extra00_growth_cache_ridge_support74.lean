module
prelude
public import RootedSixExtra00GrowthCacheRidgeSupport74Part000
public import RootedSixExtra00GrowthCacheRidgeSupport74Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra00
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport74_suffix_decode_009 : PackedRawNatGrowth.readList 14 0 ridgeSupport74_rest_009 =
    (ridgeSupport74_suffix_009, ridgeSupport74_rest_009) := by rfl
theorem ridgeSupport74_suffix_decode_008 : PackedRawNatGrowth.readList 14 7 ridgeSupport74_rest_008 =
    (ridgeSupport74_suffix_008, ridgeSupport74_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 7 0
    ridgeSupport74_rest_008 ridgeSupport74_rest_009 ridgeSupport74_rest_009
    ridgeSupport74_008 ridgeSupport74_suffix_009 ridgeSupport74_008_decode ridgeSupport74_suffix_decode_009
theorem ridgeSupport74_suffix_decode_007 : PackedRawNatGrowth.readList 14 39 ridgeSupport74_rest_007 =
    (ridgeSupport74_suffix_007, ridgeSupport74_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 7
    ridgeSupport74_rest_007 ridgeSupport74_rest_008 ridgeSupport74_rest_009
    ridgeSupport74_007 ridgeSupport74_suffix_008 ridgeSupport74_007_decode ridgeSupport74_suffix_decode_008
theorem ridgeSupport74_suffix_decode_006 : PackedRawNatGrowth.readList 14 71 ridgeSupport74_rest_006 =
    (ridgeSupport74_suffix_006, ridgeSupport74_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 39
    ridgeSupport74_rest_006 ridgeSupport74_rest_007 ridgeSupport74_rest_009
    ridgeSupport74_006 ridgeSupport74_suffix_007 ridgeSupport74_006_decode ridgeSupport74_suffix_decode_007
theorem ridgeSupport74_suffix_decode_005 : PackedRawNatGrowth.readList 14 103 ridgeSupport74_rest_005 =
    (ridgeSupport74_suffix_005, ridgeSupport74_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 71
    ridgeSupport74_rest_005 ridgeSupport74_rest_006 ridgeSupport74_rest_009
    ridgeSupport74_005 ridgeSupport74_suffix_006 ridgeSupport74_005_decode ridgeSupport74_suffix_decode_006
theorem ridgeSupport74_suffix_decode_004 : PackedRawNatGrowth.readList 14 135 ridgeSupport74_rest_004 =
    (ridgeSupport74_suffix_004, ridgeSupport74_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 103
    ridgeSupport74_rest_004 ridgeSupport74_rest_005 ridgeSupport74_rest_009
    ridgeSupport74_004 ridgeSupport74_suffix_005 ridgeSupport74_004_decode ridgeSupport74_suffix_decode_005
theorem ridgeSupport74_suffix_decode_003 : PackedRawNatGrowth.readList 14 167 ridgeSupport74_rest_003 =
    (ridgeSupport74_suffix_003, ridgeSupport74_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 135
    ridgeSupport74_rest_003 ridgeSupport74_rest_004 ridgeSupport74_rest_009
    ridgeSupport74_003 ridgeSupport74_suffix_004 ridgeSupport74_003_decode ridgeSupport74_suffix_decode_004
theorem ridgeSupport74_suffix_decode_002 : PackedRawNatGrowth.readList 14 199 ridgeSupport74_rest_002 =
    (ridgeSupport74_suffix_002, ridgeSupport74_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 167
    ridgeSupport74_rest_002 ridgeSupport74_rest_003 ridgeSupport74_rest_009
    ridgeSupport74_002 ridgeSupport74_suffix_003 ridgeSupport74_002_decode ridgeSupport74_suffix_decode_003
theorem ridgeSupport74_suffix_decode_001 : PackedRawNatGrowth.readList 14 231 ridgeSupport74_rest_001 =
    (ridgeSupport74_suffix_001, ridgeSupport74_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 199
    ridgeSupport74_rest_001 ridgeSupport74_rest_002 ridgeSupport74_rest_009
    ridgeSupport74_001 ridgeSupport74_suffix_002 ridgeSupport74_001_decode ridgeSupport74_suffix_decode_002
theorem ridgeSupport74_suffix_decode_000 : PackedRawNatGrowth.readList 14 263 ridgeSupport74_rest_000 =
    (ridgeSupport74_suffix_000, ridgeSupport74_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 231
    ridgeSupport74_rest_000 ridgeSupport74_rest_001 ridgeSupport74_rest_009
    ridgeSupport74_000 ridgeSupport74_suffix_001 ridgeSupport74_000_decode ridgeSupport74_suffix_decode_001
theorem ridgeSupport74_eq : candidateRows 74 = ridgeSupport74_suffix_000 := by
  change candidateSupports 74 = ridgeSupport74_suffix_000
  rw [ridgeSupport74_source]
  exact congrArg Prod.fst ridgeSupport74_suffix_decode_000
theorem ridgeTest_large_74 : ridgeTest 74 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport74_eq]
    simp only [ridgeSupport74_suffix_000, ridgeSupport74_suffix_001, ridgeSupport74_suffix_002, ridgeSupport74_suffix_003, ridgeSupport74_suffix_004, ridgeSupport74_suffix_005, ridgeSupport74_suffix_006, ridgeSupport74_suffix_007, ridgeSupport74_suffix_008, ridgeSupport74_suffix_009, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport74_000_mask, ridgeSupport74_001_mask, ridgeSupport74_002_mask, ridgeSupport74_003_mask, ridgeSupport74_004_mask, ridgeSupport74_005_mask, ridgeSupport74_006_mask, ridgeSupport74_007_mask, ridgeSupport74_008_mask]
    decide +kernel
  · rw [ridgeSupport74_eq]
    simp only [ridgeSupport74_suffix_000, ridgeSupport74_suffix_001, ridgeSupport74_suffix_002, ridgeSupport74_suffix_003, ridgeSupport74_suffix_004, ridgeSupport74_suffix_005, ridgeSupport74_suffix_006, ridgeSupport74_suffix_007, ridgeSupport74_suffix_008, ridgeSupport74_suffix_009, List.all_append, List.all_nil, ridgeSupport74_000_checked, ridgeSupport74_001_checked, ridgeSupport74_002_checked, ridgeSupport74_003_checked, ridgeSupport74_004_checked, ridgeSupport74_005_checked, ridgeSupport74_006_checked, ridgeSupport74_007_checked, ridgeSupport74_008_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixExtra00
