module
prelude
public import RootedSixExtra00GrowthCacheRidgeSupport82Part000
public import RootedSixExtra00GrowthCacheRidgeSupport82Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra00
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport82_suffix_decode_009 : PackedRawNatGrowth.readList 14 0 ridgeSupport82_rest_009 =
    (ridgeSupport82_suffix_009, ridgeSupport82_rest_009) := by rfl
theorem ridgeSupport82_suffix_decode_008 : PackedRawNatGrowth.readList 14 7 ridgeSupport82_rest_008 =
    (ridgeSupport82_suffix_008, ridgeSupport82_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 7 0
    ridgeSupport82_rest_008 ridgeSupport82_rest_009 ridgeSupport82_rest_009
    ridgeSupport82_008 ridgeSupport82_suffix_009 ridgeSupport82_008_decode ridgeSupport82_suffix_decode_009
theorem ridgeSupport82_suffix_decode_007 : PackedRawNatGrowth.readList 14 39 ridgeSupport82_rest_007 =
    (ridgeSupport82_suffix_007, ridgeSupport82_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 7
    ridgeSupport82_rest_007 ridgeSupport82_rest_008 ridgeSupport82_rest_009
    ridgeSupport82_007 ridgeSupport82_suffix_008 ridgeSupport82_007_decode ridgeSupport82_suffix_decode_008
theorem ridgeSupport82_suffix_decode_006 : PackedRawNatGrowth.readList 14 71 ridgeSupport82_rest_006 =
    (ridgeSupport82_suffix_006, ridgeSupport82_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 39
    ridgeSupport82_rest_006 ridgeSupport82_rest_007 ridgeSupport82_rest_009
    ridgeSupport82_006 ridgeSupport82_suffix_007 ridgeSupport82_006_decode ridgeSupport82_suffix_decode_007
theorem ridgeSupport82_suffix_decode_005 : PackedRawNatGrowth.readList 14 103 ridgeSupport82_rest_005 =
    (ridgeSupport82_suffix_005, ridgeSupport82_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 71
    ridgeSupport82_rest_005 ridgeSupport82_rest_006 ridgeSupport82_rest_009
    ridgeSupport82_005 ridgeSupport82_suffix_006 ridgeSupport82_005_decode ridgeSupport82_suffix_decode_006
theorem ridgeSupport82_suffix_decode_004 : PackedRawNatGrowth.readList 14 135 ridgeSupport82_rest_004 =
    (ridgeSupport82_suffix_004, ridgeSupport82_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 103
    ridgeSupport82_rest_004 ridgeSupport82_rest_005 ridgeSupport82_rest_009
    ridgeSupport82_004 ridgeSupport82_suffix_005 ridgeSupport82_004_decode ridgeSupport82_suffix_decode_005
theorem ridgeSupport82_suffix_decode_003 : PackedRawNatGrowth.readList 14 167 ridgeSupport82_rest_003 =
    (ridgeSupport82_suffix_003, ridgeSupport82_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 135
    ridgeSupport82_rest_003 ridgeSupport82_rest_004 ridgeSupport82_rest_009
    ridgeSupport82_003 ridgeSupport82_suffix_004 ridgeSupport82_003_decode ridgeSupport82_suffix_decode_004
theorem ridgeSupport82_suffix_decode_002 : PackedRawNatGrowth.readList 14 199 ridgeSupport82_rest_002 =
    (ridgeSupport82_suffix_002, ridgeSupport82_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 167
    ridgeSupport82_rest_002 ridgeSupport82_rest_003 ridgeSupport82_rest_009
    ridgeSupport82_002 ridgeSupport82_suffix_003 ridgeSupport82_002_decode ridgeSupport82_suffix_decode_003
theorem ridgeSupport82_suffix_decode_001 : PackedRawNatGrowth.readList 14 231 ridgeSupport82_rest_001 =
    (ridgeSupport82_suffix_001, ridgeSupport82_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 199
    ridgeSupport82_rest_001 ridgeSupport82_rest_002 ridgeSupport82_rest_009
    ridgeSupport82_001 ridgeSupport82_suffix_002 ridgeSupport82_001_decode ridgeSupport82_suffix_decode_002
theorem ridgeSupport82_suffix_decode_000 : PackedRawNatGrowth.readList 14 263 ridgeSupport82_rest_000 =
    (ridgeSupport82_suffix_000, ridgeSupport82_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 231
    ridgeSupport82_rest_000 ridgeSupport82_rest_001 ridgeSupport82_rest_009
    ridgeSupport82_000 ridgeSupport82_suffix_001 ridgeSupport82_000_decode ridgeSupport82_suffix_decode_001
theorem ridgeSupport82_eq : candidateRows 82 = ridgeSupport82_suffix_000 := by
  change candidateSupports 82 = ridgeSupport82_suffix_000
  rw [ridgeSupport82_source]
  exact congrArg Prod.fst ridgeSupport82_suffix_decode_000
theorem ridgeTest_large_82 : ridgeTest 82 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport82_eq]
    simp only [ridgeSupport82_suffix_000, ridgeSupport82_suffix_001, ridgeSupport82_suffix_002, ridgeSupport82_suffix_003, ridgeSupport82_suffix_004, ridgeSupport82_suffix_005, ridgeSupport82_suffix_006, ridgeSupport82_suffix_007, ridgeSupport82_suffix_008, ridgeSupport82_suffix_009, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport82_000_mask, ridgeSupport82_001_mask, ridgeSupport82_002_mask, ridgeSupport82_003_mask, ridgeSupport82_004_mask, ridgeSupport82_005_mask, ridgeSupport82_006_mask, ridgeSupport82_007_mask, ridgeSupport82_008_mask]
    decide +kernel
  · rw [ridgeSupport82_eq]
    simp only [ridgeSupport82_suffix_000, ridgeSupport82_suffix_001, ridgeSupport82_suffix_002, ridgeSupport82_suffix_003, ridgeSupport82_suffix_004, ridgeSupport82_suffix_005, ridgeSupport82_suffix_006, ridgeSupport82_suffix_007, ridgeSupport82_suffix_008, ridgeSupport82_suffix_009, List.all_append, List.all_nil, ridgeSupport82_000_checked, ridgeSupport82_001_checked, ridgeSupport82_002_checked, ridgeSupport82_003_checked, ridgeSupport82_004_checked, ridgeSupport82_005_checked, ridgeSupport82_006_checked, ridgeSupport82_007_checked, ridgeSupport82_008_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixExtra00
