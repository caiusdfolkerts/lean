module
prelude
public import RootedSixExtra00GrowthCacheRidgeSupport532Part000
public import RootedSixExtra00GrowthCacheRidgeSupport532Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra00
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport532_suffix_decode_009 : PackedRawNatGrowth.readList 14 0 ridgeSupport532_rest_009 =
    (ridgeSupport532_suffix_009, ridgeSupport532_rest_009) := by rfl
theorem ridgeSupport532_suffix_decode_008 : PackedRawNatGrowth.readList 14 7 ridgeSupport532_rest_008 =
    (ridgeSupport532_suffix_008, ridgeSupport532_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 7 0
    ridgeSupport532_rest_008 ridgeSupport532_rest_009 ridgeSupport532_rest_009
    ridgeSupport532_008 ridgeSupport532_suffix_009 ridgeSupport532_008_decode ridgeSupport532_suffix_decode_009
theorem ridgeSupport532_suffix_decode_007 : PackedRawNatGrowth.readList 14 39 ridgeSupport532_rest_007 =
    (ridgeSupport532_suffix_007, ridgeSupport532_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 7
    ridgeSupport532_rest_007 ridgeSupport532_rest_008 ridgeSupport532_rest_009
    ridgeSupport532_007 ridgeSupport532_suffix_008 ridgeSupport532_007_decode ridgeSupport532_suffix_decode_008
theorem ridgeSupport532_suffix_decode_006 : PackedRawNatGrowth.readList 14 71 ridgeSupport532_rest_006 =
    (ridgeSupport532_suffix_006, ridgeSupport532_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 39
    ridgeSupport532_rest_006 ridgeSupport532_rest_007 ridgeSupport532_rest_009
    ridgeSupport532_006 ridgeSupport532_suffix_007 ridgeSupport532_006_decode ridgeSupport532_suffix_decode_007
theorem ridgeSupport532_suffix_decode_005 : PackedRawNatGrowth.readList 14 103 ridgeSupport532_rest_005 =
    (ridgeSupport532_suffix_005, ridgeSupport532_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 71
    ridgeSupport532_rest_005 ridgeSupport532_rest_006 ridgeSupport532_rest_009
    ridgeSupport532_005 ridgeSupport532_suffix_006 ridgeSupport532_005_decode ridgeSupport532_suffix_decode_006
theorem ridgeSupport532_suffix_decode_004 : PackedRawNatGrowth.readList 14 135 ridgeSupport532_rest_004 =
    (ridgeSupport532_suffix_004, ridgeSupport532_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 103
    ridgeSupport532_rest_004 ridgeSupport532_rest_005 ridgeSupport532_rest_009
    ridgeSupport532_004 ridgeSupport532_suffix_005 ridgeSupport532_004_decode ridgeSupport532_suffix_decode_005
theorem ridgeSupport532_suffix_decode_003 : PackedRawNatGrowth.readList 14 167 ridgeSupport532_rest_003 =
    (ridgeSupport532_suffix_003, ridgeSupport532_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 135
    ridgeSupport532_rest_003 ridgeSupport532_rest_004 ridgeSupport532_rest_009
    ridgeSupport532_003 ridgeSupport532_suffix_004 ridgeSupport532_003_decode ridgeSupport532_suffix_decode_004
theorem ridgeSupport532_suffix_decode_002 : PackedRawNatGrowth.readList 14 199 ridgeSupport532_rest_002 =
    (ridgeSupport532_suffix_002, ridgeSupport532_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 167
    ridgeSupport532_rest_002 ridgeSupport532_rest_003 ridgeSupport532_rest_009
    ridgeSupport532_002 ridgeSupport532_suffix_003 ridgeSupport532_002_decode ridgeSupport532_suffix_decode_003
theorem ridgeSupport532_suffix_decode_001 : PackedRawNatGrowth.readList 14 231 ridgeSupport532_rest_001 =
    (ridgeSupport532_suffix_001, ridgeSupport532_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 199
    ridgeSupport532_rest_001 ridgeSupport532_rest_002 ridgeSupport532_rest_009
    ridgeSupport532_001 ridgeSupport532_suffix_002 ridgeSupport532_001_decode ridgeSupport532_suffix_decode_002
theorem ridgeSupport532_suffix_decode_000 : PackedRawNatGrowth.readList 14 263 ridgeSupport532_rest_000 =
    (ridgeSupport532_suffix_000, ridgeSupport532_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 231
    ridgeSupport532_rest_000 ridgeSupport532_rest_001 ridgeSupport532_rest_009
    ridgeSupport532_000 ridgeSupport532_suffix_001 ridgeSupport532_000_decode ridgeSupport532_suffix_decode_001
theorem ridgeSupport532_eq : candidateRows 532 = ridgeSupport532_suffix_000 := by
  change candidateSupports 532 = ridgeSupport532_suffix_000
  rw [ridgeSupport532_source]
  exact congrArg Prod.fst ridgeSupport532_suffix_decode_000
theorem ridgeTest_large_532 : ridgeTest 532 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport532_eq]
    simp only [ridgeSupport532_suffix_000, ridgeSupport532_suffix_001, ridgeSupport532_suffix_002, ridgeSupport532_suffix_003, ridgeSupport532_suffix_004, ridgeSupport532_suffix_005, ridgeSupport532_suffix_006, ridgeSupport532_suffix_007, ridgeSupport532_suffix_008, ridgeSupport532_suffix_009, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport532_000_mask, ridgeSupport532_001_mask, ridgeSupport532_002_mask, ridgeSupport532_003_mask, ridgeSupport532_004_mask, ridgeSupport532_005_mask, ridgeSupport532_006_mask, ridgeSupport532_007_mask, ridgeSupport532_008_mask]
    decide +kernel
  · rw [ridgeSupport532_eq]
    simp only [ridgeSupport532_suffix_000, ridgeSupport532_suffix_001, ridgeSupport532_suffix_002, ridgeSupport532_suffix_003, ridgeSupport532_suffix_004, ridgeSupport532_suffix_005, ridgeSupport532_suffix_006, ridgeSupport532_suffix_007, ridgeSupport532_suffix_008, ridgeSupport532_suffix_009, List.all_append, List.all_nil, ridgeSupport532_000_checked, ridgeSupport532_001_checked, ridgeSupport532_002_checked, ridgeSupport532_003_checked, ridgeSupport532_004_checked, ridgeSupport532_005_checked, ridgeSupport532_006_checked, ridgeSupport532_007_checked, ridgeSupport532_008_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixExtra00
