module
prelude
public import RootedSixExtra00GrowthCacheRidgeSupport84Part000
public import RootedSixExtra00GrowthCacheRidgeSupport84Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra00
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport84_suffix_decode_009 : PackedRawNatGrowth.readList 14 0 ridgeSupport84_rest_009 =
    (ridgeSupport84_suffix_009, ridgeSupport84_rest_009) := by rfl
theorem ridgeSupport84_suffix_decode_008 : PackedRawNatGrowth.readList 14 7 ridgeSupport84_rest_008 =
    (ridgeSupport84_suffix_008, ridgeSupport84_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 7 0
    ridgeSupport84_rest_008 ridgeSupport84_rest_009 ridgeSupport84_rest_009
    ridgeSupport84_008 ridgeSupport84_suffix_009 ridgeSupport84_008_decode ridgeSupport84_suffix_decode_009
theorem ridgeSupport84_suffix_decode_007 : PackedRawNatGrowth.readList 14 39 ridgeSupport84_rest_007 =
    (ridgeSupport84_suffix_007, ridgeSupport84_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 7
    ridgeSupport84_rest_007 ridgeSupport84_rest_008 ridgeSupport84_rest_009
    ridgeSupport84_007 ridgeSupport84_suffix_008 ridgeSupport84_007_decode ridgeSupport84_suffix_decode_008
theorem ridgeSupport84_suffix_decode_006 : PackedRawNatGrowth.readList 14 71 ridgeSupport84_rest_006 =
    (ridgeSupport84_suffix_006, ridgeSupport84_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 39
    ridgeSupport84_rest_006 ridgeSupport84_rest_007 ridgeSupport84_rest_009
    ridgeSupport84_006 ridgeSupport84_suffix_007 ridgeSupport84_006_decode ridgeSupport84_suffix_decode_007
theorem ridgeSupport84_suffix_decode_005 : PackedRawNatGrowth.readList 14 103 ridgeSupport84_rest_005 =
    (ridgeSupport84_suffix_005, ridgeSupport84_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 71
    ridgeSupport84_rest_005 ridgeSupport84_rest_006 ridgeSupport84_rest_009
    ridgeSupport84_005 ridgeSupport84_suffix_006 ridgeSupport84_005_decode ridgeSupport84_suffix_decode_006
theorem ridgeSupport84_suffix_decode_004 : PackedRawNatGrowth.readList 14 135 ridgeSupport84_rest_004 =
    (ridgeSupport84_suffix_004, ridgeSupport84_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 103
    ridgeSupport84_rest_004 ridgeSupport84_rest_005 ridgeSupport84_rest_009
    ridgeSupport84_004 ridgeSupport84_suffix_005 ridgeSupport84_004_decode ridgeSupport84_suffix_decode_005
theorem ridgeSupport84_suffix_decode_003 : PackedRawNatGrowth.readList 14 167 ridgeSupport84_rest_003 =
    (ridgeSupport84_suffix_003, ridgeSupport84_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 135
    ridgeSupport84_rest_003 ridgeSupport84_rest_004 ridgeSupport84_rest_009
    ridgeSupport84_003 ridgeSupport84_suffix_004 ridgeSupport84_003_decode ridgeSupport84_suffix_decode_004
theorem ridgeSupport84_suffix_decode_002 : PackedRawNatGrowth.readList 14 199 ridgeSupport84_rest_002 =
    (ridgeSupport84_suffix_002, ridgeSupport84_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 167
    ridgeSupport84_rest_002 ridgeSupport84_rest_003 ridgeSupport84_rest_009
    ridgeSupport84_002 ridgeSupport84_suffix_003 ridgeSupport84_002_decode ridgeSupport84_suffix_decode_003
theorem ridgeSupport84_suffix_decode_001 : PackedRawNatGrowth.readList 14 231 ridgeSupport84_rest_001 =
    (ridgeSupport84_suffix_001, ridgeSupport84_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 199
    ridgeSupport84_rest_001 ridgeSupport84_rest_002 ridgeSupport84_rest_009
    ridgeSupport84_001 ridgeSupport84_suffix_002 ridgeSupport84_001_decode ridgeSupport84_suffix_decode_002
theorem ridgeSupport84_suffix_decode_000 : PackedRawNatGrowth.readList 14 263 ridgeSupport84_rest_000 =
    (ridgeSupport84_suffix_000, ridgeSupport84_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 231
    ridgeSupport84_rest_000 ridgeSupport84_rest_001 ridgeSupport84_rest_009
    ridgeSupport84_000 ridgeSupport84_suffix_001 ridgeSupport84_000_decode ridgeSupport84_suffix_decode_001
theorem ridgeSupport84_eq : candidateRows 84 = ridgeSupport84_suffix_000 := by
  change candidateSupports 84 = ridgeSupport84_suffix_000
  rw [ridgeSupport84_source]
  exact congrArg Prod.fst ridgeSupport84_suffix_decode_000
theorem ridgeTest_large_84 : ridgeTest 84 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport84_eq]
    simp only [ridgeSupport84_suffix_000, ridgeSupport84_suffix_001, ridgeSupport84_suffix_002, ridgeSupport84_suffix_003, ridgeSupport84_suffix_004, ridgeSupport84_suffix_005, ridgeSupport84_suffix_006, ridgeSupport84_suffix_007, ridgeSupport84_suffix_008, ridgeSupport84_suffix_009, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport84_000_mask, ridgeSupport84_001_mask, ridgeSupport84_002_mask, ridgeSupport84_003_mask, ridgeSupport84_004_mask, ridgeSupport84_005_mask, ridgeSupport84_006_mask, ridgeSupport84_007_mask, ridgeSupport84_008_mask]
    decide +kernel
  · rw [ridgeSupport84_eq]
    simp only [ridgeSupport84_suffix_000, ridgeSupport84_suffix_001, ridgeSupport84_suffix_002, ridgeSupport84_suffix_003, ridgeSupport84_suffix_004, ridgeSupport84_suffix_005, ridgeSupport84_suffix_006, ridgeSupport84_suffix_007, ridgeSupport84_suffix_008, ridgeSupport84_suffix_009, List.all_append, List.all_nil, ridgeSupport84_000_checked, ridgeSupport84_001_checked, ridgeSupport84_002_checked, ridgeSupport84_003_checked, ridgeSupport84_004_checked, ridgeSupport84_005_checked, ridgeSupport84_006_checked, ridgeSupport84_007_checked, ridgeSupport84_008_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixExtra00
