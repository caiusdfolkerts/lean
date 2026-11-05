module
prelude
public import RootedSixExtra00GrowthCacheRidgeSupport148Part000
public import RootedSixExtra00GrowthCacheRidgeSupport148Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra00
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport148_suffix_decode_009 : PackedRawNatGrowth.readList 14 0 ridgeSupport148_rest_009 =
    (ridgeSupport148_suffix_009, ridgeSupport148_rest_009) := by rfl
theorem ridgeSupport148_suffix_decode_008 : PackedRawNatGrowth.readList 14 7 ridgeSupport148_rest_008 =
    (ridgeSupport148_suffix_008, ridgeSupport148_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 7 0
    ridgeSupport148_rest_008 ridgeSupport148_rest_009 ridgeSupport148_rest_009
    ridgeSupport148_008 ridgeSupport148_suffix_009 ridgeSupport148_008_decode ridgeSupport148_suffix_decode_009
theorem ridgeSupport148_suffix_decode_007 : PackedRawNatGrowth.readList 14 39 ridgeSupport148_rest_007 =
    (ridgeSupport148_suffix_007, ridgeSupport148_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 7
    ridgeSupport148_rest_007 ridgeSupport148_rest_008 ridgeSupport148_rest_009
    ridgeSupport148_007 ridgeSupport148_suffix_008 ridgeSupport148_007_decode ridgeSupport148_suffix_decode_008
theorem ridgeSupport148_suffix_decode_006 : PackedRawNatGrowth.readList 14 71 ridgeSupport148_rest_006 =
    (ridgeSupport148_suffix_006, ridgeSupport148_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 39
    ridgeSupport148_rest_006 ridgeSupport148_rest_007 ridgeSupport148_rest_009
    ridgeSupport148_006 ridgeSupport148_suffix_007 ridgeSupport148_006_decode ridgeSupport148_suffix_decode_007
theorem ridgeSupport148_suffix_decode_005 : PackedRawNatGrowth.readList 14 103 ridgeSupport148_rest_005 =
    (ridgeSupport148_suffix_005, ridgeSupport148_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 71
    ridgeSupport148_rest_005 ridgeSupport148_rest_006 ridgeSupport148_rest_009
    ridgeSupport148_005 ridgeSupport148_suffix_006 ridgeSupport148_005_decode ridgeSupport148_suffix_decode_006
theorem ridgeSupport148_suffix_decode_004 : PackedRawNatGrowth.readList 14 135 ridgeSupport148_rest_004 =
    (ridgeSupport148_suffix_004, ridgeSupport148_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 103
    ridgeSupport148_rest_004 ridgeSupport148_rest_005 ridgeSupport148_rest_009
    ridgeSupport148_004 ridgeSupport148_suffix_005 ridgeSupport148_004_decode ridgeSupport148_suffix_decode_005
theorem ridgeSupport148_suffix_decode_003 : PackedRawNatGrowth.readList 14 167 ridgeSupport148_rest_003 =
    (ridgeSupport148_suffix_003, ridgeSupport148_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 135
    ridgeSupport148_rest_003 ridgeSupport148_rest_004 ridgeSupport148_rest_009
    ridgeSupport148_003 ridgeSupport148_suffix_004 ridgeSupport148_003_decode ridgeSupport148_suffix_decode_004
theorem ridgeSupport148_suffix_decode_002 : PackedRawNatGrowth.readList 14 199 ridgeSupport148_rest_002 =
    (ridgeSupport148_suffix_002, ridgeSupport148_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 167
    ridgeSupport148_rest_002 ridgeSupport148_rest_003 ridgeSupport148_rest_009
    ridgeSupport148_002 ridgeSupport148_suffix_003 ridgeSupport148_002_decode ridgeSupport148_suffix_decode_003
theorem ridgeSupport148_suffix_decode_001 : PackedRawNatGrowth.readList 14 231 ridgeSupport148_rest_001 =
    (ridgeSupport148_suffix_001, ridgeSupport148_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 199
    ridgeSupport148_rest_001 ridgeSupport148_rest_002 ridgeSupport148_rest_009
    ridgeSupport148_001 ridgeSupport148_suffix_002 ridgeSupport148_001_decode ridgeSupport148_suffix_decode_002
theorem ridgeSupport148_suffix_decode_000 : PackedRawNatGrowth.readList 14 263 ridgeSupport148_rest_000 =
    (ridgeSupport148_suffix_000, ridgeSupport148_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 231
    ridgeSupport148_rest_000 ridgeSupport148_rest_001 ridgeSupport148_rest_009
    ridgeSupport148_000 ridgeSupport148_suffix_001 ridgeSupport148_000_decode ridgeSupport148_suffix_decode_001
theorem ridgeSupport148_eq : candidateRows 148 = ridgeSupport148_suffix_000 := by
  change candidateSupports 148 = ridgeSupport148_suffix_000
  rw [ridgeSupport148_source]
  exact congrArg Prod.fst ridgeSupport148_suffix_decode_000
theorem ridgeTest_large_148 : ridgeTest 148 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport148_eq]
    simp only [ridgeSupport148_suffix_000, ridgeSupport148_suffix_001, ridgeSupport148_suffix_002, ridgeSupport148_suffix_003, ridgeSupport148_suffix_004, ridgeSupport148_suffix_005, ridgeSupport148_suffix_006, ridgeSupport148_suffix_007, ridgeSupport148_suffix_008, ridgeSupport148_suffix_009, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport148_000_mask, ridgeSupport148_001_mask, ridgeSupport148_002_mask, ridgeSupport148_003_mask, ridgeSupport148_004_mask, ridgeSupport148_005_mask, ridgeSupport148_006_mask, ridgeSupport148_007_mask, ridgeSupport148_008_mask]
    decide +kernel
  · rw [ridgeSupport148_eq]
    simp only [ridgeSupport148_suffix_000, ridgeSupport148_suffix_001, ridgeSupport148_suffix_002, ridgeSupport148_suffix_003, ridgeSupport148_suffix_004, ridgeSupport148_suffix_005, ridgeSupport148_suffix_006, ridgeSupport148_suffix_007, ridgeSupport148_suffix_008, ridgeSupport148_suffix_009, List.all_append, List.all_nil, ridgeSupport148_000_checked, ridgeSupport148_001_checked, ridgeSupport148_002_checked, ridgeSupport148_003_checked, ridgeSupport148_004_checked, ridgeSupport148_005_checked, ridgeSupport148_006_checked, ridgeSupport148_007_checked, ridgeSupport148_008_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixExtra00
