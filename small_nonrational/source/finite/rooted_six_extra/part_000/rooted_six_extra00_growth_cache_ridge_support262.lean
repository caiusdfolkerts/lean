module
prelude
public import RootedSixExtra00GrowthCacheRidgeSupport262Part000
public import RootedSixExtra00GrowthCacheRidgeSupport262Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra00
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport262_suffix_decode_009 : PackedRawNatGrowth.readList 14 0 ridgeSupport262_rest_009 =
    (ridgeSupport262_suffix_009, ridgeSupport262_rest_009) := by rfl
theorem ridgeSupport262_suffix_decode_008 : PackedRawNatGrowth.readList 14 7 ridgeSupport262_rest_008 =
    (ridgeSupport262_suffix_008, ridgeSupport262_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 7 0
    ridgeSupport262_rest_008 ridgeSupport262_rest_009 ridgeSupport262_rest_009
    ridgeSupport262_008 ridgeSupport262_suffix_009 ridgeSupport262_008_decode ridgeSupport262_suffix_decode_009
theorem ridgeSupport262_suffix_decode_007 : PackedRawNatGrowth.readList 14 39 ridgeSupport262_rest_007 =
    (ridgeSupport262_suffix_007, ridgeSupport262_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 7
    ridgeSupport262_rest_007 ridgeSupport262_rest_008 ridgeSupport262_rest_009
    ridgeSupport262_007 ridgeSupport262_suffix_008 ridgeSupport262_007_decode ridgeSupport262_suffix_decode_008
theorem ridgeSupport262_suffix_decode_006 : PackedRawNatGrowth.readList 14 71 ridgeSupport262_rest_006 =
    (ridgeSupport262_suffix_006, ridgeSupport262_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 39
    ridgeSupport262_rest_006 ridgeSupport262_rest_007 ridgeSupport262_rest_009
    ridgeSupport262_006 ridgeSupport262_suffix_007 ridgeSupport262_006_decode ridgeSupport262_suffix_decode_007
theorem ridgeSupport262_suffix_decode_005 : PackedRawNatGrowth.readList 14 103 ridgeSupport262_rest_005 =
    (ridgeSupport262_suffix_005, ridgeSupport262_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 71
    ridgeSupport262_rest_005 ridgeSupport262_rest_006 ridgeSupport262_rest_009
    ridgeSupport262_005 ridgeSupport262_suffix_006 ridgeSupport262_005_decode ridgeSupport262_suffix_decode_006
theorem ridgeSupport262_suffix_decode_004 : PackedRawNatGrowth.readList 14 135 ridgeSupport262_rest_004 =
    (ridgeSupport262_suffix_004, ridgeSupport262_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 103
    ridgeSupport262_rest_004 ridgeSupport262_rest_005 ridgeSupport262_rest_009
    ridgeSupport262_004 ridgeSupport262_suffix_005 ridgeSupport262_004_decode ridgeSupport262_suffix_decode_005
theorem ridgeSupport262_suffix_decode_003 : PackedRawNatGrowth.readList 14 167 ridgeSupport262_rest_003 =
    (ridgeSupport262_suffix_003, ridgeSupport262_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 135
    ridgeSupport262_rest_003 ridgeSupport262_rest_004 ridgeSupport262_rest_009
    ridgeSupport262_003 ridgeSupport262_suffix_004 ridgeSupport262_003_decode ridgeSupport262_suffix_decode_004
theorem ridgeSupport262_suffix_decode_002 : PackedRawNatGrowth.readList 14 199 ridgeSupport262_rest_002 =
    (ridgeSupport262_suffix_002, ridgeSupport262_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 167
    ridgeSupport262_rest_002 ridgeSupport262_rest_003 ridgeSupport262_rest_009
    ridgeSupport262_002 ridgeSupport262_suffix_003 ridgeSupport262_002_decode ridgeSupport262_suffix_decode_003
theorem ridgeSupport262_suffix_decode_001 : PackedRawNatGrowth.readList 14 231 ridgeSupport262_rest_001 =
    (ridgeSupport262_suffix_001, ridgeSupport262_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 199
    ridgeSupport262_rest_001 ridgeSupport262_rest_002 ridgeSupport262_rest_009
    ridgeSupport262_001 ridgeSupport262_suffix_002 ridgeSupport262_001_decode ridgeSupport262_suffix_decode_002
theorem ridgeSupport262_suffix_decode_000 : PackedRawNatGrowth.readList 14 263 ridgeSupport262_rest_000 =
    (ridgeSupport262_suffix_000, ridgeSupport262_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 231
    ridgeSupport262_rest_000 ridgeSupport262_rest_001 ridgeSupport262_rest_009
    ridgeSupport262_000 ridgeSupport262_suffix_001 ridgeSupport262_000_decode ridgeSupport262_suffix_decode_001
theorem ridgeSupport262_eq : candidateRows 262 = ridgeSupport262_suffix_000 := by
  change candidateSupports 262 = ridgeSupport262_suffix_000
  rw [ridgeSupport262_source]
  exact congrArg Prod.fst ridgeSupport262_suffix_decode_000
theorem ridgeTest_large_262 : ridgeTest 262 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport262_eq]
    simp only [ridgeSupport262_suffix_000, ridgeSupport262_suffix_001, ridgeSupport262_suffix_002, ridgeSupport262_suffix_003, ridgeSupport262_suffix_004, ridgeSupport262_suffix_005, ridgeSupport262_suffix_006, ridgeSupport262_suffix_007, ridgeSupport262_suffix_008, ridgeSupport262_suffix_009, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport262_000_mask, ridgeSupport262_001_mask, ridgeSupport262_002_mask, ridgeSupport262_003_mask, ridgeSupport262_004_mask, ridgeSupport262_005_mask, ridgeSupport262_006_mask, ridgeSupport262_007_mask, ridgeSupport262_008_mask]
    decide +kernel
  · rw [ridgeSupport262_eq]
    simp only [ridgeSupport262_suffix_000, ridgeSupport262_suffix_001, ridgeSupport262_suffix_002, ridgeSupport262_suffix_003, ridgeSupport262_suffix_004, ridgeSupport262_suffix_005, ridgeSupport262_suffix_006, ridgeSupport262_suffix_007, ridgeSupport262_suffix_008, ridgeSupport262_suffix_009, List.all_append, List.all_nil, ridgeSupport262_000_checked, ridgeSupport262_001_checked, ridgeSupport262_002_checked, ridgeSupport262_003_checked, ridgeSupport262_004_checked, ridgeSupport262_005_checked, ridgeSupport262_006_checked, ridgeSupport262_007_checked, ridgeSupport262_008_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixExtra00
