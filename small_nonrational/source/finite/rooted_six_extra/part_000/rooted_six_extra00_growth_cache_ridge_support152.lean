module
prelude
public import RootedSixExtra00GrowthCacheRidgeSupport152Part000
public import RootedSixExtra00GrowthCacheRidgeSupport152Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra00
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport152_suffix_decode_009 : PackedRawNatGrowth.readList 14 0 ridgeSupport152_rest_009 =
    (ridgeSupport152_suffix_009, ridgeSupport152_rest_009) := by rfl
theorem ridgeSupport152_suffix_decode_008 : PackedRawNatGrowth.readList 14 7 ridgeSupport152_rest_008 =
    (ridgeSupport152_suffix_008, ridgeSupport152_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 7 0
    ridgeSupport152_rest_008 ridgeSupport152_rest_009 ridgeSupport152_rest_009
    ridgeSupport152_008 ridgeSupport152_suffix_009 ridgeSupport152_008_decode ridgeSupport152_suffix_decode_009
theorem ridgeSupport152_suffix_decode_007 : PackedRawNatGrowth.readList 14 39 ridgeSupport152_rest_007 =
    (ridgeSupport152_suffix_007, ridgeSupport152_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 7
    ridgeSupport152_rest_007 ridgeSupport152_rest_008 ridgeSupport152_rest_009
    ridgeSupport152_007 ridgeSupport152_suffix_008 ridgeSupport152_007_decode ridgeSupport152_suffix_decode_008
theorem ridgeSupport152_suffix_decode_006 : PackedRawNatGrowth.readList 14 71 ridgeSupport152_rest_006 =
    (ridgeSupport152_suffix_006, ridgeSupport152_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 39
    ridgeSupport152_rest_006 ridgeSupport152_rest_007 ridgeSupport152_rest_009
    ridgeSupport152_006 ridgeSupport152_suffix_007 ridgeSupport152_006_decode ridgeSupport152_suffix_decode_007
theorem ridgeSupport152_suffix_decode_005 : PackedRawNatGrowth.readList 14 103 ridgeSupport152_rest_005 =
    (ridgeSupport152_suffix_005, ridgeSupport152_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 71
    ridgeSupport152_rest_005 ridgeSupport152_rest_006 ridgeSupport152_rest_009
    ridgeSupport152_005 ridgeSupport152_suffix_006 ridgeSupport152_005_decode ridgeSupport152_suffix_decode_006
theorem ridgeSupport152_suffix_decode_004 : PackedRawNatGrowth.readList 14 135 ridgeSupport152_rest_004 =
    (ridgeSupport152_suffix_004, ridgeSupport152_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 103
    ridgeSupport152_rest_004 ridgeSupport152_rest_005 ridgeSupport152_rest_009
    ridgeSupport152_004 ridgeSupport152_suffix_005 ridgeSupport152_004_decode ridgeSupport152_suffix_decode_005
theorem ridgeSupport152_suffix_decode_003 : PackedRawNatGrowth.readList 14 167 ridgeSupport152_rest_003 =
    (ridgeSupport152_suffix_003, ridgeSupport152_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 135
    ridgeSupport152_rest_003 ridgeSupport152_rest_004 ridgeSupport152_rest_009
    ridgeSupport152_003 ridgeSupport152_suffix_004 ridgeSupport152_003_decode ridgeSupport152_suffix_decode_004
theorem ridgeSupport152_suffix_decode_002 : PackedRawNatGrowth.readList 14 199 ridgeSupport152_rest_002 =
    (ridgeSupport152_suffix_002, ridgeSupport152_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 167
    ridgeSupport152_rest_002 ridgeSupport152_rest_003 ridgeSupport152_rest_009
    ridgeSupport152_002 ridgeSupport152_suffix_003 ridgeSupport152_002_decode ridgeSupport152_suffix_decode_003
theorem ridgeSupport152_suffix_decode_001 : PackedRawNatGrowth.readList 14 231 ridgeSupport152_rest_001 =
    (ridgeSupport152_suffix_001, ridgeSupport152_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 199
    ridgeSupport152_rest_001 ridgeSupport152_rest_002 ridgeSupport152_rest_009
    ridgeSupport152_001 ridgeSupport152_suffix_002 ridgeSupport152_001_decode ridgeSupport152_suffix_decode_002
theorem ridgeSupport152_suffix_decode_000 : PackedRawNatGrowth.readList 14 263 ridgeSupport152_rest_000 =
    (ridgeSupport152_suffix_000, ridgeSupport152_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 231
    ridgeSupport152_rest_000 ridgeSupport152_rest_001 ridgeSupport152_rest_009
    ridgeSupport152_000 ridgeSupport152_suffix_001 ridgeSupport152_000_decode ridgeSupport152_suffix_decode_001
theorem ridgeSupport152_eq : candidateRows 152 = ridgeSupport152_suffix_000 := by
  change candidateSupports 152 = ridgeSupport152_suffix_000
  rw [ridgeSupport152_source]
  exact congrArg Prod.fst ridgeSupport152_suffix_decode_000
theorem ridgeTest_large_152 : ridgeTest 152 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport152_eq]
    simp only [ridgeSupport152_suffix_000, ridgeSupport152_suffix_001, ridgeSupport152_suffix_002, ridgeSupport152_suffix_003, ridgeSupport152_suffix_004, ridgeSupport152_suffix_005, ridgeSupport152_suffix_006, ridgeSupport152_suffix_007, ridgeSupport152_suffix_008, ridgeSupport152_suffix_009, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport152_000_mask, ridgeSupport152_001_mask, ridgeSupport152_002_mask, ridgeSupport152_003_mask, ridgeSupport152_004_mask, ridgeSupport152_005_mask, ridgeSupport152_006_mask, ridgeSupport152_007_mask, ridgeSupport152_008_mask]
    decide +kernel
  · rw [ridgeSupport152_eq]
    simp only [ridgeSupport152_suffix_000, ridgeSupport152_suffix_001, ridgeSupport152_suffix_002, ridgeSupport152_suffix_003, ridgeSupport152_suffix_004, ridgeSupport152_suffix_005, ridgeSupport152_suffix_006, ridgeSupport152_suffix_007, ridgeSupport152_suffix_008, ridgeSupport152_suffix_009, List.all_append, List.all_nil, ridgeSupport152_000_checked, ridgeSupport152_001_checked, ridgeSupport152_002_checked, ridgeSupport152_003_checked, ridgeSupport152_004_checked, ridgeSupport152_005_checked, ridgeSupport152_006_checked, ridgeSupport152_007_checked, ridgeSupport152_008_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixExtra00
