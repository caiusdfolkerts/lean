module
prelude
public import RootedSixExtra00GrowthCacheRidgeSupport131Part000
public import RootedSixExtra00GrowthCacheRidgeSupport131Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra00
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport131_suffix_decode_009 : PackedRawNatGrowth.readList 14 0 ridgeSupport131_rest_009 =
    (ridgeSupport131_suffix_009, ridgeSupport131_rest_009) := by rfl
theorem ridgeSupport131_suffix_decode_008 : PackedRawNatGrowth.readList 14 7 ridgeSupport131_rest_008 =
    (ridgeSupport131_suffix_008, ridgeSupport131_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 7 0
    ridgeSupport131_rest_008 ridgeSupport131_rest_009 ridgeSupport131_rest_009
    ridgeSupport131_008 ridgeSupport131_suffix_009 ridgeSupport131_008_decode ridgeSupport131_suffix_decode_009
theorem ridgeSupport131_suffix_decode_007 : PackedRawNatGrowth.readList 14 39 ridgeSupport131_rest_007 =
    (ridgeSupport131_suffix_007, ridgeSupport131_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 7
    ridgeSupport131_rest_007 ridgeSupport131_rest_008 ridgeSupport131_rest_009
    ridgeSupport131_007 ridgeSupport131_suffix_008 ridgeSupport131_007_decode ridgeSupport131_suffix_decode_008
theorem ridgeSupport131_suffix_decode_006 : PackedRawNatGrowth.readList 14 71 ridgeSupport131_rest_006 =
    (ridgeSupport131_suffix_006, ridgeSupport131_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 39
    ridgeSupport131_rest_006 ridgeSupport131_rest_007 ridgeSupport131_rest_009
    ridgeSupport131_006 ridgeSupport131_suffix_007 ridgeSupport131_006_decode ridgeSupport131_suffix_decode_007
theorem ridgeSupport131_suffix_decode_005 : PackedRawNatGrowth.readList 14 103 ridgeSupport131_rest_005 =
    (ridgeSupport131_suffix_005, ridgeSupport131_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 71
    ridgeSupport131_rest_005 ridgeSupport131_rest_006 ridgeSupport131_rest_009
    ridgeSupport131_005 ridgeSupport131_suffix_006 ridgeSupport131_005_decode ridgeSupport131_suffix_decode_006
theorem ridgeSupport131_suffix_decode_004 : PackedRawNatGrowth.readList 14 135 ridgeSupport131_rest_004 =
    (ridgeSupport131_suffix_004, ridgeSupport131_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 103
    ridgeSupport131_rest_004 ridgeSupport131_rest_005 ridgeSupport131_rest_009
    ridgeSupport131_004 ridgeSupport131_suffix_005 ridgeSupport131_004_decode ridgeSupport131_suffix_decode_005
theorem ridgeSupport131_suffix_decode_003 : PackedRawNatGrowth.readList 14 167 ridgeSupport131_rest_003 =
    (ridgeSupport131_suffix_003, ridgeSupport131_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 135
    ridgeSupport131_rest_003 ridgeSupport131_rest_004 ridgeSupport131_rest_009
    ridgeSupport131_003 ridgeSupport131_suffix_004 ridgeSupport131_003_decode ridgeSupport131_suffix_decode_004
theorem ridgeSupport131_suffix_decode_002 : PackedRawNatGrowth.readList 14 199 ridgeSupport131_rest_002 =
    (ridgeSupport131_suffix_002, ridgeSupport131_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 167
    ridgeSupport131_rest_002 ridgeSupport131_rest_003 ridgeSupport131_rest_009
    ridgeSupport131_002 ridgeSupport131_suffix_003 ridgeSupport131_002_decode ridgeSupport131_suffix_decode_003
theorem ridgeSupport131_suffix_decode_001 : PackedRawNatGrowth.readList 14 231 ridgeSupport131_rest_001 =
    (ridgeSupport131_suffix_001, ridgeSupport131_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 199
    ridgeSupport131_rest_001 ridgeSupport131_rest_002 ridgeSupport131_rest_009
    ridgeSupport131_001 ridgeSupport131_suffix_002 ridgeSupport131_001_decode ridgeSupport131_suffix_decode_002
theorem ridgeSupport131_suffix_decode_000 : PackedRawNatGrowth.readList 14 263 ridgeSupport131_rest_000 =
    (ridgeSupport131_suffix_000, ridgeSupport131_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 231
    ridgeSupport131_rest_000 ridgeSupport131_rest_001 ridgeSupport131_rest_009
    ridgeSupport131_000 ridgeSupport131_suffix_001 ridgeSupport131_000_decode ridgeSupport131_suffix_decode_001
theorem ridgeSupport131_eq : candidateRows 131 = ridgeSupport131_suffix_000 := by
  change candidateSupports 131 = ridgeSupport131_suffix_000
  rw [ridgeSupport131_source]
  exact congrArg Prod.fst ridgeSupport131_suffix_decode_000
theorem ridgeTest_large_131 : ridgeTest 131 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport131_eq]
    simp only [ridgeSupport131_suffix_000, ridgeSupport131_suffix_001, ridgeSupport131_suffix_002, ridgeSupport131_suffix_003, ridgeSupport131_suffix_004, ridgeSupport131_suffix_005, ridgeSupport131_suffix_006, ridgeSupport131_suffix_007, ridgeSupport131_suffix_008, ridgeSupport131_suffix_009, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport131_000_mask, ridgeSupport131_001_mask, ridgeSupport131_002_mask, ridgeSupport131_003_mask, ridgeSupport131_004_mask, ridgeSupport131_005_mask, ridgeSupport131_006_mask, ridgeSupport131_007_mask, ridgeSupport131_008_mask]
    decide +kernel
  · rw [ridgeSupport131_eq]
    simp only [ridgeSupport131_suffix_000, ridgeSupport131_suffix_001, ridgeSupport131_suffix_002, ridgeSupport131_suffix_003, ridgeSupport131_suffix_004, ridgeSupport131_suffix_005, ridgeSupport131_suffix_006, ridgeSupport131_suffix_007, ridgeSupport131_suffix_008, ridgeSupport131_suffix_009, List.all_append, List.all_nil, ridgeSupport131_000_checked, ridgeSupport131_001_checked, ridgeSupport131_002_checked, ridgeSupport131_003_checked, ridgeSupport131_004_checked, ridgeSupport131_005_checked, ridgeSupport131_006_checked, ridgeSupport131_007_checked, ridgeSupport131_008_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixExtra00
