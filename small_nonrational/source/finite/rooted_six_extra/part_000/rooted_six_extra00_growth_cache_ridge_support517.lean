module
prelude
public import RootedSixExtra00GrowthCacheRidgeSupport517Part000
public import RootedSixExtra00GrowthCacheRidgeSupport517Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra00
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport517_suffix_decode_009 : PackedRawNatGrowth.readList 14 0 ridgeSupport517_rest_009 =
    (ridgeSupport517_suffix_009, ridgeSupport517_rest_009) := by rfl
theorem ridgeSupport517_suffix_decode_008 : PackedRawNatGrowth.readList 14 7 ridgeSupport517_rest_008 =
    (ridgeSupport517_suffix_008, ridgeSupport517_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 7 0
    ridgeSupport517_rest_008 ridgeSupport517_rest_009 ridgeSupport517_rest_009
    ridgeSupport517_008 ridgeSupport517_suffix_009 ridgeSupport517_008_decode ridgeSupport517_suffix_decode_009
theorem ridgeSupport517_suffix_decode_007 : PackedRawNatGrowth.readList 14 39 ridgeSupport517_rest_007 =
    (ridgeSupport517_suffix_007, ridgeSupport517_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 7
    ridgeSupport517_rest_007 ridgeSupport517_rest_008 ridgeSupport517_rest_009
    ridgeSupport517_007 ridgeSupport517_suffix_008 ridgeSupport517_007_decode ridgeSupport517_suffix_decode_008
theorem ridgeSupport517_suffix_decode_006 : PackedRawNatGrowth.readList 14 71 ridgeSupport517_rest_006 =
    (ridgeSupport517_suffix_006, ridgeSupport517_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 39
    ridgeSupport517_rest_006 ridgeSupport517_rest_007 ridgeSupport517_rest_009
    ridgeSupport517_006 ridgeSupport517_suffix_007 ridgeSupport517_006_decode ridgeSupport517_suffix_decode_007
theorem ridgeSupport517_suffix_decode_005 : PackedRawNatGrowth.readList 14 103 ridgeSupport517_rest_005 =
    (ridgeSupport517_suffix_005, ridgeSupport517_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 71
    ridgeSupport517_rest_005 ridgeSupport517_rest_006 ridgeSupport517_rest_009
    ridgeSupport517_005 ridgeSupport517_suffix_006 ridgeSupport517_005_decode ridgeSupport517_suffix_decode_006
theorem ridgeSupport517_suffix_decode_004 : PackedRawNatGrowth.readList 14 135 ridgeSupport517_rest_004 =
    (ridgeSupport517_suffix_004, ridgeSupport517_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 103
    ridgeSupport517_rest_004 ridgeSupport517_rest_005 ridgeSupport517_rest_009
    ridgeSupport517_004 ridgeSupport517_suffix_005 ridgeSupport517_004_decode ridgeSupport517_suffix_decode_005
theorem ridgeSupport517_suffix_decode_003 : PackedRawNatGrowth.readList 14 167 ridgeSupport517_rest_003 =
    (ridgeSupport517_suffix_003, ridgeSupport517_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 135
    ridgeSupport517_rest_003 ridgeSupport517_rest_004 ridgeSupport517_rest_009
    ridgeSupport517_003 ridgeSupport517_suffix_004 ridgeSupport517_003_decode ridgeSupport517_suffix_decode_004
theorem ridgeSupport517_suffix_decode_002 : PackedRawNatGrowth.readList 14 199 ridgeSupport517_rest_002 =
    (ridgeSupport517_suffix_002, ridgeSupport517_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 167
    ridgeSupport517_rest_002 ridgeSupport517_rest_003 ridgeSupport517_rest_009
    ridgeSupport517_002 ridgeSupport517_suffix_003 ridgeSupport517_002_decode ridgeSupport517_suffix_decode_003
theorem ridgeSupport517_suffix_decode_001 : PackedRawNatGrowth.readList 14 231 ridgeSupport517_rest_001 =
    (ridgeSupport517_suffix_001, ridgeSupport517_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 199
    ridgeSupport517_rest_001 ridgeSupport517_rest_002 ridgeSupport517_rest_009
    ridgeSupport517_001 ridgeSupport517_suffix_002 ridgeSupport517_001_decode ridgeSupport517_suffix_decode_002
theorem ridgeSupport517_suffix_decode_000 : PackedRawNatGrowth.readList 14 263 ridgeSupport517_rest_000 =
    (ridgeSupport517_suffix_000, ridgeSupport517_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 231
    ridgeSupport517_rest_000 ridgeSupport517_rest_001 ridgeSupport517_rest_009
    ridgeSupport517_000 ridgeSupport517_suffix_001 ridgeSupport517_000_decode ridgeSupport517_suffix_decode_001
theorem ridgeSupport517_eq : candidateRows 517 = ridgeSupport517_suffix_000 := by
  change candidateSupports 517 = ridgeSupport517_suffix_000
  rw [ridgeSupport517_source]
  exact congrArg Prod.fst ridgeSupport517_suffix_decode_000
theorem ridgeTest_large_517 : ridgeTest 517 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport517_eq]
    simp only [ridgeSupport517_suffix_000, ridgeSupport517_suffix_001, ridgeSupport517_suffix_002, ridgeSupport517_suffix_003, ridgeSupport517_suffix_004, ridgeSupport517_suffix_005, ridgeSupport517_suffix_006, ridgeSupport517_suffix_007, ridgeSupport517_suffix_008, ridgeSupport517_suffix_009, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport517_000_mask, ridgeSupport517_001_mask, ridgeSupport517_002_mask, ridgeSupport517_003_mask, ridgeSupport517_004_mask, ridgeSupport517_005_mask, ridgeSupport517_006_mask, ridgeSupport517_007_mask, ridgeSupport517_008_mask]
    decide +kernel
  · rw [ridgeSupport517_eq]
    simp only [ridgeSupport517_suffix_000, ridgeSupport517_suffix_001, ridgeSupport517_suffix_002, ridgeSupport517_suffix_003, ridgeSupport517_suffix_004, ridgeSupport517_suffix_005, ridgeSupport517_suffix_006, ridgeSupport517_suffix_007, ridgeSupport517_suffix_008, ridgeSupport517_suffix_009, List.all_append, List.all_nil, ridgeSupport517_000_checked, ridgeSupport517_001_checked, ridgeSupport517_002_checked, ridgeSupport517_003_checked, ridgeSupport517_004_checked, ridgeSupport517_005_checked, ridgeSupport517_006_checked, ridgeSupport517_007_checked, ridgeSupport517_008_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixExtra00
