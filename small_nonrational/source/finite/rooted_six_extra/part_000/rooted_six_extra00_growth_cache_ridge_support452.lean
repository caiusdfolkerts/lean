module
prelude
public import RootedSixExtra00GrowthCacheRidgeSupport452Part000
public import RootedSixExtra00GrowthCacheRidgeSupport452Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra00
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport452_suffix_decode_009 : PackedRawNatGrowth.readList 14 0 ridgeSupport452_rest_009 =
    (ridgeSupport452_suffix_009, ridgeSupport452_rest_009) := by rfl
theorem ridgeSupport452_suffix_decode_008 : PackedRawNatGrowth.readList 14 2 ridgeSupport452_rest_008 =
    (ridgeSupport452_suffix_008, ridgeSupport452_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 2 0
    ridgeSupport452_rest_008 ridgeSupport452_rest_009 ridgeSupport452_rest_009
    ridgeSupport452_008 ridgeSupport452_suffix_009 ridgeSupport452_008_decode ridgeSupport452_suffix_decode_009
theorem ridgeSupport452_suffix_decode_007 : PackedRawNatGrowth.readList 14 34 ridgeSupport452_rest_007 =
    (ridgeSupport452_suffix_007, ridgeSupport452_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 2
    ridgeSupport452_rest_007 ridgeSupport452_rest_008 ridgeSupport452_rest_009
    ridgeSupport452_007 ridgeSupport452_suffix_008 ridgeSupport452_007_decode ridgeSupport452_suffix_decode_008
theorem ridgeSupport452_suffix_decode_006 : PackedRawNatGrowth.readList 14 66 ridgeSupport452_rest_006 =
    (ridgeSupport452_suffix_006, ridgeSupport452_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 34
    ridgeSupport452_rest_006 ridgeSupport452_rest_007 ridgeSupport452_rest_009
    ridgeSupport452_006 ridgeSupport452_suffix_007 ridgeSupport452_006_decode ridgeSupport452_suffix_decode_007
theorem ridgeSupport452_suffix_decode_005 : PackedRawNatGrowth.readList 14 98 ridgeSupport452_rest_005 =
    (ridgeSupport452_suffix_005, ridgeSupport452_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 66
    ridgeSupport452_rest_005 ridgeSupport452_rest_006 ridgeSupport452_rest_009
    ridgeSupport452_005 ridgeSupport452_suffix_006 ridgeSupport452_005_decode ridgeSupport452_suffix_decode_006
theorem ridgeSupport452_suffix_decode_004 : PackedRawNatGrowth.readList 14 130 ridgeSupport452_rest_004 =
    (ridgeSupport452_suffix_004, ridgeSupport452_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 98
    ridgeSupport452_rest_004 ridgeSupport452_rest_005 ridgeSupport452_rest_009
    ridgeSupport452_004 ridgeSupport452_suffix_005 ridgeSupport452_004_decode ridgeSupport452_suffix_decode_005
theorem ridgeSupport452_suffix_decode_003 : PackedRawNatGrowth.readList 14 162 ridgeSupport452_rest_003 =
    (ridgeSupport452_suffix_003, ridgeSupport452_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 130
    ridgeSupport452_rest_003 ridgeSupport452_rest_004 ridgeSupport452_rest_009
    ridgeSupport452_003 ridgeSupport452_suffix_004 ridgeSupport452_003_decode ridgeSupport452_suffix_decode_004
theorem ridgeSupport452_suffix_decode_002 : PackedRawNatGrowth.readList 14 194 ridgeSupport452_rest_002 =
    (ridgeSupport452_suffix_002, ridgeSupport452_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 162
    ridgeSupport452_rest_002 ridgeSupport452_rest_003 ridgeSupport452_rest_009
    ridgeSupport452_002 ridgeSupport452_suffix_003 ridgeSupport452_002_decode ridgeSupport452_suffix_decode_003
theorem ridgeSupport452_suffix_decode_001 : PackedRawNatGrowth.readList 14 226 ridgeSupport452_rest_001 =
    (ridgeSupport452_suffix_001, ridgeSupport452_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 194
    ridgeSupport452_rest_001 ridgeSupport452_rest_002 ridgeSupport452_rest_009
    ridgeSupport452_001 ridgeSupport452_suffix_002 ridgeSupport452_001_decode ridgeSupport452_suffix_decode_002
theorem ridgeSupport452_suffix_decode_000 : PackedRawNatGrowth.readList 14 258 ridgeSupport452_rest_000 =
    (ridgeSupport452_suffix_000, ridgeSupport452_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 226
    ridgeSupport452_rest_000 ridgeSupport452_rest_001 ridgeSupport452_rest_009
    ridgeSupport452_000 ridgeSupport452_suffix_001 ridgeSupport452_000_decode ridgeSupport452_suffix_decode_001
theorem ridgeSupport452_eq : candidateRows 452 = ridgeSupport452_suffix_000 := by
  change candidateSupports 452 = ridgeSupport452_suffix_000
  rw [ridgeSupport452_source]
  exact congrArg Prod.fst ridgeSupport452_suffix_decode_000
theorem ridgeTest_large_452 : ridgeTest 452 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport452_eq]
    simp only [ridgeSupport452_suffix_000, ridgeSupport452_suffix_001, ridgeSupport452_suffix_002, ridgeSupport452_suffix_003, ridgeSupport452_suffix_004, ridgeSupport452_suffix_005, ridgeSupport452_suffix_006, ridgeSupport452_suffix_007, ridgeSupport452_suffix_008, ridgeSupport452_suffix_009, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport452_000_mask, ridgeSupport452_001_mask, ridgeSupport452_002_mask, ridgeSupport452_003_mask, ridgeSupport452_004_mask, ridgeSupport452_005_mask, ridgeSupport452_006_mask, ridgeSupport452_007_mask, ridgeSupport452_008_mask]
    decide +kernel
  · rw [ridgeSupport452_eq]
    simp only [ridgeSupport452_suffix_000, ridgeSupport452_suffix_001, ridgeSupport452_suffix_002, ridgeSupport452_suffix_003, ridgeSupport452_suffix_004, ridgeSupport452_suffix_005, ridgeSupport452_suffix_006, ridgeSupport452_suffix_007, ridgeSupport452_suffix_008, ridgeSupport452_suffix_009, List.all_append, List.all_nil, ridgeSupport452_000_checked, ridgeSupport452_001_checked, ridgeSupport452_002_checked, ridgeSupport452_003_checked, ridgeSupport452_004_checked, ridgeSupport452_005_checked, ridgeSupport452_006_checked, ridgeSupport452_007_checked, ridgeSupport452_008_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixExtra00
