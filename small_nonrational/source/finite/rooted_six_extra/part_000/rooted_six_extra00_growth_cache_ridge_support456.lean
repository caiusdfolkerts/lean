module
prelude
public import RootedSixExtra00GrowthCacheRidgeSupport456Part000
public import RootedSixExtra00GrowthCacheRidgeSupport456Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra00
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport456_suffix_decode_009 : PackedRawNatGrowth.readList 14 0 ridgeSupport456_rest_009 =
    (ridgeSupport456_suffix_009, ridgeSupport456_rest_009) := by rfl
theorem ridgeSupport456_suffix_decode_008 : PackedRawNatGrowth.readList 14 2 ridgeSupport456_rest_008 =
    (ridgeSupport456_suffix_008, ridgeSupport456_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 2 0
    ridgeSupport456_rest_008 ridgeSupport456_rest_009 ridgeSupport456_rest_009
    ridgeSupport456_008 ridgeSupport456_suffix_009 ridgeSupport456_008_decode ridgeSupport456_suffix_decode_009
theorem ridgeSupport456_suffix_decode_007 : PackedRawNatGrowth.readList 14 34 ridgeSupport456_rest_007 =
    (ridgeSupport456_suffix_007, ridgeSupport456_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 2
    ridgeSupport456_rest_007 ridgeSupport456_rest_008 ridgeSupport456_rest_009
    ridgeSupport456_007 ridgeSupport456_suffix_008 ridgeSupport456_007_decode ridgeSupport456_suffix_decode_008
theorem ridgeSupport456_suffix_decode_006 : PackedRawNatGrowth.readList 14 66 ridgeSupport456_rest_006 =
    (ridgeSupport456_suffix_006, ridgeSupport456_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 34
    ridgeSupport456_rest_006 ridgeSupport456_rest_007 ridgeSupport456_rest_009
    ridgeSupport456_006 ridgeSupport456_suffix_007 ridgeSupport456_006_decode ridgeSupport456_suffix_decode_007
theorem ridgeSupport456_suffix_decode_005 : PackedRawNatGrowth.readList 14 98 ridgeSupport456_rest_005 =
    (ridgeSupport456_suffix_005, ridgeSupport456_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 66
    ridgeSupport456_rest_005 ridgeSupport456_rest_006 ridgeSupport456_rest_009
    ridgeSupport456_005 ridgeSupport456_suffix_006 ridgeSupport456_005_decode ridgeSupport456_suffix_decode_006
theorem ridgeSupport456_suffix_decode_004 : PackedRawNatGrowth.readList 14 130 ridgeSupport456_rest_004 =
    (ridgeSupport456_suffix_004, ridgeSupport456_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 98
    ridgeSupport456_rest_004 ridgeSupport456_rest_005 ridgeSupport456_rest_009
    ridgeSupport456_004 ridgeSupport456_suffix_005 ridgeSupport456_004_decode ridgeSupport456_suffix_decode_005
theorem ridgeSupport456_suffix_decode_003 : PackedRawNatGrowth.readList 14 162 ridgeSupport456_rest_003 =
    (ridgeSupport456_suffix_003, ridgeSupport456_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 130
    ridgeSupport456_rest_003 ridgeSupport456_rest_004 ridgeSupport456_rest_009
    ridgeSupport456_003 ridgeSupport456_suffix_004 ridgeSupport456_003_decode ridgeSupport456_suffix_decode_004
theorem ridgeSupport456_suffix_decode_002 : PackedRawNatGrowth.readList 14 194 ridgeSupport456_rest_002 =
    (ridgeSupport456_suffix_002, ridgeSupport456_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 162
    ridgeSupport456_rest_002 ridgeSupport456_rest_003 ridgeSupport456_rest_009
    ridgeSupport456_002 ridgeSupport456_suffix_003 ridgeSupport456_002_decode ridgeSupport456_suffix_decode_003
theorem ridgeSupport456_suffix_decode_001 : PackedRawNatGrowth.readList 14 226 ridgeSupport456_rest_001 =
    (ridgeSupport456_suffix_001, ridgeSupport456_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 194
    ridgeSupport456_rest_001 ridgeSupport456_rest_002 ridgeSupport456_rest_009
    ridgeSupport456_001 ridgeSupport456_suffix_002 ridgeSupport456_001_decode ridgeSupport456_suffix_decode_002
theorem ridgeSupport456_suffix_decode_000 : PackedRawNatGrowth.readList 14 258 ridgeSupport456_rest_000 =
    (ridgeSupport456_suffix_000, ridgeSupport456_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 226
    ridgeSupport456_rest_000 ridgeSupport456_rest_001 ridgeSupport456_rest_009
    ridgeSupport456_000 ridgeSupport456_suffix_001 ridgeSupport456_000_decode ridgeSupport456_suffix_decode_001
theorem ridgeSupport456_eq : candidateRows 456 = ridgeSupport456_suffix_000 := by
  change candidateSupports 456 = ridgeSupport456_suffix_000
  rw [ridgeSupport456_source]
  exact congrArg Prod.fst ridgeSupport456_suffix_decode_000
theorem ridgeTest_large_456 : ridgeTest 456 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport456_eq]
    simp only [ridgeSupport456_suffix_000, ridgeSupport456_suffix_001, ridgeSupport456_suffix_002, ridgeSupport456_suffix_003, ridgeSupport456_suffix_004, ridgeSupport456_suffix_005, ridgeSupport456_suffix_006, ridgeSupport456_suffix_007, ridgeSupport456_suffix_008, ridgeSupport456_suffix_009, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport456_000_mask, ridgeSupport456_001_mask, ridgeSupport456_002_mask, ridgeSupport456_003_mask, ridgeSupport456_004_mask, ridgeSupport456_005_mask, ridgeSupport456_006_mask, ridgeSupport456_007_mask, ridgeSupport456_008_mask]
    decide +kernel
  · rw [ridgeSupport456_eq]
    simp only [ridgeSupport456_suffix_000, ridgeSupport456_suffix_001, ridgeSupport456_suffix_002, ridgeSupport456_suffix_003, ridgeSupport456_suffix_004, ridgeSupport456_suffix_005, ridgeSupport456_suffix_006, ridgeSupport456_suffix_007, ridgeSupport456_suffix_008, ridgeSupport456_suffix_009, List.all_append, List.all_nil, ridgeSupport456_000_checked, ridgeSupport456_001_checked, ridgeSupport456_002_checked, ridgeSupport456_003_checked, ridgeSupport456_004_checked, ridgeSupport456_005_checked, ridgeSupport456_006_checked, ridgeSupport456_007_checked, ridgeSupport456_008_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixExtra00
