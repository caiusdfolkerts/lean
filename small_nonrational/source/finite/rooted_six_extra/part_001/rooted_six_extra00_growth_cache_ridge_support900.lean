module
prelude
public import RootedSixExtra00GrowthCacheRidgeSupport900Part000
public import RootedSixExtra00GrowthCacheRidgeSupport900Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra00
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport900_suffix_decode_009 : PackedRawNatGrowth.readList 14 0 ridgeSupport900_rest_009 =
    (ridgeSupport900_suffix_009, ridgeSupport900_rest_009) := by rfl
theorem ridgeSupport900_suffix_decode_008 : PackedRawNatGrowth.readList 14 2 ridgeSupport900_rest_008 =
    (ridgeSupport900_suffix_008, ridgeSupport900_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 2 0
    ridgeSupport900_rest_008 ridgeSupport900_rest_009 ridgeSupport900_rest_009
    ridgeSupport900_008 ridgeSupport900_suffix_009 ridgeSupport900_008_decode ridgeSupport900_suffix_decode_009
theorem ridgeSupport900_suffix_decode_007 : PackedRawNatGrowth.readList 14 34 ridgeSupport900_rest_007 =
    (ridgeSupport900_suffix_007, ridgeSupport900_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 2
    ridgeSupport900_rest_007 ridgeSupport900_rest_008 ridgeSupport900_rest_009
    ridgeSupport900_007 ridgeSupport900_suffix_008 ridgeSupport900_007_decode ridgeSupport900_suffix_decode_008
theorem ridgeSupport900_suffix_decode_006 : PackedRawNatGrowth.readList 14 66 ridgeSupport900_rest_006 =
    (ridgeSupport900_suffix_006, ridgeSupport900_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 34
    ridgeSupport900_rest_006 ridgeSupport900_rest_007 ridgeSupport900_rest_009
    ridgeSupport900_006 ridgeSupport900_suffix_007 ridgeSupport900_006_decode ridgeSupport900_suffix_decode_007
theorem ridgeSupport900_suffix_decode_005 : PackedRawNatGrowth.readList 14 98 ridgeSupport900_rest_005 =
    (ridgeSupport900_suffix_005, ridgeSupport900_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 66
    ridgeSupport900_rest_005 ridgeSupport900_rest_006 ridgeSupport900_rest_009
    ridgeSupport900_005 ridgeSupport900_suffix_006 ridgeSupport900_005_decode ridgeSupport900_suffix_decode_006
theorem ridgeSupport900_suffix_decode_004 : PackedRawNatGrowth.readList 14 130 ridgeSupport900_rest_004 =
    (ridgeSupport900_suffix_004, ridgeSupport900_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 98
    ridgeSupport900_rest_004 ridgeSupport900_rest_005 ridgeSupport900_rest_009
    ridgeSupport900_004 ridgeSupport900_suffix_005 ridgeSupport900_004_decode ridgeSupport900_suffix_decode_005
theorem ridgeSupport900_suffix_decode_003 : PackedRawNatGrowth.readList 14 162 ridgeSupport900_rest_003 =
    (ridgeSupport900_suffix_003, ridgeSupport900_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 130
    ridgeSupport900_rest_003 ridgeSupport900_rest_004 ridgeSupport900_rest_009
    ridgeSupport900_003 ridgeSupport900_suffix_004 ridgeSupport900_003_decode ridgeSupport900_suffix_decode_004
theorem ridgeSupport900_suffix_decode_002 : PackedRawNatGrowth.readList 14 194 ridgeSupport900_rest_002 =
    (ridgeSupport900_suffix_002, ridgeSupport900_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 162
    ridgeSupport900_rest_002 ridgeSupport900_rest_003 ridgeSupport900_rest_009
    ridgeSupport900_002 ridgeSupport900_suffix_003 ridgeSupport900_002_decode ridgeSupport900_suffix_decode_003
theorem ridgeSupport900_suffix_decode_001 : PackedRawNatGrowth.readList 14 226 ridgeSupport900_rest_001 =
    (ridgeSupport900_suffix_001, ridgeSupport900_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 194
    ridgeSupport900_rest_001 ridgeSupport900_rest_002 ridgeSupport900_rest_009
    ridgeSupport900_001 ridgeSupport900_suffix_002 ridgeSupport900_001_decode ridgeSupport900_suffix_decode_002
theorem ridgeSupport900_suffix_decode_000 : PackedRawNatGrowth.readList 14 258 ridgeSupport900_rest_000 =
    (ridgeSupport900_suffix_000, ridgeSupport900_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 226
    ridgeSupport900_rest_000 ridgeSupport900_rest_001 ridgeSupport900_rest_009
    ridgeSupport900_000 ridgeSupport900_suffix_001 ridgeSupport900_000_decode ridgeSupport900_suffix_decode_001
theorem ridgeSupport900_eq : candidateRows 900 = ridgeSupport900_suffix_000 := by
  change candidateSupports 900 = ridgeSupport900_suffix_000
  rw [ridgeSupport900_source]
  exact congrArg Prod.fst ridgeSupport900_suffix_decode_000
theorem ridgeTest_large_900 : ridgeTest 900 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport900_eq]
    simp only [ridgeSupport900_suffix_000, ridgeSupport900_suffix_001, ridgeSupport900_suffix_002, ridgeSupport900_suffix_003, ridgeSupport900_suffix_004, ridgeSupport900_suffix_005, ridgeSupport900_suffix_006, ridgeSupport900_suffix_007, ridgeSupport900_suffix_008, ridgeSupport900_suffix_009, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport900_000_mask, ridgeSupport900_001_mask, ridgeSupport900_002_mask, ridgeSupport900_003_mask, ridgeSupport900_004_mask, ridgeSupport900_005_mask, ridgeSupport900_006_mask, ridgeSupport900_007_mask, ridgeSupport900_008_mask]
    decide +kernel
  · rw [ridgeSupport900_eq]
    simp only [ridgeSupport900_suffix_000, ridgeSupport900_suffix_001, ridgeSupport900_suffix_002, ridgeSupport900_suffix_003, ridgeSupport900_suffix_004, ridgeSupport900_suffix_005, ridgeSupport900_suffix_006, ridgeSupport900_suffix_007, ridgeSupport900_suffix_008, ridgeSupport900_suffix_009, List.all_append, List.all_nil, ridgeSupport900_000_checked, ridgeSupport900_001_checked, ridgeSupport900_002_checked, ridgeSupport900_003_checked, ridgeSupport900_004_checked, ridgeSupport900_005_checked, ridgeSupport900_006_checked, ridgeSupport900_007_checked, ridgeSupport900_008_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixExtra00
