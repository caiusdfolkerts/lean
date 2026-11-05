module
prelude
public import RootedSixExtra00GrowthCacheRidgeSupport904Part000
public import RootedSixExtra00GrowthCacheRidgeSupport904Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra00
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport904_suffix_decode_009 : PackedRawNatGrowth.readList 14 0 ridgeSupport904_rest_009 =
    (ridgeSupport904_suffix_009, ridgeSupport904_rest_009) := by rfl
theorem ridgeSupport904_suffix_decode_008 : PackedRawNatGrowth.readList 14 2 ridgeSupport904_rest_008 =
    (ridgeSupport904_suffix_008, ridgeSupport904_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 2 0
    ridgeSupport904_rest_008 ridgeSupport904_rest_009 ridgeSupport904_rest_009
    ridgeSupport904_008 ridgeSupport904_suffix_009 ridgeSupport904_008_decode ridgeSupport904_suffix_decode_009
theorem ridgeSupport904_suffix_decode_007 : PackedRawNatGrowth.readList 14 34 ridgeSupport904_rest_007 =
    (ridgeSupport904_suffix_007, ridgeSupport904_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 2
    ridgeSupport904_rest_007 ridgeSupport904_rest_008 ridgeSupport904_rest_009
    ridgeSupport904_007 ridgeSupport904_suffix_008 ridgeSupport904_007_decode ridgeSupport904_suffix_decode_008
theorem ridgeSupport904_suffix_decode_006 : PackedRawNatGrowth.readList 14 66 ridgeSupport904_rest_006 =
    (ridgeSupport904_suffix_006, ridgeSupport904_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 34
    ridgeSupport904_rest_006 ridgeSupport904_rest_007 ridgeSupport904_rest_009
    ridgeSupport904_006 ridgeSupport904_suffix_007 ridgeSupport904_006_decode ridgeSupport904_suffix_decode_007
theorem ridgeSupport904_suffix_decode_005 : PackedRawNatGrowth.readList 14 98 ridgeSupport904_rest_005 =
    (ridgeSupport904_suffix_005, ridgeSupport904_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 66
    ridgeSupport904_rest_005 ridgeSupport904_rest_006 ridgeSupport904_rest_009
    ridgeSupport904_005 ridgeSupport904_suffix_006 ridgeSupport904_005_decode ridgeSupport904_suffix_decode_006
theorem ridgeSupport904_suffix_decode_004 : PackedRawNatGrowth.readList 14 130 ridgeSupport904_rest_004 =
    (ridgeSupport904_suffix_004, ridgeSupport904_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 98
    ridgeSupport904_rest_004 ridgeSupport904_rest_005 ridgeSupport904_rest_009
    ridgeSupport904_004 ridgeSupport904_suffix_005 ridgeSupport904_004_decode ridgeSupport904_suffix_decode_005
theorem ridgeSupport904_suffix_decode_003 : PackedRawNatGrowth.readList 14 162 ridgeSupport904_rest_003 =
    (ridgeSupport904_suffix_003, ridgeSupport904_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 130
    ridgeSupport904_rest_003 ridgeSupport904_rest_004 ridgeSupport904_rest_009
    ridgeSupport904_003 ridgeSupport904_suffix_004 ridgeSupport904_003_decode ridgeSupport904_suffix_decode_004
theorem ridgeSupport904_suffix_decode_002 : PackedRawNatGrowth.readList 14 194 ridgeSupport904_rest_002 =
    (ridgeSupport904_suffix_002, ridgeSupport904_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 162
    ridgeSupport904_rest_002 ridgeSupport904_rest_003 ridgeSupport904_rest_009
    ridgeSupport904_002 ridgeSupport904_suffix_003 ridgeSupport904_002_decode ridgeSupport904_suffix_decode_003
theorem ridgeSupport904_suffix_decode_001 : PackedRawNatGrowth.readList 14 226 ridgeSupport904_rest_001 =
    (ridgeSupport904_suffix_001, ridgeSupport904_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 194
    ridgeSupport904_rest_001 ridgeSupport904_rest_002 ridgeSupport904_rest_009
    ridgeSupport904_001 ridgeSupport904_suffix_002 ridgeSupport904_001_decode ridgeSupport904_suffix_decode_002
theorem ridgeSupport904_suffix_decode_000 : PackedRawNatGrowth.readList 14 258 ridgeSupport904_rest_000 =
    (ridgeSupport904_suffix_000, ridgeSupport904_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 226
    ridgeSupport904_rest_000 ridgeSupport904_rest_001 ridgeSupport904_rest_009
    ridgeSupport904_000 ridgeSupport904_suffix_001 ridgeSupport904_000_decode ridgeSupport904_suffix_decode_001
theorem ridgeSupport904_eq : candidateRows 904 = ridgeSupport904_suffix_000 := by
  change candidateSupports 904 = ridgeSupport904_suffix_000
  rw [ridgeSupport904_source]
  exact congrArg Prod.fst ridgeSupport904_suffix_decode_000
theorem ridgeTest_large_904 : ridgeTest 904 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport904_eq]
    simp only [ridgeSupport904_suffix_000, ridgeSupport904_suffix_001, ridgeSupport904_suffix_002, ridgeSupport904_suffix_003, ridgeSupport904_suffix_004, ridgeSupport904_suffix_005, ridgeSupport904_suffix_006, ridgeSupport904_suffix_007, ridgeSupport904_suffix_008, ridgeSupport904_suffix_009, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport904_000_mask, ridgeSupport904_001_mask, ridgeSupport904_002_mask, ridgeSupport904_003_mask, ridgeSupport904_004_mask, ridgeSupport904_005_mask, ridgeSupport904_006_mask, ridgeSupport904_007_mask, ridgeSupport904_008_mask]
    decide +kernel
  · rw [ridgeSupport904_eq]
    simp only [ridgeSupport904_suffix_000, ridgeSupport904_suffix_001, ridgeSupport904_suffix_002, ridgeSupport904_suffix_003, ridgeSupport904_suffix_004, ridgeSupport904_suffix_005, ridgeSupport904_suffix_006, ridgeSupport904_suffix_007, ridgeSupport904_suffix_008, ridgeSupport904_suffix_009, List.all_append, List.all_nil, ridgeSupport904_000_checked, ridgeSupport904_001_checked, ridgeSupport904_002_checked, ridgeSupport904_003_checked, ridgeSupport904_004_checked, ridgeSupport904_005_checked, ridgeSupport904_006_checked, ridgeSupport904_007_checked, ridgeSupport904_008_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixExtra00
