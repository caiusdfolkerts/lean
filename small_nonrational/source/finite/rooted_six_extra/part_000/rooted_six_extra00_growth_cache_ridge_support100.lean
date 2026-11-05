module
prelude
public import RootedSixExtra00GrowthCacheRidgeSupport100Part000
public import RootedSixExtra00GrowthCacheRidgeSupport100Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra00
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport100_suffix_decode_009 : PackedRawNatGrowth.readList 14 0 ridgeSupport100_rest_009 =
    (ridgeSupport100_suffix_009, ridgeSupport100_rest_009) := by rfl
theorem ridgeSupport100_suffix_decode_008 : PackedRawNatGrowth.readList 14 7 ridgeSupport100_rest_008 =
    (ridgeSupport100_suffix_008, ridgeSupport100_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 7 0
    ridgeSupport100_rest_008 ridgeSupport100_rest_009 ridgeSupport100_rest_009
    ridgeSupport100_008 ridgeSupport100_suffix_009 ridgeSupport100_008_decode ridgeSupport100_suffix_decode_009
theorem ridgeSupport100_suffix_decode_007 : PackedRawNatGrowth.readList 14 39 ridgeSupport100_rest_007 =
    (ridgeSupport100_suffix_007, ridgeSupport100_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 7
    ridgeSupport100_rest_007 ridgeSupport100_rest_008 ridgeSupport100_rest_009
    ridgeSupport100_007 ridgeSupport100_suffix_008 ridgeSupport100_007_decode ridgeSupport100_suffix_decode_008
theorem ridgeSupport100_suffix_decode_006 : PackedRawNatGrowth.readList 14 71 ridgeSupport100_rest_006 =
    (ridgeSupport100_suffix_006, ridgeSupport100_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 39
    ridgeSupport100_rest_006 ridgeSupport100_rest_007 ridgeSupport100_rest_009
    ridgeSupport100_006 ridgeSupport100_suffix_007 ridgeSupport100_006_decode ridgeSupport100_suffix_decode_007
theorem ridgeSupport100_suffix_decode_005 : PackedRawNatGrowth.readList 14 103 ridgeSupport100_rest_005 =
    (ridgeSupport100_suffix_005, ridgeSupport100_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 71
    ridgeSupport100_rest_005 ridgeSupport100_rest_006 ridgeSupport100_rest_009
    ridgeSupport100_005 ridgeSupport100_suffix_006 ridgeSupport100_005_decode ridgeSupport100_suffix_decode_006
theorem ridgeSupport100_suffix_decode_004 : PackedRawNatGrowth.readList 14 135 ridgeSupport100_rest_004 =
    (ridgeSupport100_suffix_004, ridgeSupport100_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 103
    ridgeSupport100_rest_004 ridgeSupport100_rest_005 ridgeSupport100_rest_009
    ridgeSupport100_004 ridgeSupport100_suffix_005 ridgeSupport100_004_decode ridgeSupport100_suffix_decode_005
theorem ridgeSupport100_suffix_decode_003 : PackedRawNatGrowth.readList 14 167 ridgeSupport100_rest_003 =
    (ridgeSupport100_suffix_003, ridgeSupport100_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 135
    ridgeSupport100_rest_003 ridgeSupport100_rest_004 ridgeSupport100_rest_009
    ridgeSupport100_003 ridgeSupport100_suffix_004 ridgeSupport100_003_decode ridgeSupport100_suffix_decode_004
theorem ridgeSupport100_suffix_decode_002 : PackedRawNatGrowth.readList 14 199 ridgeSupport100_rest_002 =
    (ridgeSupport100_suffix_002, ridgeSupport100_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 167
    ridgeSupport100_rest_002 ridgeSupport100_rest_003 ridgeSupport100_rest_009
    ridgeSupport100_002 ridgeSupport100_suffix_003 ridgeSupport100_002_decode ridgeSupport100_suffix_decode_003
theorem ridgeSupport100_suffix_decode_001 : PackedRawNatGrowth.readList 14 231 ridgeSupport100_rest_001 =
    (ridgeSupport100_suffix_001, ridgeSupport100_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 199
    ridgeSupport100_rest_001 ridgeSupport100_rest_002 ridgeSupport100_rest_009
    ridgeSupport100_001 ridgeSupport100_suffix_002 ridgeSupport100_001_decode ridgeSupport100_suffix_decode_002
theorem ridgeSupport100_suffix_decode_000 : PackedRawNatGrowth.readList 14 263 ridgeSupport100_rest_000 =
    (ridgeSupport100_suffix_000, ridgeSupport100_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 231
    ridgeSupport100_rest_000 ridgeSupport100_rest_001 ridgeSupport100_rest_009
    ridgeSupport100_000 ridgeSupport100_suffix_001 ridgeSupport100_000_decode ridgeSupport100_suffix_decode_001
theorem ridgeSupport100_eq : candidateRows 100 = ridgeSupport100_suffix_000 := by
  change candidateSupports 100 = ridgeSupport100_suffix_000
  rw [ridgeSupport100_source]
  exact congrArg Prod.fst ridgeSupport100_suffix_decode_000
theorem ridgeTest_large_100 : ridgeTest 100 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport100_eq]
    simp only [ridgeSupport100_suffix_000, ridgeSupport100_suffix_001, ridgeSupport100_suffix_002, ridgeSupport100_suffix_003, ridgeSupport100_suffix_004, ridgeSupport100_suffix_005, ridgeSupport100_suffix_006, ridgeSupport100_suffix_007, ridgeSupport100_suffix_008, ridgeSupport100_suffix_009, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport100_000_mask, ridgeSupport100_001_mask, ridgeSupport100_002_mask, ridgeSupport100_003_mask, ridgeSupport100_004_mask, ridgeSupport100_005_mask, ridgeSupport100_006_mask, ridgeSupport100_007_mask, ridgeSupport100_008_mask]
    decide +kernel
  · rw [ridgeSupport100_eq]
    simp only [ridgeSupport100_suffix_000, ridgeSupport100_suffix_001, ridgeSupport100_suffix_002, ridgeSupport100_suffix_003, ridgeSupport100_suffix_004, ridgeSupport100_suffix_005, ridgeSupport100_suffix_006, ridgeSupport100_suffix_007, ridgeSupport100_suffix_008, ridgeSupport100_suffix_009, List.all_append, List.all_nil, ridgeSupport100_000_checked, ridgeSupport100_001_checked, ridgeSupport100_002_checked, ridgeSupport100_003_checked, ridgeSupport100_004_checked, ridgeSupport100_005_checked, ridgeSupport100_006_checked, ridgeSupport100_007_checked, ridgeSupport100_008_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixExtra00
