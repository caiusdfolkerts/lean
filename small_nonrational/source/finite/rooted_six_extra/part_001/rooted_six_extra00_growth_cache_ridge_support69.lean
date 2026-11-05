module
prelude
public import RootedSixExtra00GrowthCacheRidgeSupport69Part000
public import RootedSixExtra00GrowthCacheRidgeSupport69Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra00
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport69_suffix_decode_009 : PackedRawNatGrowth.readList 14 0 ridgeSupport69_rest_009 =
    (ridgeSupport69_suffix_009, ridgeSupport69_rest_009) := by rfl
theorem ridgeSupport69_suffix_decode_008 : PackedRawNatGrowth.readList 14 7 ridgeSupport69_rest_008 =
    (ridgeSupport69_suffix_008, ridgeSupport69_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 7 0
    ridgeSupport69_rest_008 ridgeSupport69_rest_009 ridgeSupport69_rest_009
    ridgeSupport69_008 ridgeSupport69_suffix_009 ridgeSupport69_008_decode ridgeSupport69_suffix_decode_009
theorem ridgeSupport69_suffix_decode_007 : PackedRawNatGrowth.readList 14 39 ridgeSupport69_rest_007 =
    (ridgeSupport69_suffix_007, ridgeSupport69_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 7
    ridgeSupport69_rest_007 ridgeSupport69_rest_008 ridgeSupport69_rest_009
    ridgeSupport69_007 ridgeSupport69_suffix_008 ridgeSupport69_007_decode ridgeSupport69_suffix_decode_008
theorem ridgeSupport69_suffix_decode_006 : PackedRawNatGrowth.readList 14 71 ridgeSupport69_rest_006 =
    (ridgeSupport69_suffix_006, ridgeSupport69_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 39
    ridgeSupport69_rest_006 ridgeSupport69_rest_007 ridgeSupport69_rest_009
    ridgeSupport69_006 ridgeSupport69_suffix_007 ridgeSupport69_006_decode ridgeSupport69_suffix_decode_007
theorem ridgeSupport69_suffix_decode_005 : PackedRawNatGrowth.readList 14 103 ridgeSupport69_rest_005 =
    (ridgeSupport69_suffix_005, ridgeSupport69_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 71
    ridgeSupport69_rest_005 ridgeSupport69_rest_006 ridgeSupport69_rest_009
    ridgeSupport69_005 ridgeSupport69_suffix_006 ridgeSupport69_005_decode ridgeSupport69_suffix_decode_006
theorem ridgeSupport69_suffix_decode_004 : PackedRawNatGrowth.readList 14 135 ridgeSupport69_rest_004 =
    (ridgeSupport69_suffix_004, ridgeSupport69_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 103
    ridgeSupport69_rest_004 ridgeSupport69_rest_005 ridgeSupport69_rest_009
    ridgeSupport69_004 ridgeSupport69_suffix_005 ridgeSupport69_004_decode ridgeSupport69_suffix_decode_005
theorem ridgeSupport69_suffix_decode_003 : PackedRawNatGrowth.readList 14 167 ridgeSupport69_rest_003 =
    (ridgeSupport69_suffix_003, ridgeSupport69_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 135
    ridgeSupport69_rest_003 ridgeSupport69_rest_004 ridgeSupport69_rest_009
    ridgeSupport69_003 ridgeSupport69_suffix_004 ridgeSupport69_003_decode ridgeSupport69_suffix_decode_004
theorem ridgeSupport69_suffix_decode_002 : PackedRawNatGrowth.readList 14 199 ridgeSupport69_rest_002 =
    (ridgeSupport69_suffix_002, ridgeSupport69_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 167
    ridgeSupport69_rest_002 ridgeSupport69_rest_003 ridgeSupport69_rest_009
    ridgeSupport69_002 ridgeSupport69_suffix_003 ridgeSupport69_002_decode ridgeSupport69_suffix_decode_003
theorem ridgeSupport69_suffix_decode_001 : PackedRawNatGrowth.readList 14 231 ridgeSupport69_rest_001 =
    (ridgeSupport69_suffix_001, ridgeSupport69_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 199
    ridgeSupport69_rest_001 ridgeSupport69_rest_002 ridgeSupport69_rest_009
    ridgeSupport69_001 ridgeSupport69_suffix_002 ridgeSupport69_001_decode ridgeSupport69_suffix_decode_002
theorem ridgeSupport69_suffix_decode_000 : PackedRawNatGrowth.readList 14 263 ridgeSupport69_rest_000 =
    (ridgeSupport69_suffix_000, ridgeSupport69_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 231
    ridgeSupport69_rest_000 ridgeSupport69_rest_001 ridgeSupport69_rest_009
    ridgeSupport69_000 ridgeSupport69_suffix_001 ridgeSupport69_000_decode ridgeSupport69_suffix_decode_001
theorem ridgeSupport69_eq : candidateRows 69 = ridgeSupport69_suffix_000 := by
  change candidateSupports 69 = ridgeSupport69_suffix_000
  rw [ridgeSupport69_source]
  exact congrArg Prod.fst ridgeSupport69_suffix_decode_000
theorem ridgeTest_large_69 : ridgeTest 69 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport69_eq]
    simp only [ridgeSupport69_suffix_000, ridgeSupport69_suffix_001, ridgeSupport69_suffix_002, ridgeSupport69_suffix_003, ridgeSupport69_suffix_004, ridgeSupport69_suffix_005, ridgeSupport69_suffix_006, ridgeSupport69_suffix_007, ridgeSupport69_suffix_008, ridgeSupport69_suffix_009, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport69_000_mask, ridgeSupport69_001_mask, ridgeSupport69_002_mask, ridgeSupport69_003_mask, ridgeSupport69_004_mask, ridgeSupport69_005_mask, ridgeSupport69_006_mask, ridgeSupport69_007_mask, ridgeSupport69_008_mask]
    decide +kernel
  · rw [ridgeSupport69_eq]
    simp only [ridgeSupport69_suffix_000, ridgeSupport69_suffix_001, ridgeSupport69_suffix_002, ridgeSupport69_suffix_003, ridgeSupport69_suffix_004, ridgeSupport69_suffix_005, ridgeSupport69_suffix_006, ridgeSupport69_suffix_007, ridgeSupport69_suffix_008, ridgeSupport69_suffix_009, List.all_append, List.all_nil, ridgeSupport69_000_checked, ridgeSupport69_001_checked, ridgeSupport69_002_checked, ridgeSupport69_003_checked, ridgeSupport69_004_checked, ridgeSupport69_005_checked, ridgeSupport69_006_checked, ridgeSupport69_007_checked, ridgeSupport69_008_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixExtra00
