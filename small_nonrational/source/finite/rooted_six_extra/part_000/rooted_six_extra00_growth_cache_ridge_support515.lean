module
prelude
public import RootedSixExtra00GrowthCacheRidgeSupport515Part000
public import RootedSixExtra00GrowthCacheRidgeSupport515Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra00
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport515_suffix_decode_009 : PackedRawNatGrowth.readList 14 0 ridgeSupport515_rest_009 =
    (ridgeSupport515_suffix_009, ridgeSupport515_rest_009) := by rfl
theorem ridgeSupport515_suffix_decode_008 : PackedRawNatGrowth.readList 14 7 ridgeSupport515_rest_008 =
    (ridgeSupport515_suffix_008, ridgeSupport515_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 7 0
    ridgeSupport515_rest_008 ridgeSupport515_rest_009 ridgeSupport515_rest_009
    ridgeSupport515_008 ridgeSupport515_suffix_009 ridgeSupport515_008_decode ridgeSupport515_suffix_decode_009
theorem ridgeSupport515_suffix_decode_007 : PackedRawNatGrowth.readList 14 39 ridgeSupport515_rest_007 =
    (ridgeSupport515_suffix_007, ridgeSupport515_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 7
    ridgeSupport515_rest_007 ridgeSupport515_rest_008 ridgeSupport515_rest_009
    ridgeSupport515_007 ridgeSupport515_suffix_008 ridgeSupport515_007_decode ridgeSupport515_suffix_decode_008
theorem ridgeSupport515_suffix_decode_006 : PackedRawNatGrowth.readList 14 71 ridgeSupport515_rest_006 =
    (ridgeSupport515_suffix_006, ridgeSupport515_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 39
    ridgeSupport515_rest_006 ridgeSupport515_rest_007 ridgeSupport515_rest_009
    ridgeSupport515_006 ridgeSupport515_suffix_007 ridgeSupport515_006_decode ridgeSupport515_suffix_decode_007
theorem ridgeSupport515_suffix_decode_005 : PackedRawNatGrowth.readList 14 103 ridgeSupport515_rest_005 =
    (ridgeSupport515_suffix_005, ridgeSupport515_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 71
    ridgeSupport515_rest_005 ridgeSupport515_rest_006 ridgeSupport515_rest_009
    ridgeSupport515_005 ridgeSupport515_suffix_006 ridgeSupport515_005_decode ridgeSupport515_suffix_decode_006
theorem ridgeSupport515_suffix_decode_004 : PackedRawNatGrowth.readList 14 135 ridgeSupport515_rest_004 =
    (ridgeSupport515_suffix_004, ridgeSupport515_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 103
    ridgeSupport515_rest_004 ridgeSupport515_rest_005 ridgeSupport515_rest_009
    ridgeSupport515_004 ridgeSupport515_suffix_005 ridgeSupport515_004_decode ridgeSupport515_suffix_decode_005
theorem ridgeSupport515_suffix_decode_003 : PackedRawNatGrowth.readList 14 167 ridgeSupport515_rest_003 =
    (ridgeSupport515_suffix_003, ridgeSupport515_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 135
    ridgeSupport515_rest_003 ridgeSupport515_rest_004 ridgeSupport515_rest_009
    ridgeSupport515_003 ridgeSupport515_suffix_004 ridgeSupport515_003_decode ridgeSupport515_suffix_decode_004
theorem ridgeSupport515_suffix_decode_002 : PackedRawNatGrowth.readList 14 199 ridgeSupport515_rest_002 =
    (ridgeSupport515_suffix_002, ridgeSupport515_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 167
    ridgeSupport515_rest_002 ridgeSupport515_rest_003 ridgeSupport515_rest_009
    ridgeSupport515_002 ridgeSupport515_suffix_003 ridgeSupport515_002_decode ridgeSupport515_suffix_decode_003
theorem ridgeSupport515_suffix_decode_001 : PackedRawNatGrowth.readList 14 231 ridgeSupport515_rest_001 =
    (ridgeSupport515_suffix_001, ridgeSupport515_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 199
    ridgeSupport515_rest_001 ridgeSupport515_rest_002 ridgeSupport515_rest_009
    ridgeSupport515_001 ridgeSupport515_suffix_002 ridgeSupport515_001_decode ridgeSupport515_suffix_decode_002
theorem ridgeSupport515_suffix_decode_000 : PackedRawNatGrowth.readList 14 263 ridgeSupport515_rest_000 =
    (ridgeSupport515_suffix_000, ridgeSupport515_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 231
    ridgeSupport515_rest_000 ridgeSupport515_rest_001 ridgeSupport515_rest_009
    ridgeSupport515_000 ridgeSupport515_suffix_001 ridgeSupport515_000_decode ridgeSupport515_suffix_decode_001
theorem ridgeSupport515_eq : candidateRows 515 = ridgeSupport515_suffix_000 := by
  change candidateSupports 515 = ridgeSupport515_suffix_000
  rw [ridgeSupport515_source]
  exact congrArg Prod.fst ridgeSupport515_suffix_decode_000
theorem ridgeTest_large_515 : ridgeTest 515 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport515_eq]
    simp only [ridgeSupport515_suffix_000, ridgeSupport515_suffix_001, ridgeSupport515_suffix_002, ridgeSupport515_suffix_003, ridgeSupport515_suffix_004, ridgeSupport515_suffix_005, ridgeSupport515_suffix_006, ridgeSupport515_suffix_007, ridgeSupport515_suffix_008, ridgeSupport515_suffix_009, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport515_000_mask, ridgeSupport515_001_mask, ridgeSupport515_002_mask, ridgeSupport515_003_mask, ridgeSupport515_004_mask, ridgeSupport515_005_mask, ridgeSupport515_006_mask, ridgeSupport515_007_mask, ridgeSupport515_008_mask]
    decide +kernel
  · rw [ridgeSupport515_eq]
    simp only [ridgeSupport515_suffix_000, ridgeSupport515_suffix_001, ridgeSupport515_suffix_002, ridgeSupport515_suffix_003, ridgeSupport515_suffix_004, ridgeSupport515_suffix_005, ridgeSupport515_suffix_006, ridgeSupport515_suffix_007, ridgeSupport515_suffix_008, ridgeSupport515_suffix_009, List.all_append, List.all_nil, ridgeSupport515_000_checked, ridgeSupport515_001_checked, ridgeSupport515_002_checked, ridgeSupport515_003_checked, ridgeSupport515_004_checked, ridgeSupport515_005_checked, ridgeSupport515_006_checked, ridgeSupport515_007_checked, ridgeSupport515_008_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixExtra00
