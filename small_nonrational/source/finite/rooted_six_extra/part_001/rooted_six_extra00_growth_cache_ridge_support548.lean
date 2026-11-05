module
prelude
public import RootedSixExtra00GrowthCacheRidgeSupport548Part000
public import RootedSixExtra00GrowthCacheRidgeSupport548Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra00
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport548_suffix_decode_009 : PackedRawNatGrowth.readList 14 0 ridgeSupport548_rest_009 =
    (ridgeSupport548_suffix_009, ridgeSupport548_rest_009) := by rfl
theorem ridgeSupport548_suffix_decode_008 : PackedRawNatGrowth.readList 14 7 ridgeSupport548_rest_008 =
    (ridgeSupport548_suffix_008, ridgeSupport548_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 7 0
    ridgeSupport548_rest_008 ridgeSupport548_rest_009 ridgeSupport548_rest_009
    ridgeSupport548_008 ridgeSupport548_suffix_009 ridgeSupport548_008_decode ridgeSupport548_suffix_decode_009
theorem ridgeSupport548_suffix_decode_007 : PackedRawNatGrowth.readList 14 39 ridgeSupport548_rest_007 =
    (ridgeSupport548_suffix_007, ridgeSupport548_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 7
    ridgeSupport548_rest_007 ridgeSupport548_rest_008 ridgeSupport548_rest_009
    ridgeSupport548_007 ridgeSupport548_suffix_008 ridgeSupport548_007_decode ridgeSupport548_suffix_decode_008
theorem ridgeSupport548_suffix_decode_006 : PackedRawNatGrowth.readList 14 71 ridgeSupport548_rest_006 =
    (ridgeSupport548_suffix_006, ridgeSupport548_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 39
    ridgeSupport548_rest_006 ridgeSupport548_rest_007 ridgeSupport548_rest_009
    ridgeSupport548_006 ridgeSupport548_suffix_007 ridgeSupport548_006_decode ridgeSupport548_suffix_decode_007
theorem ridgeSupport548_suffix_decode_005 : PackedRawNatGrowth.readList 14 103 ridgeSupport548_rest_005 =
    (ridgeSupport548_suffix_005, ridgeSupport548_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 71
    ridgeSupport548_rest_005 ridgeSupport548_rest_006 ridgeSupport548_rest_009
    ridgeSupport548_005 ridgeSupport548_suffix_006 ridgeSupport548_005_decode ridgeSupport548_suffix_decode_006
theorem ridgeSupport548_suffix_decode_004 : PackedRawNatGrowth.readList 14 135 ridgeSupport548_rest_004 =
    (ridgeSupport548_suffix_004, ridgeSupport548_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 103
    ridgeSupport548_rest_004 ridgeSupport548_rest_005 ridgeSupport548_rest_009
    ridgeSupport548_004 ridgeSupport548_suffix_005 ridgeSupport548_004_decode ridgeSupport548_suffix_decode_005
theorem ridgeSupport548_suffix_decode_003 : PackedRawNatGrowth.readList 14 167 ridgeSupport548_rest_003 =
    (ridgeSupport548_suffix_003, ridgeSupport548_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 135
    ridgeSupport548_rest_003 ridgeSupport548_rest_004 ridgeSupport548_rest_009
    ridgeSupport548_003 ridgeSupport548_suffix_004 ridgeSupport548_003_decode ridgeSupport548_suffix_decode_004
theorem ridgeSupport548_suffix_decode_002 : PackedRawNatGrowth.readList 14 199 ridgeSupport548_rest_002 =
    (ridgeSupport548_suffix_002, ridgeSupport548_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 167
    ridgeSupport548_rest_002 ridgeSupport548_rest_003 ridgeSupport548_rest_009
    ridgeSupport548_002 ridgeSupport548_suffix_003 ridgeSupport548_002_decode ridgeSupport548_suffix_decode_003
theorem ridgeSupport548_suffix_decode_001 : PackedRawNatGrowth.readList 14 231 ridgeSupport548_rest_001 =
    (ridgeSupport548_suffix_001, ridgeSupport548_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 199
    ridgeSupport548_rest_001 ridgeSupport548_rest_002 ridgeSupport548_rest_009
    ridgeSupport548_001 ridgeSupport548_suffix_002 ridgeSupport548_001_decode ridgeSupport548_suffix_decode_002
theorem ridgeSupport548_suffix_decode_000 : PackedRawNatGrowth.readList 14 263 ridgeSupport548_rest_000 =
    (ridgeSupport548_suffix_000, ridgeSupport548_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 231
    ridgeSupport548_rest_000 ridgeSupport548_rest_001 ridgeSupport548_rest_009
    ridgeSupport548_000 ridgeSupport548_suffix_001 ridgeSupport548_000_decode ridgeSupport548_suffix_decode_001
theorem ridgeSupport548_eq : candidateRows 548 = ridgeSupport548_suffix_000 := by
  change candidateSupports 548 = ridgeSupport548_suffix_000
  rw [ridgeSupport548_source]
  exact congrArg Prod.fst ridgeSupport548_suffix_decode_000
theorem ridgeTest_large_548 : ridgeTest 548 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport548_eq]
    simp only [ridgeSupport548_suffix_000, ridgeSupport548_suffix_001, ridgeSupport548_suffix_002, ridgeSupport548_suffix_003, ridgeSupport548_suffix_004, ridgeSupport548_suffix_005, ridgeSupport548_suffix_006, ridgeSupport548_suffix_007, ridgeSupport548_suffix_008, ridgeSupport548_suffix_009, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport548_000_mask, ridgeSupport548_001_mask, ridgeSupport548_002_mask, ridgeSupport548_003_mask, ridgeSupport548_004_mask, ridgeSupport548_005_mask, ridgeSupport548_006_mask, ridgeSupport548_007_mask, ridgeSupport548_008_mask]
    decide +kernel
  · rw [ridgeSupport548_eq]
    simp only [ridgeSupport548_suffix_000, ridgeSupport548_suffix_001, ridgeSupport548_suffix_002, ridgeSupport548_suffix_003, ridgeSupport548_suffix_004, ridgeSupport548_suffix_005, ridgeSupport548_suffix_006, ridgeSupport548_suffix_007, ridgeSupport548_suffix_008, ridgeSupport548_suffix_009, List.all_append, List.all_nil, ridgeSupport548_000_checked, ridgeSupport548_001_checked, ridgeSupport548_002_checked, ridgeSupport548_003_checked, ridgeSupport548_004_checked, ridgeSupport548_005_checked, ridgeSupport548_006_checked, ridgeSupport548_007_checked, ridgeSupport548_008_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixExtra00
