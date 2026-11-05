module
prelude
public import RootedSixExtra00GrowthCacheRidgeSupport518Part000
public import RootedSixExtra00GrowthCacheRidgeSupport518Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra00
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport518_suffix_decode_009 : PackedRawNatGrowth.readList 14 0 ridgeSupport518_rest_009 =
    (ridgeSupport518_suffix_009, ridgeSupport518_rest_009) := by rfl
theorem ridgeSupport518_suffix_decode_008 : PackedRawNatGrowth.readList 14 7 ridgeSupport518_rest_008 =
    (ridgeSupport518_suffix_008, ridgeSupport518_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 7 0
    ridgeSupport518_rest_008 ridgeSupport518_rest_009 ridgeSupport518_rest_009
    ridgeSupport518_008 ridgeSupport518_suffix_009 ridgeSupport518_008_decode ridgeSupport518_suffix_decode_009
theorem ridgeSupport518_suffix_decode_007 : PackedRawNatGrowth.readList 14 39 ridgeSupport518_rest_007 =
    (ridgeSupport518_suffix_007, ridgeSupport518_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 7
    ridgeSupport518_rest_007 ridgeSupport518_rest_008 ridgeSupport518_rest_009
    ridgeSupport518_007 ridgeSupport518_suffix_008 ridgeSupport518_007_decode ridgeSupport518_suffix_decode_008
theorem ridgeSupport518_suffix_decode_006 : PackedRawNatGrowth.readList 14 71 ridgeSupport518_rest_006 =
    (ridgeSupport518_suffix_006, ridgeSupport518_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 39
    ridgeSupport518_rest_006 ridgeSupport518_rest_007 ridgeSupport518_rest_009
    ridgeSupport518_006 ridgeSupport518_suffix_007 ridgeSupport518_006_decode ridgeSupport518_suffix_decode_007
theorem ridgeSupport518_suffix_decode_005 : PackedRawNatGrowth.readList 14 103 ridgeSupport518_rest_005 =
    (ridgeSupport518_suffix_005, ridgeSupport518_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 71
    ridgeSupport518_rest_005 ridgeSupport518_rest_006 ridgeSupport518_rest_009
    ridgeSupport518_005 ridgeSupport518_suffix_006 ridgeSupport518_005_decode ridgeSupport518_suffix_decode_006
theorem ridgeSupport518_suffix_decode_004 : PackedRawNatGrowth.readList 14 135 ridgeSupport518_rest_004 =
    (ridgeSupport518_suffix_004, ridgeSupport518_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 103
    ridgeSupport518_rest_004 ridgeSupport518_rest_005 ridgeSupport518_rest_009
    ridgeSupport518_004 ridgeSupport518_suffix_005 ridgeSupport518_004_decode ridgeSupport518_suffix_decode_005
theorem ridgeSupport518_suffix_decode_003 : PackedRawNatGrowth.readList 14 167 ridgeSupport518_rest_003 =
    (ridgeSupport518_suffix_003, ridgeSupport518_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 135
    ridgeSupport518_rest_003 ridgeSupport518_rest_004 ridgeSupport518_rest_009
    ridgeSupport518_003 ridgeSupport518_suffix_004 ridgeSupport518_003_decode ridgeSupport518_suffix_decode_004
theorem ridgeSupport518_suffix_decode_002 : PackedRawNatGrowth.readList 14 199 ridgeSupport518_rest_002 =
    (ridgeSupport518_suffix_002, ridgeSupport518_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 167
    ridgeSupport518_rest_002 ridgeSupport518_rest_003 ridgeSupport518_rest_009
    ridgeSupport518_002 ridgeSupport518_suffix_003 ridgeSupport518_002_decode ridgeSupport518_suffix_decode_003
theorem ridgeSupport518_suffix_decode_001 : PackedRawNatGrowth.readList 14 231 ridgeSupport518_rest_001 =
    (ridgeSupport518_suffix_001, ridgeSupport518_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 199
    ridgeSupport518_rest_001 ridgeSupport518_rest_002 ridgeSupport518_rest_009
    ridgeSupport518_001 ridgeSupport518_suffix_002 ridgeSupport518_001_decode ridgeSupport518_suffix_decode_002
theorem ridgeSupport518_suffix_decode_000 : PackedRawNatGrowth.readList 14 263 ridgeSupport518_rest_000 =
    (ridgeSupport518_suffix_000, ridgeSupport518_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 231
    ridgeSupport518_rest_000 ridgeSupport518_rest_001 ridgeSupport518_rest_009
    ridgeSupport518_000 ridgeSupport518_suffix_001 ridgeSupport518_000_decode ridgeSupport518_suffix_decode_001
theorem ridgeSupport518_eq : candidateRows 518 = ridgeSupport518_suffix_000 := by
  change candidateSupports 518 = ridgeSupport518_suffix_000
  rw [ridgeSupport518_source]
  exact congrArg Prod.fst ridgeSupport518_suffix_decode_000
theorem ridgeTest_large_518 : ridgeTest 518 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport518_eq]
    simp only [ridgeSupport518_suffix_000, ridgeSupport518_suffix_001, ridgeSupport518_suffix_002, ridgeSupport518_suffix_003, ridgeSupport518_suffix_004, ridgeSupport518_suffix_005, ridgeSupport518_suffix_006, ridgeSupport518_suffix_007, ridgeSupport518_suffix_008, ridgeSupport518_suffix_009, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport518_000_mask, ridgeSupport518_001_mask, ridgeSupport518_002_mask, ridgeSupport518_003_mask, ridgeSupport518_004_mask, ridgeSupport518_005_mask, ridgeSupport518_006_mask, ridgeSupport518_007_mask, ridgeSupport518_008_mask]
    decide +kernel
  · rw [ridgeSupport518_eq]
    simp only [ridgeSupport518_suffix_000, ridgeSupport518_suffix_001, ridgeSupport518_suffix_002, ridgeSupport518_suffix_003, ridgeSupport518_suffix_004, ridgeSupport518_suffix_005, ridgeSupport518_suffix_006, ridgeSupport518_suffix_007, ridgeSupport518_suffix_008, ridgeSupport518_suffix_009, List.all_append, List.all_nil, ridgeSupport518_000_checked, ridgeSupport518_001_checked, ridgeSupport518_002_checked, ridgeSupport518_003_checked, ridgeSupport518_004_checked, ridgeSupport518_005_checked, ridgeSupport518_006_checked, ridgeSupport518_007_checked, ridgeSupport518_008_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixExtra00
