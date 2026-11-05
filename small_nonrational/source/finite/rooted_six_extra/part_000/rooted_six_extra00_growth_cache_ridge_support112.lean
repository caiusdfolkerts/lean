module
prelude
public import RootedSixExtra00GrowthCacheRidgeSupport112Part000
public import RootedSixExtra00GrowthCacheRidgeSupport112Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra00
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport112_suffix_decode_009 : PackedRawNatGrowth.readList 14 0 ridgeSupport112_rest_009 =
    (ridgeSupport112_suffix_009, ridgeSupport112_rest_009) := by rfl
theorem ridgeSupport112_suffix_decode_008 : PackedRawNatGrowth.readList 14 7 ridgeSupport112_rest_008 =
    (ridgeSupport112_suffix_008, ridgeSupport112_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 7 0
    ridgeSupport112_rest_008 ridgeSupport112_rest_009 ridgeSupport112_rest_009
    ridgeSupport112_008 ridgeSupport112_suffix_009 ridgeSupport112_008_decode ridgeSupport112_suffix_decode_009
theorem ridgeSupport112_suffix_decode_007 : PackedRawNatGrowth.readList 14 39 ridgeSupport112_rest_007 =
    (ridgeSupport112_suffix_007, ridgeSupport112_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 7
    ridgeSupport112_rest_007 ridgeSupport112_rest_008 ridgeSupport112_rest_009
    ridgeSupport112_007 ridgeSupport112_suffix_008 ridgeSupport112_007_decode ridgeSupport112_suffix_decode_008
theorem ridgeSupport112_suffix_decode_006 : PackedRawNatGrowth.readList 14 71 ridgeSupport112_rest_006 =
    (ridgeSupport112_suffix_006, ridgeSupport112_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 39
    ridgeSupport112_rest_006 ridgeSupport112_rest_007 ridgeSupport112_rest_009
    ridgeSupport112_006 ridgeSupport112_suffix_007 ridgeSupport112_006_decode ridgeSupport112_suffix_decode_007
theorem ridgeSupport112_suffix_decode_005 : PackedRawNatGrowth.readList 14 103 ridgeSupport112_rest_005 =
    (ridgeSupport112_suffix_005, ridgeSupport112_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 71
    ridgeSupport112_rest_005 ridgeSupport112_rest_006 ridgeSupport112_rest_009
    ridgeSupport112_005 ridgeSupport112_suffix_006 ridgeSupport112_005_decode ridgeSupport112_suffix_decode_006
theorem ridgeSupport112_suffix_decode_004 : PackedRawNatGrowth.readList 14 135 ridgeSupport112_rest_004 =
    (ridgeSupport112_suffix_004, ridgeSupport112_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 103
    ridgeSupport112_rest_004 ridgeSupport112_rest_005 ridgeSupport112_rest_009
    ridgeSupport112_004 ridgeSupport112_suffix_005 ridgeSupport112_004_decode ridgeSupport112_suffix_decode_005
theorem ridgeSupport112_suffix_decode_003 : PackedRawNatGrowth.readList 14 167 ridgeSupport112_rest_003 =
    (ridgeSupport112_suffix_003, ridgeSupport112_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 135
    ridgeSupport112_rest_003 ridgeSupport112_rest_004 ridgeSupport112_rest_009
    ridgeSupport112_003 ridgeSupport112_suffix_004 ridgeSupport112_003_decode ridgeSupport112_suffix_decode_004
theorem ridgeSupport112_suffix_decode_002 : PackedRawNatGrowth.readList 14 199 ridgeSupport112_rest_002 =
    (ridgeSupport112_suffix_002, ridgeSupport112_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 167
    ridgeSupport112_rest_002 ridgeSupport112_rest_003 ridgeSupport112_rest_009
    ridgeSupport112_002 ridgeSupport112_suffix_003 ridgeSupport112_002_decode ridgeSupport112_suffix_decode_003
theorem ridgeSupport112_suffix_decode_001 : PackedRawNatGrowth.readList 14 231 ridgeSupport112_rest_001 =
    (ridgeSupport112_suffix_001, ridgeSupport112_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 199
    ridgeSupport112_rest_001 ridgeSupport112_rest_002 ridgeSupport112_rest_009
    ridgeSupport112_001 ridgeSupport112_suffix_002 ridgeSupport112_001_decode ridgeSupport112_suffix_decode_002
theorem ridgeSupport112_suffix_decode_000 : PackedRawNatGrowth.readList 14 263 ridgeSupport112_rest_000 =
    (ridgeSupport112_suffix_000, ridgeSupport112_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 231
    ridgeSupport112_rest_000 ridgeSupport112_rest_001 ridgeSupport112_rest_009
    ridgeSupport112_000 ridgeSupport112_suffix_001 ridgeSupport112_000_decode ridgeSupport112_suffix_decode_001
theorem ridgeSupport112_eq : candidateRows 112 = ridgeSupport112_suffix_000 := by
  change candidateSupports 112 = ridgeSupport112_suffix_000
  rw [ridgeSupport112_source]
  exact congrArg Prod.fst ridgeSupport112_suffix_decode_000
theorem ridgeTest_large_112 : ridgeTest 112 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport112_eq]
    simp only [ridgeSupport112_suffix_000, ridgeSupport112_suffix_001, ridgeSupport112_suffix_002, ridgeSupport112_suffix_003, ridgeSupport112_suffix_004, ridgeSupport112_suffix_005, ridgeSupport112_suffix_006, ridgeSupport112_suffix_007, ridgeSupport112_suffix_008, ridgeSupport112_suffix_009, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport112_000_mask, ridgeSupport112_001_mask, ridgeSupport112_002_mask, ridgeSupport112_003_mask, ridgeSupport112_004_mask, ridgeSupport112_005_mask, ridgeSupport112_006_mask, ridgeSupport112_007_mask, ridgeSupport112_008_mask]
    decide +kernel
  · rw [ridgeSupport112_eq]
    simp only [ridgeSupport112_suffix_000, ridgeSupport112_suffix_001, ridgeSupport112_suffix_002, ridgeSupport112_suffix_003, ridgeSupport112_suffix_004, ridgeSupport112_suffix_005, ridgeSupport112_suffix_006, ridgeSupport112_suffix_007, ridgeSupport112_suffix_008, ridgeSupport112_suffix_009, List.all_append, List.all_nil, ridgeSupport112_000_checked, ridgeSupport112_001_checked, ridgeSupport112_002_checked, ridgeSupport112_003_checked, ridgeSupport112_004_checked, ridgeSupport112_005_checked, ridgeSupport112_006_checked, ridgeSupport112_007_checked, ridgeSupport112_008_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixExtra00
