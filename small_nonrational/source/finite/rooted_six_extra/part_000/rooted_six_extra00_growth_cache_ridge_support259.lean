module
prelude
public import RootedSixExtra00GrowthCacheRidgeSupport259Part000
public import RootedSixExtra00GrowthCacheRidgeSupport259Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra00
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport259_suffix_decode_009 : PackedRawNatGrowth.readList 14 0 ridgeSupport259_rest_009 =
    (ridgeSupport259_suffix_009, ridgeSupport259_rest_009) := by rfl
theorem ridgeSupport259_suffix_decode_008 : PackedRawNatGrowth.readList 14 7 ridgeSupport259_rest_008 =
    (ridgeSupport259_suffix_008, ridgeSupport259_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 7 0
    ridgeSupport259_rest_008 ridgeSupport259_rest_009 ridgeSupport259_rest_009
    ridgeSupport259_008 ridgeSupport259_suffix_009 ridgeSupport259_008_decode ridgeSupport259_suffix_decode_009
theorem ridgeSupport259_suffix_decode_007 : PackedRawNatGrowth.readList 14 39 ridgeSupport259_rest_007 =
    (ridgeSupport259_suffix_007, ridgeSupport259_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 7
    ridgeSupport259_rest_007 ridgeSupport259_rest_008 ridgeSupport259_rest_009
    ridgeSupport259_007 ridgeSupport259_suffix_008 ridgeSupport259_007_decode ridgeSupport259_suffix_decode_008
theorem ridgeSupport259_suffix_decode_006 : PackedRawNatGrowth.readList 14 71 ridgeSupport259_rest_006 =
    (ridgeSupport259_suffix_006, ridgeSupport259_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 39
    ridgeSupport259_rest_006 ridgeSupport259_rest_007 ridgeSupport259_rest_009
    ridgeSupport259_006 ridgeSupport259_suffix_007 ridgeSupport259_006_decode ridgeSupport259_suffix_decode_007
theorem ridgeSupport259_suffix_decode_005 : PackedRawNatGrowth.readList 14 103 ridgeSupport259_rest_005 =
    (ridgeSupport259_suffix_005, ridgeSupport259_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 71
    ridgeSupport259_rest_005 ridgeSupport259_rest_006 ridgeSupport259_rest_009
    ridgeSupport259_005 ridgeSupport259_suffix_006 ridgeSupport259_005_decode ridgeSupport259_suffix_decode_006
theorem ridgeSupport259_suffix_decode_004 : PackedRawNatGrowth.readList 14 135 ridgeSupport259_rest_004 =
    (ridgeSupport259_suffix_004, ridgeSupport259_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 103
    ridgeSupport259_rest_004 ridgeSupport259_rest_005 ridgeSupport259_rest_009
    ridgeSupport259_004 ridgeSupport259_suffix_005 ridgeSupport259_004_decode ridgeSupport259_suffix_decode_005
theorem ridgeSupport259_suffix_decode_003 : PackedRawNatGrowth.readList 14 167 ridgeSupport259_rest_003 =
    (ridgeSupport259_suffix_003, ridgeSupport259_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 135
    ridgeSupport259_rest_003 ridgeSupport259_rest_004 ridgeSupport259_rest_009
    ridgeSupport259_003 ridgeSupport259_suffix_004 ridgeSupport259_003_decode ridgeSupport259_suffix_decode_004
theorem ridgeSupport259_suffix_decode_002 : PackedRawNatGrowth.readList 14 199 ridgeSupport259_rest_002 =
    (ridgeSupport259_suffix_002, ridgeSupport259_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 167
    ridgeSupport259_rest_002 ridgeSupport259_rest_003 ridgeSupport259_rest_009
    ridgeSupport259_002 ridgeSupport259_suffix_003 ridgeSupport259_002_decode ridgeSupport259_suffix_decode_003
theorem ridgeSupport259_suffix_decode_001 : PackedRawNatGrowth.readList 14 231 ridgeSupport259_rest_001 =
    (ridgeSupport259_suffix_001, ridgeSupport259_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 199
    ridgeSupport259_rest_001 ridgeSupport259_rest_002 ridgeSupport259_rest_009
    ridgeSupport259_001 ridgeSupport259_suffix_002 ridgeSupport259_001_decode ridgeSupport259_suffix_decode_002
theorem ridgeSupport259_suffix_decode_000 : PackedRawNatGrowth.readList 14 263 ridgeSupport259_rest_000 =
    (ridgeSupport259_suffix_000, ridgeSupport259_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 231
    ridgeSupport259_rest_000 ridgeSupport259_rest_001 ridgeSupport259_rest_009
    ridgeSupport259_000 ridgeSupport259_suffix_001 ridgeSupport259_000_decode ridgeSupport259_suffix_decode_001
theorem ridgeSupport259_eq : candidateRows 259 = ridgeSupport259_suffix_000 := by
  change candidateSupports 259 = ridgeSupport259_suffix_000
  rw [ridgeSupport259_source]
  exact congrArg Prod.fst ridgeSupport259_suffix_decode_000
theorem ridgeTest_large_259 : ridgeTest 259 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport259_eq]
    simp only [ridgeSupport259_suffix_000, ridgeSupport259_suffix_001, ridgeSupport259_suffix_002, ridgeSupport259_suffix_003, ridgeSupport259_suffix_004, ridgeSupport259_suffix_005, ridgeSupport259_suffix_006, ridgeSupport259_suffix_007, ridgeSupport259_suffix_008, ridgeSupport259_suffix_009, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport259_000_mask, ridgeSupport259_001_mask, ridgeSupport259_002_mask, ridgeSupport259_003_mask, ridgeSupport259_004_mask, ridgeSupport259_005_mask, ridgeSupport259_006_mask, ridgeSupport259_007_mask, ridgeSupport259_008_mask]
    decide +kernel
  · rw [ridgeSupport259_eq]
    simp only [ridgeSupport259_suffix_000, ridgeSupport259_suffix_001, ridgeSupport259_suffix_002, ridgeSupport259_suffix_003, ridgeSupport259_suffix_004, ridgeSupport259_suffix_005, ridgeSupport259_suffix_006, ridgeSupport259_suffix_007, ridgeSupport259_suffix_008, ridgeSupport259_suffix_009, List.all_append, List.all_nil, ridgeSupport259_000_checked, ridgeSupport259_001_checked, ridgeSupport259_002_checked, ridgeSupport259_003_checked, ridgeSupport259_004_checked, ridgeSupport259_005_checked, ridgeSupport259_006_checked, ridgeSupport259_007_checked, ridgeSupport259_008_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixExtra00
