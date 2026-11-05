module
prelude
public import RootedSixExtra02GrowthCacheRidgeSupport296Part000
public import RootedSixExtra02GrowthCacheRidgeSupport296Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra02
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport296_suffix_decode_009 : PackedRawNatGrowth.readList 13 0 ridgeSupport296_rest_009 =
    (ridgeSupport296_suffix_009, ridgeSupport296_rest_009) := by rfl
theorem ridgeSupport296_suffix_decode_008 : PackedRawNatGrowth.readList 13 25 ridgeSupport296_rest_008 =
    (ridgeSupport296_suffix_008, ridgeSupport296_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 13 25 0
    ridgeSupport296_rest_008 ridgeSupport296_rest_009 ridgeSupport296_rest_009
    ridgeSupport296_008 ridgeSupport296_suffix_009 ridgeSupport296_008_decode ridgeSupport296_suffix_decode_009
theorem ridgeSupport296_suffix_decode_007 : PackedRawNatGrowth.readList 13 57 ridgeSupport296_rest_007 =
    (ridgeSupport296_suffix_007, ridgeSupport296_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 25
    ridgeSupport296_rest_007 ridgeSupport296_rest_008 ridgeSupport296_rest_009
    ridgeSupport296_007 ridgeSupport296_suffix_008 ridgeSupport296_007_decode ridgeSupport296_suffix_decode_008
theorem ridgeSupport296_suffix_decode_006 : PackedRawNatGrowth.readList 13 89 ridgeSupport296_rest_006 =
    (ridgeSupport296_suffix_006, ridgeSupport296_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 57
    ridgeSupport296_rest_006 ridgeSupport296_rest_007 ridgeSupport296_rest_009
    ridgeSupport296_006 ridgeSupport296_suffix_007 ridgeSupport296_006_decode ridgeSupport296_suffix_decode_007
theorem ridgeSupport296_suffix_decode_005 : PackedRawNatGrowth.readList 13 121 ridgeSupport296_rest_005 =
    (ridgeSupport296_suffix_005, ridgeSupport296_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 89
    ridgeSupport296_rest_005 ridgeSupport296_rest_006 ridgeSupport296_rest_009
    ridgeSupport296_005 ridgeSupport296_suffix_006 ridgeSupport296_005_decode ridgeSupport296_suffix_decode_006
theorem ridgeSupport296_suffix_decode_004 : PackedRawNatGrowth.readList 13 153 ridgeSupport296_rest_004 =
    (ridgeSupport296_suffix_004, ridgeSupport296_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 121
    ridgeSupport296_rest_004 ridgeSupport296_rest_005 ridgeSupport296_rest_009
    ridgeSupport296_004 ridgeSupport296_suffix_005 ridgeSupport296_004_decode ridgeSupport296_suffix_decode_005
theorem ridgeSupport296_suffix_decode_003 : PackedRawNatGrowth.readList 13 185 ridgeSupport296_rest_003 =
    (ridgeSupport296_suffix_003, ridgeSupport296_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 153
    ridgeSupport296_rest_003 ridgeSupport296_rest_004 ridgeSupport296_rest_009
    ridgeSupport296_003 ridgeSupport296_suffix_004 ridgeSupport296_003_decode ridgeSupport296_suffix_decode_004
theorem ridgeSupport296_suffix_decode_002 : PackedRawNatGrowth.readList 13 217 ridgeSupport296_rest_002 =
    (ridgeSupport296_suffix_002, ridgeSupport296_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 185
    ridgeSupport296_rest_002 ridgeSupport296_rest_003 ridgeSupport296_rest_009
    ridgeSupport296_002 ridgeSupport296_suffix_003 ridgeSupport296_002_decode ridgeSupport296_suffix_decode_003
theorem ridgeSupport296_suffix_decode_001 : PackedRawNatGrowth.readList 13 249 ridgeSupport296_rest_001 =
    (ridgeSupport296_suffix_001, ridgeSupport296_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 217
    ridgeSupport296_rest_001 ridgeSupport296_rest_002 ridgeSupport296_rest_009
    ridgeSupport296_001 ridgeSupport296_suffix_002 ridgeSupport296_001_decode ridgeSupport296_suffix_decode_002
theorem ridgeSupport296_suffix_decode_000 : PackedRawNatGrowth.readList 13 281 ridgeSupport296_rest_000 =
    (ridgeSupport296_suffix_000, ridgeSupport296_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 249
    ridgeSupport296_rest_000 ridgeSupport296_rest_001 ridgeSupport296_rest_009
    ridgeSupport296_000 ridgeSupport296_suffix_001 ridgeSupport296_000_decode ridgeSupport296_suffix_decode_001
theorem ridgeSupport296_eq : candidateRows 296 = ridgeSupport296_suffix_000 := by
  change candidateSupports 296 = ridgeSupport296_suffix_000
  rw [ridgeSupport296_source]
  exact congrArg Prod.fst ridgeSupport296_suffix_decode_000
theorem ridgeTest_large_296 : ridgeTest 296 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport296_eq]
    simp only [ridgeSupport296_suffix_000, ridgeSupport296_suffix_001, ridgeSupport296_suffix_002, ridgeSupport296_suffix_003, ridgeSupport296_suffix_004, ridgeSupport296_suffix_005, ridgeSupport296_suffix_006, ridgeSupport296_suffix_007, ridgeSupport296_suffix_008, ridgeSupport296_suffix_009, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport296_000_mask, ridgeSupport296_001_mask, ridgeSupport296_002_mask, ridgeSupport296_003_mask, ridgeSupport296_004_mask, ridgeSupport296_005_mask, ridgeSupport296_006_mask, ridgeSupport296_007_mask, ridgeSupport296_008_mask]
    decide +kernel
  · rw [ridgeSupport296_eq]
    simp only [ridgeSupport296_suffix_000, ridgeSupport296_suffix_001, ridgeSupport296_suffix_002, ridgeSupport296_suffix_003, ridgeSupport296_suffix_004, ridgeSupport296_suffix_005, ridgeSupport296_suffix_006, ridgeSupport296_suffix_007, ridgeSupport296_suffix_008, ridgeSupport296_suffix_009, List.all_append, List.all_nil, ridgeSupport296_000_checked, ridgeSupport296_001_checked, ridgeSupport296_002_checked, ridgeSupport296_003_checked, ridgeSupport296_004_checked, ridgeSupport296_005_checked, ridgeSupport296_006_checked, ridgeSupport296_007_checked, ridgeSupport296_008_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixExtra02
