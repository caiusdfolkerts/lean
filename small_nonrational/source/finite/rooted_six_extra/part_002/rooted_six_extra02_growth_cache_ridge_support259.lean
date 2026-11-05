module
prelude
public import RootedSixExtra02GrowthCacheRidgeSupport259Part000
public import RootedSixExtra02GrowthCacheRidgeSupport259Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra02
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport259_suffix_decode_009 : PackedRawNatGrowth.readList 13 0 ridgeSupport259_rest_009 =
    (ridgeSupport259_suffix_009, ridgeSupport259_rest_009) := by rfl
theorem ridgeSupport259_suffix_decode_008 : PackedRawNatGrowth.readList 13 25 ridgeSupport259_rest_008 =
    (ridgeSupport259_suffix_008, ridgeSupport259_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 13 25 0
    ridgeSupport259_rest_008 ridgeSupport259_rest_009 ridgeSupport259_rest_009
    ridgeSupport259_008 ridgeSupport259_suffix_009 ridgeSupport259_008_decode ridgeSupport259_suffix_decode_009
theorem ridgeSupport259_suffix_decode_007 : PackedRawNatGrowth.readList 13 57 ridgeSupport259_rest_007 =
    (ridgeSupport259_suffix_007, ridgeSupport259_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 25
    ridgeSupport259_rest_007 ridgeSupport259_rest_008 ridgeSupport259_rest_009
    ridgeSupport259_007 ridgeSupport259_suffix_008 ridgeSupport259_007_decode ridgeSupport259_suffix_decode_008
theorem ridgeSupport259_suffix_decode_006 : PackedRawNatGrowth.readList 13 89 ridgeSupport259_rest_006 =
    (ridgeSupport259_suffix_006, ridgeSupport259_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 57
    ridgeSupport259_rest_006 ridgeSupport259_rest_007 ridgeSupport259_rest_009
    ridgeSupport259_006 ridgeSupport259_suffix_007 ridgeSupport259_006_decode ridgeSupport259_suffix_decode_007
theorem ridgeSupport259_suffix_decode_005 : PackedRawNatGrowth.readList 13 121 ridgeSupport259_rest_005 =
    (ridgeSupport259_suffix_005, ridgeSupport259_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 89
    ridgeSupport259_rest_005 ridgeSupport259_rest_006 ridgeSupport259_rest_009
    ridgeSupport259_005 ridgeSupport259_suffix_006 ridgeSupport259_005_decode ridgeSupport259_suffix_decode_006
theorem ridgeSupport259_suffix_decode_004 : PackedRawNatGrowth.readList 13 153 ridgeSupport259_rest_004 =
    (ridgeSupport259_suffix_004, ridgeSupport259_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 121
    ridgeSupport259_rest_004 ridgeSupport259_rest_005 ridgeSupport259_rest_009
    ridgeSupport259_004 ridgeSupport259_suffix_005 ridgeSupport259_004_decode ridgeSupport259_suffix_decode_005
theorem ridgeSupport259_suffix_decode_003 : PackedRawNatGrowth.readList 13 185 ridgeSupport259_rest_003 =
    (ridgeSupport259_suffix_003, ridgeSupport259_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 153
    ridgeSupport259_rest_003 ridgeSupport259_rest_004 ridgeSupport259_rest_009
    ridgeSupport259_003 ridgeSupport259_suffix_004 ridgeSupport259_003_decode ridgeSupport259_suffix_decode_004
theorem ridgeSupport259_suffix_decode_002 : PackedRawNatGrowth.readList 13 217 ridgeSupport259_rest_002 =
    (ridgeSupport259_suffix_002, ridgeSupport259_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 185
    ridgeSupport259_rest_002 ridgeSupport259_rest_003 ridgeSupport259_rest_009
    ridgeSupport259_002 ridgeSupport259_suffix_003 ridgeSupport259_002_decode ridgeSupport259_suffix_decode_003
theorem ridgeSupport259_suffix_decode_001 : PackedRawNatGrowth.readList 13 249 ridgeSupport259_rest_001 =
    (ridgeSupport259_suffix_001, ridgeSupport259_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 217
    ridgeSupport259_rest_001 ridgeSupport259_rest_002 ridgeSupport259_rest_009
    ridgeSupport259_001 ridgeSupport259_suffix_002 ridgeSupport259_001_decode ridgeSupport259_suffix_decode_002
theorem ridgeSupport259_suffix_decode_000 : PackedRawNatGrowth.readList 13 281 ridgeSupport259_rest_000 =
    (ridgeSupport259_suffix_000, ridgeSupport259_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 249
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

end Papers.RationalityTen.RootedCaches.RootedSixExtra02
