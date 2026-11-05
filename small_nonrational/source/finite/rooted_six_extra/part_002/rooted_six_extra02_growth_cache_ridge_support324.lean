module
prelude
public import RootedSixExtra02GrowthCacheRidgeSupport324Part000
public import RootedSixExtra02GrowthCacheRidgeSupport324Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra02
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport324_suffix_decode_009 : PackedRawNatGrowth.readList 13 0 ridgeSupport324_rest_009 =
    (ridgeSupport324_suffix_009, ridgeSupport324_rest_009) := by rfl
theorem ridgeSupport324_suffix_decode_008 : PackedRawNatGrowth.readList 13 13 ridgeSupport324_rest_008 =
    (ridgeSupport324_suffix_008, ridgeSupport324_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 13 13 0
    ridgeSupport324_rest_008 ridgeSupport324_rest_009 ridgeSupport324_rest_009
    ridgeSupport324_008 ridgeSupport324_suffix_009 ridgeSupport324_008_decode ridgeSupport324_suffix_decode_009
theorem ridgeSupport324_suffix_decode_007 : PackedRawNatGrowth.readList 13 45 ridgeSupport324_rest_007 =
    (ridgeSupport324_suffix_007, ridgeSupport324_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 13
    ridgeSupport324_rest_007 ridgeSupport324_rest_008 ridgeSupport324_rest_009
    ridgeSupport324_007 ridgeSupport324_suffix_008 ridgeSupport324_007_decode ridgeSupport324_suffix_decode_008
theorem ridgeSupport324_suffix_decode_006 : PackedRawNatGrowth.readList 13 77 ridgeSupport324_rest_006 =
    (ridgeSupport324_suffix_006, ridgeSupport324_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 45
    ridgeSupport324_rest_006 ridgeSupport324_rest_007 ridgeSupport324_rest_009
    ridgeSupport324_006 ridgeSupport324_suffix_007 ridgeSupport324_006_decode ridgeSupport324_suffix_decode_007
theorem ridgeSupport324_suffix_decode_005 : PackedRawNatGrowth.readList 13 109 ridgeSupport324_rest_005 =
    (ridgeSupport324_suffix_005, ridgeSupport324_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 77
    ridgeSupport324_rest_005 ridgeSupport324_rest_006 ridgeSupport324_rest_009
    ridgeSupport324_005 ridgeSupport324_suffix_006 ridgeSupport324_005_decode ridgeSupport324_suffix_decode_006
theorem ridgeSupport324_suffix_decode_004 : PackedRawNatGrowth.readList 13 141 ridgeSupport324_rest_004 =
    (ridgeSupport324_suffix_004, ridgeSupport324_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 109
    ridgeSupport324_rest_004 ridgeSupport324_rest_005 ridgeSupport324_rest_009
    ridgeSupport324_004 ridgeSupport324_suffix_005 ridgeSupport324_004_decode ridgeSupport324_suffix_decode_005
theorem ridgeSupport324_suffix_decode_003 : PackedRawNatGrowth.readList 13 173 ridgeSupport324_rest_003 =
    (ridgeSupport324_suffix_003, ridgeSupport324_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 141
    ridgeSupport324_rest_003 ridgeSupport324_rest_004 ridgeSupport324_rest_009
    ridgeSupport324_003 ridgeSupport324_suffix_004 ridgeSupport324_003_decode ridgeSupport324_suffix_decode_004
theorem ridgeSupport324_suffix_decode_002 : PackedRawNatGrowth.readList 13 205 ridgeSupport324_rest_002 =
    (ridgeSupport324_suffix_002, ridgeSupport324_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 173
    ridgeSupport324_rest_002 ridgeSupport324_rest_003 ridgeSupport324_rest_009
    ridgeSupport324_002 ridgeSupport324_suffix_003 ridgeSupport324_002_decode ridgeSupport324_suffix_decode_003
theorem ridgeSupport324_suffix_decode_001 : PackedRawNatGrowth.readList 13 237 ridgeSupport324_rest_001 =
    (ridgeSupport324_suffix_001, ridgeSupport324_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 205
    ridgeSupport324_rest_001 ridgeSupport324_rest_002 ridgeSupport324_rest_009
    ridgeSupport324_001 ridgeSupport324_suffix_002 ridgeSupport324_001_decode ridgeSupport324_suffix_decode_002
theorem ridgeSupport324_suffix_decode_000 : PackedRawNatGrowth.readList 13 269 ridgeSupport324_rest_000 =
    (ridgeSupport324_suffix_000, ridgeSupport324_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 237
    ridgeSupport324_rest_000 ridgeSupport324_rest_001 ridgeSupport324_rest_009
    ridgeSupport324_000 ridgeSupport324_suffix_001 ridgeSupport324_000_decode ridgeSupport324_suffix_decode_001
theorem ridgeSupport324_eq : candidateRows 324 = ridgeSupport324_suffix_000 := by
  change candidateSupports 324 = ridgeSupport324_suffix_000
  rw [ridgeSupport324_source]
  exact congrArg Prod.fst ridgeSupport324_suffix_decode_000
theorem ridgeTest_large_324 : ridgeTest 324 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport324_eq]
    simp only [ridgeSupport324_suffix_000, ridgeSupport324_suffix_001, ridgeSupport324_suffix_002, ridgeSupport324_suffix_003, ridgeSupport324_suffix_004, ridgeSupport324_suffix_005, ridgeSupport324_suffix_006, ridgeSupport324_suffix_007, ridgeSupport324_suffix_008, ridgeSupport324_suffix_009, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport324_000_mask, ridgeSupport324_001_mask, ridgeSupport324_002_mask, ridgeSupport324_003_mask, ridgeSupport324_004_mask, ridgeSupport324_005_mask, ridgeSupport324_006_mask, ridgeSupport324_007_mask, ridgeSupport324_008_mask]
    decide +kernel
  · rw [ridgeSupport324_eq]
    simp only [ridgeSupport324_suffix_000, ridgeSupport324_suffix_001, ridgeSupport324_suffix_002, ridgeSupport324_suffix_003, ridgeSupport324_suffix_004, ridgeSupport324_suffix_005, ridgeSupport324_suffix_006, ridgeSupport324_suffix_007, ridgeSupport324_suffix_008, ridgeSupport324_suffix_009, List.all_append, List.all_nil, ridgeSupport324_000_checked, ridgeSupport324_001_checked, ridgeSupport324_002_checked, ridgeSupport324_003_checked, ridgeSupport324_004_checked, ridgeSupport324_005_checked, ridgeSupport324_006_checked, ridgeSupport324_007_checked, ridgeSupport324_008_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixExtra02
