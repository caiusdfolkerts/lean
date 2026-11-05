module
prelude
public import RootedSixExtra02GrowthCacheRidgeSupport580Part000
public import RootedSixExtra02GrowthCacheRidgeSupport580Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra02
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport580_suffix_decode_009 : PackedRawNatGrowth.readList 13 0 ridgeSupport580_rest_009 =
    (ridgeSupport580_suffix_009, ridgeSupport580_rest_009) := by rfl
theorem ridgeSupport580_suffix_decode_008 : PackedRawNatGrowth.readList 13 13 ridgeSupport580_rest_008 =
    (ridgeSupport580_suffix_008, ridgeSupport580_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 13 13 0
    ridgeSupport580_rest_008 ridgeSupport580_rest_009 ridgeSupport580_rest_009
    ridgeSupport580_008 ridgeSupport580_suffix_009 ridgeSupport580_008_decode ridgeSupport580_suffix_decode_009
theorem ridgeSupport580_suffix_decode_007 : PackedRawNatGrowth.readList 13 45 ridgeSupport580_rest_007 =
    (ridgeSupport580_suffix_007, ridgeSupport580_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 13
    ridgeSupport580_rest_007 ridgeSupport580_rest_008 ridgeSupport580_rest_009
    ridgeSupport580_007 ridgeSupport580_suffix_008 ridgeSupport580_007_decode ridgeSupport580_suffix_decode_008
theorem ridgeSupport580_suffix_decode_006 : PackedRawNatGrowth.readList 13 77 ridgeSupport580_rest_006 =
    (ridgeSupport580_suffix_006, ridgeSupport580_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 45
    ridgeSupport580_rest_006 ridgeSupport580_rest_007 ridgeSupport580_rest_009
    ridgeSupport580_006 ridgeSupport580_suffix_007 ridgeSupport580_006_decode ridgeSupport580_suffix_decode_007
theorem ridgeSupport580_suffix_decode_005 : PackedRawNatGrowth.readList 13 109 ridgeSupport580_rest_005 =
    (ridgeSupport580_suffix_005, ridgeSupport580_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 77
    ridgeSupport580_rest_005 ridgeSupport580_rest_006 ridgeSupport580_rest_009
    ridgeSupport580_005 ridgeSupport580_suffix_006 ridgeSupport580_005_decode ridgeSupport580_suffix_decode_006
theorem ridgeSupport580_suffix_decode_004 : PackedRawNatGrowth.readList 13 141 ridgeSupport580_rest_004 =
    (ridgeSupport580_suffix_004, ridgeSupport580_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 109
    ridgeSupport580_rest_004 ridgeSupport580_rest_005 ridgeSupport580_rest_009
    ridgeSupport580_004 ridgeSupport580_suffix_005 ridgeSupport580_004_decode ridgeSupport580_suffix_decode_005
theorem ridgeSupport580_suffix_decode_003 : PackedRawNatGrowth.readList 13 173 ridgeSupport580_rest_003 =
    (ridgeSupport580_suffix_003, ridgeSupport580_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 141
    ridgeSupport580_rest_003 ridgeSupport580_rest_004 ridgeSupport580_rest_009
    ridgeSupport580_003 ridgeSupport580_suffix_004 ridgeSupport580_003_decode ridgeSupport580_suffix_decode_004
theorem ridgeSupport580_suffix_decode_002 : PackedRawNatGrowth.readList 13 205 ridgeSupport580_rest_002 =
    (ridgeSupport580_suffix_002, ridgeSupport580_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 173
    ridgeSupport580_rest_002 ridgeSupport580_rest_003 ridgeSupport580_rest_009
    ridgeSupport580_002 ridgeSupport580_suffix_003 ridgeSupport580_002_decode ridgeSupport580_suffix_decode_003
theorem ridgeSupport580_suffix_decode_001 : PackedRawNatGrowth.readList 13 237 ridgeSupport580_rest_001 =
    (ridgeSupport580_suffix_001, ridgeSupport580_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 205
    ridgeSupport580_rest_001 ridgeSupport580_rest_002 ridgeSupport580_rest_009
    ridgeSupport580_001 ridgeSupport580_suffix_002 ridgeSupport580_001_decode ridgeSupport580_suffix_decode_002
theorem ridgeSupport580_suffix_decode_000 : PackedRawNatGrowth.readList 13 269 ridgeSupport580_rest_000 =
    (ridgeSupport580_suffix_000, ridgeSupport580_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 237
    ridgeSupport580_rest_000 ridgeSupport580_rest_001 ridgeSupport580_rest_009
    ridgeSupport580_000 ridgeSupport580_suffix_001 ridgeSupport580_000_decode ridgeSupport580_suffix_decode_001
theorem ridgeSupport580_eq : candidateRows 580 = ridgeSupport580_suffix_000 := by
  change candidateSupports 580 = ridgeSupport580_suffix_000
  rw [ridgeSupport580_source]
  exact congrArg Prod.fst ridgeSupport580_suffix_decode_000
theorem ridgeTest_large_580 : ridgeTest 580 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport580_eq]
    simp only [ridgeSupport580_suffix_000, ridgeSupport580_suffix_001, ridgeSupport580_suffix_002, ridgeSupport580_suffix_003, ridgeSupport580_suffix_004, ridgeSupport580_suffix_005, ridgeSupport580_suffix_006, ridgeSupport580_suffix_007, ridgeSupport580_suffix_008, ridgeSupport580_suffix_009, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport580_000_mask, ridgeSupport580_001_mask, ridgeSupport580_002_mask, ridgeSupport580_003_mask, ridgeSupport580_004_mask, ridgeSupport580_005_mask, ridgeSupport580_006_mask, ridgeSupport580_007_mask, ridgeSupport580_008_mask]
    decide +kernel
  · rw [ridgeSupport580_eq]
    simp only [ridgeSupport580_suffix_000, ridgeSupport580_suffix_001, ridgeSupport580_suffix_002, ridgeSupport580_suffix_003, ridgeSupport580_suffix_004, ridgeSupport580_suffix_005, ridgeSupport580_suffix_006, ridgeSupport580_suffix_007, ridgeSupport580_suffix_008, ridgeSupport580_suffix_009, List.all_append, List.all_nil, ridgeSupport580_000_checked, ridgeSupport580_001_checked, ridgeSupport580_002_checked, ridgeSupport580_003_checked, ridgeSupport580_004_checked, ridgeSupport580_005_checked, ridgeSupport580_006_checked, ridgeSupport580_007_checked, ridgeSupport580_008_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixExtra02
