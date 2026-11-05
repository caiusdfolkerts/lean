module
prelude
public import RootedSixExtra02GrowthCacheRidgeSupport772Part000
public import RootedSixExtra02GrowthCacheRidgeSupport772Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra02
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport772_suffix_decode_009 : PackedRawNatGrowth.readList 13 0 ridgeSupport772_rest_009 =
    (ridgeSupport772_suffix_009, ridgeSupport772_rest_009) := by rfl
theorem ridgeSupport772_suffix_decode_008 : PackedRawNatGrowth.readList 13 13 ridgeSupport772_rest_008 =
    (ridgeSupport772_suffix_008, ridgeSupport772_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 13 13 0
    ridgeSupport772_rest_008 ridgeSupport772_rest_009 ridgeSupport772_rest_009
    ridgeSupport772_008 ridgeSupport772_suffix_009 ridgeSupport772_008_decode ridgeSupport772_suffix_decode_009
theorem ridgeSupport772_suffix_decode_007 : PackedRawNatGrowth.readList 13 45 ridgeSupport772_rest_007 =
    (ridgeSupport772_suffix_007, ridgeSupport772_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 13
    ridgeSupport772_rest_007 ridgeSupport772_rest_008 ridgeSupport772_rest_009
    ridgeSupport772_007 ridgeSupport772_suffix_008 ridgeSupport772_007_decode ridgeSupport772_suffix_decode_008
theorem ridgeSupport772_suffix_decode_006 : PackedRawNatGrowth.readList 13 77 ridgeSupport772_rest_006 =
    (ridgeSupport772_suffix_006, ridgeSupport772_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 45
    ridgeSupport772_rest_006 ridgeSupport772_rest_007 ridgeSupport772_rest_009
    ridgeSupport772_006 ridgeSupport772_suffix_007 ridgeSupport772_006_decode ridgeSupport772_suffix_decode_007
theorem ridgeSupport772_suffix_decode_005 : PackedRawNatGrowth.readList 13 109 ridgeSupport772_rest_005 =
    (ridgeSupport772_suffix_005, ridgeSupport772_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 77
    ridgeSupport772_rest_005 ridgeSupport772_rest_006 ridgeSupport772_rest_009
    ridgeSupport772_005 ridgeSupport772_suffix_006 ridgeSupport772_005_decode ridgeSupport772_suffix_decode_006
theorem ridgeSupport772_suffix_decode_004 : PackedRawNatGrowth.readList 13 141 ridgeSupport772_rest_004 =
    (ridgeSupport772_suffix_004, ridgeSupport772_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 109
    ridgeSupport772_rest_004 ridgeSupport772_rest_005 ridgeSupport772_rest_009
    ridgeSupport772_004 ridgeSupport772_suffix_005 ridgeSupport772_004_decode ridgeSupport772_suffix_decode_005
theorem ridgeSupport772_suffix_decode_003 : PackedRawNatGrowth.readList 13 173 ridgeSupport772_rest_003 =
    (ridgeSupport772_suffix_003, ridgeSupport772_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 141
    ridgeSupport772_rest_003 ridgeSupport772_rest_004 ridgeSupport772_rest_009
    ridgeSupport772_003 ridgeSupport772_suffix_004 ridgeSupport772_003_decode ridgeSupport772_suffix_decode_004
theorem ridgeSupport772_suffix_decode_002 : PackedRawNatGrowth.readList 13 205 ridgeSupport772_rest_002 =
    (ridgeSupport772_suffix_002, ridgeSupport772_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 173
    ridgeSupport772_rest_002 ridgeSupport772_rest_003 ridgeSupport772_rest_009
    ridgeSupport772_002 ridgeSupport772_suffix_003 ridgeSupport772_002_decode ridgeSupport772_suffix_decode_003
theorem ridgeSupport772_suffix_decode_001 : PackedRawNatGrowth.readList 13 237 ridgeSupport772_rest_001 =
    (ridgeSupport772_suffix_001, ridgeSupport772_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 205
    ridgeSupport772_rest_001 ridgeSupport772_rest_002 ridgeSupport772_rest_009
    ridgeSupport772_001 ridgeSupport772_suffix_002 ridgeSupport772_001_decode ridgeSupport772_suffix_decode_002
theorem ridgeSupport772_suffix_decode_000 : PackedRawNatGrowth.readList 13 269 ridgeSupport772_rest_000 =
    (ridgeSupport772_suffix_000, ridgeSupport772_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 237
    ridgeSupport772_rest_000 ridgeSupport772_rest_001 ridgeSupport772_rest_009
    ridgeSupport772_000 ridgeSupport772_suffix_001 ridgeSupport772_000_decode ridgeSupport772_suffix_decode_001
theorem ridgeSupport772_eq : candidateRows 772 = ridgeSupport772_suffix_000 := by
  change candidateSupports 772 = ridgeSupport772_suffix_000
  rw [ridgeSupport772_source]
  exact congrArg Prod.fst ridgeSupport772_suffix_decode_000
theorem ridgeTest_large_772 : ridgeTest 772 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport772_eq]
    simp only [ridgeSupport772_suffix_000, ridgeSupport772_suffix_001, ridgeSupport772_suffix_002, ridgeSupport772_suffix_003, ridgeSupport772_suffix_004, ridgeSupport772_suffix_005, ridgeSupport772_suffix_006, ridgeSupport772_suffix_007, ridgeSupport772_suffix_008, ridgeSupport772_suffix_009, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport772_000_mask, ridgeSupport772_001_mask, ridgeSupport772_002_mask, ridgeSupport772_003_mask, ridgeSupport772_004_mask, ridgeSupport772_005_mask, ridgeSupport772_006_mask, ridgeSupport772_007_mask, ridgeSupport772_008_mask]
    decide +kernel
  · rw [ridgeSupport772_eq]
    simp only [ridgeSupport772_suffix_000, ridgeSupport772_suffix_001, ridgeSupport772_suffix_002, ridgeSupport772_suffix_003, ridgeSupport772_suffix_004, ridgeSupport772_suffix_005, ridgeSupport772_suffix_006, ridgeSupport772_suffix_007, ridgeSupport772_suffix_008, ridgeSupport772_suffix_009, List.all_append, List.all_nil, ridgeSupport772_000_checked, ridgeSupport772_001_checked, ridgeSupport772_002_checked, ridgeSupport772_003_checked, ridgeSupport772_004_checked, ridgeSupport772_005_checked, ridgeSupport772_006_checked, ridgeSupport772_007_checked, ridgeSupport772_008_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixExtra02
