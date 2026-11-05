module
prelude
public import RootedSixExtra02GrowthCacheRidgeSupport592Part000
public import RootedSixExtra02GrowthCacheRidgeSupport592Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra02
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport592_suffix_decode_009 : PackedRawNatGrowth.readList 13 0 ridgeSupport592_rest_009 =
    (ridgeSupport592_suffix_009, ridgeSupport592_rest_009) := by rfl
theorem ridgeSupport592_suffix_decode_008 : PackedRawNatGrowth.readList 13 13 ridgeSupport592_rest_008 =
    (ridgeSupport592_suffix_008, ridgeSupport592_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 13 13 0
    ridgeSupport592_rest_008 ridgeSupport592_rest_009 ridgeSupport592_rest_009
    ridgeSupport592_008 ridgeSupport592_suffix_009 ridgeSupport592_008_decode ridgeSupport592_suffix_decode_009
theorem ridgeSupport592_suffix_decode_007 : PackedRawNatGrowth.readList 13 45 ridgeSupport592_rest_007 =
    (ridgeSupport592_suffix_007, ridgeSupport592_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 13
    ridgeSupport592_rest_007 ridgeSupport592_rest_008 ridgeSupport592_rest_009
    ridgeSupport592_007 ridgeSupport592_suffix_008 ridgeSupport592_007_decode ridgeSupport592_suffix_decode_008
theorem ridgeSupport592_suffix_decode_006 : PackedRawNatGrowth.readList 13 77 ridgeSupport592_rest_006 =
    (ridgeSupport592_suffix_006, ridgeSupport592_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 45
    ridgeSupport592_rest_006 ridgeSupport592_rest_007 ridgeSupport592_rest_009
    ridgeSupport592_006 ridgeSupport592_suffix_007 ridgeSupport592_006_decode ridgeSupport592_suffix_decode_007
theorem ridgeSupport592_suffix_decode_005 : PackedRawNatGrowth.readList 13 109 ridgeSupport592_rest_005 =
    (ridgeSupport592_suffix_005, ridgeSupport592_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 77
    ridgeSupport592_rest_005 ridgeSupport592_rest_006 ridgeSupport592_rest_009
    ridgeSupport592_005 ridgeSupport592_suffix_006 ridgeSupport592_005_decode ridgeSupport592_suffix_decode_006
theorem ridgeSupport592_suffix_decode_004 : PackedRawNatGrowth.readList 13 141 ridgeSupport592_rest_004 =
    (ridgeSupport592_suffix_004, ridgeSupport592_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 109
    ridgeSupport592_rest_004 ridgeSupport592_rest_005 ridgeSupport592_rest_009
    ridgeSupport592_004 ridgeSupport592_suffix_005 ridgeSupport592_004_decode ridgeSupport592_suffix_decode_005
theorem ridgeSupport592_suffix_decode_003 : PackedRawNatGrowth.readList 13 173 ridgeSupport592_rest_003 =
    (ridgeSupport592_suffix_003, ridgeSupport592_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 141
    ridgeSupport592_rest_003 ridgeSupport592_rest_004 ridgeSupport592_rest_009
    ridgeSupport592_003 ridgeSupport592_suffix_004 ridgeSupport592_003_decode ridgeSupport592_suffix_decode_004
theorem ridgeSupport592_suffix_decode_002 : PackedRawNatGrowth.readList 13 205 ridgeSupport592_rest_002 =
    (ridgeSupport592_suffix_002, ridgeSupport592_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 173
    ridgeSupport592_rest_002 ridgeSupport592_rest_003 ridgeSupport592_rest_009
    ridgeSupport592_002 ridgeSupport592_suffix_003 ridgeSupport592_002_decode ridgeSupport592_suffix_decode_003
theorem ridgeSupport592_suffix_decode_001 : PackedRawNatGrowth.readList 13 237 ridgeSupport592_rest_001 =
    (ridgeSupport592_suffix_001, ridgeSupport592_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 205
    ridgeSupport592_rest_001 ridgeSupport592_rest_002 ridgeSupport592_rest_009
    ridgeSupport592_001 ridgeSupport592_suffix_002 ridgeSupport592_001_decode ridgeSupport592_suffix_decode_002
theorem ridgeSupport592_suffix_decode_000 : PackedRawNatGrowth.readList 13 269 ridgeSupport592_rest_000 =
    (ridgeSupport592_suffix_000, ridgeSupport592_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 237
    ridgeSupport592_rest_000 ridgeSupport592_rest_001 ridgeSupport592_rest_009
    ridgeSupport592_000 ridgeSupport592_suffix_001 ridgeSupport592_000_decode ridgeSupport592_suffix_decode_001
theorem ridgeSupport592_eq : candidateRows 592 = ridgeSupport592_suffix_000 := by
  change candidateSupports 592 = ridgeSupport592_suffix_000
  rw [ridgeSupport592_source]
  exact congrArg Prod.fst ridgeSupport592_suffix_decode_000
theorem ridgeTest_large_592 : ridgeTest 592 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport592_eq]
    simp only [ridgeSupport592_suffix_000, ridgeSupport592_suffix_001, ridgeSupport592_suffix_002, ridgeSupport592_suffix_003, ridgeSupport592_suffix_004, ridgeSupport592_suffix_005, ridgeSupport592_suffix_006, ridgeSupport592_suffix_007, ridgeSupport592_suffix_008, ridgeSupport592_suffix_009, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport592_000_mask, ridgeSupport592_001_mask, ridgeSupport592_002_mask, ridgeSupport592_003_mask, ridgeSupport592_004_mask, ridgeSupport592_005_mask, ridgeSupport592_006_mask, ridgeSupport592_007_mask, ridgeSupport592_008_mask]
    decide +kernel
  · rw [ridgeSupport592_eq]
    simp only [ridgeSupport592_suffix_000, ridgeSupport592_suffix_001, ridgeSupport592_suffix_002, ridgeSupport592_suffix_003, ridgeSupport592_suffix_004, ridgeSupport592_suffix_005, ridgeSupport592_suffix_006, ridgeSupport592_suffix_007, ridgeSupport592_suffix_008, ridgeSupport592_suffix_009, List.all_append, List.all_nil, ridgeSupport592_000_checked, ridgeSupport592_001_checked, ridgeSupport592_002_checked, ridgeSupport592_003_checked, ridgeSupport592_004_checked, ridgeSupport592_005_checked, ridgeSupport592_006_checked, ridgeSupport592_007_checked, ridgeSupport592_008_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixExtra02
