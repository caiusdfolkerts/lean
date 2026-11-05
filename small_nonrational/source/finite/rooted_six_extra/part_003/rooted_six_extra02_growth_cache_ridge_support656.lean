module
prelude
public import RootedSixExtra02GrowthCacheRidgeSupport656Part000
public import RootedSixExtra02GrowthCacheRidgeSupport656Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra02
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport656_suffix_decode_009 : PackedRawNatGrowth.readList 13 0 ridgeSupport656_rest_009 =
    (ridgeSupport656_suffix_009, ridgeSupport656_rest_009) := by rfl
theorem ridgeSupport656_suffix_decode_008 : PackedRawNatGrowth.readList 13 13 ridgeSupport656_rest_008 =
    (ridgeSupport656_suffix_008, ridgeSupport656_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 13 13 0
    ridgeSupport656_rest_008 ridgeSupport656_rest_009 ridgeSupport656_rest_009
    ridgeSupport656_008 ridgeSupport656_suffix_009 ridgeSupport656_008_decode ridgeSupport656_suffix_decode_009
theorem ridgeSupport656_suffix_decode_007 : PackedRawNatGrowth.readList 13 45 ridgeSupport656_rest_007 =
    (ridgeSupport656_suffix_007, ridgeSupport656_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 13
    ridgeSupport656_rest_007 ridgeSupport656_rest_008 ridgeSupport656_rest_009
    ridgeSupport656_007 ridgeSupport656_suffix_008 ridgeSupport656_007_decode ridgeSupport656_suffix_decode_008
theorem ridgeSupport656_suffix_decode_006 : PackedRawNatGrowth.readList 13 77 ridgeSupport656_rest_006 =
    (ridgeSupport656_suffix_006, ridgeSupport656_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 45
    ridgeSupport656_rest_006 ridgeSupport656_rest_007 ridgeSupport656_rest_009
    ridgeSupport656_006 ridgeSupport656_suffix_007 ridgeSupport656_006_decode ridgeSupport656_suffix_decode_007
theorem ridgeSupport656_suffix_decode_005 : PackedRawNatGrowth.readList 13 109 ridgeSupport656_rest_005 =
    (ridgeSupport656_suffix_005, ridgeSupport656_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 77
    ridgeSupport656_rest_005 ridgeSupport656_rest_006 ridgeSupport656_rest_009
    ridgeSupport656_005 ridgeSupport656_suffix_006 ridgeSupport656_005_decode ridgeSupport656_suffix_decode_006
theorem ridgeSupport656_suffix_decode_004 : PackedRawNatGrowth.readList 13 141 ridgeSupport656_rest_004 =
    (ridgeSupport656_suffix_004, ridgeSupport656_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 109
    ridgeSupport656_rest_004 ridgeSupport656_rest_005 ridgeSupport656_rest_009
    ridgeSupport656_004 ridgeSupport656_suffix_005 ridgeSupport656_004_decode ridgeSupport656_suffix_decode_005
theorem ridgeSupport656_suffix_decode_003 : PackedRawNatGrowth.readList 13 173 ridgeSupport656_rest_003 =
    (ridgeSupport656_suffix_003, ridgeSupport656_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 141
    ridgeSupport656_rest_003 ridgeSupport656_rest_004 ridgeSupport656_rest_009
    ridgeSupport656_003 ridgeSupport656_suffix_004 ridgeSupport656_003_decode ridgeSupport656_suffix_decode_004
theorem ridgeSupport656_suffix_decode_002 : PackedRawNatGrowth.readList 13 205 ridgeSupport656_rest_002 =
    (ridgeSupport656_suffix_002, ridgeSupport656_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 173
    ridgeSupport656_rest_002 ridgeSupport656_rest_003 ridgeSupport656_rest_009
    ridgeSupport656_002 ridgeSupport656_suffix_003 ridgeSupport656_002_decode ridgeSupport656_suffix_decode_003
theorem ridgeSupport656_suffix_decode_001 : PackedRawNatGrowth.readList 13 237 ridgeSupport656_rest_001 =
    (ridgeSupport656_suffix_001, ridgeSupport656_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 205
    ridgeSupport656_rest_001 ridgeSupport656_rest_002 ridgeSupport656_rest_009
    ridgeSupport656_001 ridgeSupport656_suffix_002 ridgeSupport656_001_decode ridgeSupport656_suffix_decode_002
theorem ridgeSupport656_suffix_decode_000 : PackedRawNatGrowth.readList 13 269 ridgeSupport656_rest_000 =
    (ridgeSupport656_suffix_000, ridgeSupport656_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 237
    ridgeSupport656_rest_000 ridgeSupport656_rest_001 ridgeSupport656_rest_009
    ridgeSupport656_000 ridgeSupport656_suffix_001 ridgeSupport656_000_decode ridgeSupport656_suffix_decode_001
theorem ridgeSupport656_eq : candidateRows 656 = ridgeSupport656_suffix_000 := by
  change candidateSupports 656 = ridgeSupport656_suffix_000
  rw [ridgeSupport656_source]
  exact congrArg Prod.fst ridgeSupport656_suffix_decode_000
theorem ridgeTest_large_656 : ridgeTest 656 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport656_eq]
    simp only [ridgeSupport656_suffix_000, ridgeSupport656_suffix_001, ridgeSupport656_suffix_002, ridgeSupport656_suffix_003, ridgeSupport656_suffix_004, ridgeSupport656_suffix_005, ridgeSupport656_suffix_006, ridgeSupport656_suffix_007, ridgeSupport656_suffix_008, ridgeSupport656_suffix_009, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport656_000_mask, ridgeSupport656_001_mask, ridgeSupport656_002_mask, ridgeSupport656_003_mask, ridgeSupport656_004_mask, ridgeSupport656_005_mask, ridgeSupport656_006_mask, ridgeSupport656_007_mask, ridgeSupport656_008_mask]
    decide +kernel
  · rw [ridgeSupport656_eq]
    simp only [ridgeSupport656_suffix_000, ridgeSupport656_suffix_001, ridgeSupport656_suffix_002, ridgeSupport656_suffix_003, ridgeSupport656_suffix_004, ridgeSupport656_suffix_005, ridgeSupport656_suffix_006, ridgeSupport656_suffix_007, ridgeSupport656_suffix_008, ridgeSupport656_suffix_009, List.all_append, List.all_nil, ridgeSupport656_000_checked, ridgeSupport656_001_checked, ridgeSupport656_002_checked, ridgeSupport656_003_checked, ridgeSupport656_004_checked, ridgeSupport656_005_checked, ridgeSupport656_006_checked, ridgeSupport656_007_checked, ridgeSupport656_008_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixExtra02
