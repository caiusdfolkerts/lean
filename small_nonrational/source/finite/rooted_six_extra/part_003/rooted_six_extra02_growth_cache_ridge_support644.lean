module
prelude
public import RootedSixExtra02GrowthCacheRidgeSupport644Part000
public import RootedSixExtra02GrowthCacheRidgeSupport644Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra02
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport644_suffix_decode_009 : PackedRawNatGrowth.readList 13 0 ridgeSupport644_rest_009 =
    (ridgeSupport644_suffix_009, ridgeSupport644_rest_009) := by rfl
theorem ridgeSupport644_suffix_decode_008 : PackedRawNatGrowth.readList 13 13 ridgeSupport644_rest_008 =
    (ridgeSupport644_suffix_008, ridgeSupport644_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 13 13 0
    ridgeSupport644_rest_008 ridgeSupport644_rest_009 ridgeSupport644_rest_009
    ridgeSupport644_008 ridgeSupport644_suffix_009 ridgeSupport644_008_decode ridgeSupport644_suffix_decode_009
theorem ridgeSupport644_suffix_decode_007 : PackedRawNatGrowth.readList 13 45 ridgeSupport644_rest_007 =
    (ridgeSupport644_suffix_007, ridgeSupport644_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 13
    ridgeSupport644_rest_007 ridgeSupport644_rest_008 ridgeSupport644_rest_009
    ridgeSupport644_007 ridgeSupport644_suffix_008 ridgeSupport644_007_decode ridgeSupport644_suffix_decode_008
theorem ridgeSupport644_suffix_decode_006 : PackedRawNatGrowth.readList 13 77 ridgeSupport644_rest_006 =
    (ridgeSupport644_suffix_006, ridgeSupport644_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 45
    ridgeSupport644_rest_006 ridgeSupport644_rest_007 ridgeSupport644_rest_009
    ridgeSupport644_006 ridgeSupport644_suffix_007 ridgeSupport644_006_decode ridgeSupport644_suffix_decode_007
theorem ridgeSupport644_suffix_decode_005 : PackedRawNatGrowth.readList 13 109 ridgeSupport644_rest_005 =
    (ridgeSupport644_suffix_005, ridgeSupport644_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 77
    ridgeSupport644_rest_005 ridgeSupport644_rest_006 ridgeSupport644_rest_009
    ridgeSupport644_005 ridgeSupport644_suffix_006 ridgeSupport644_005_decode ridgeSupport644_suffix_decode_006
theorem ridgeSupport644_suffix_decode_004 : PackedRawNatGrowth.readList 13 141 ridgeSupport644_rest_004 =
    (ridgeSupport644_suffix_004, ridgeSupport644_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 109
    ridgeSupport644_rest_004 ridgeSupport644_rest_005 ridgeSupport644_rest_009
    ridgeSupport644_004 ridgeSupport644_suffix_005 ridgeSupport644_004_decode ridgeSupport644_suffix_decode_005
theorem ridgeSupport644_suffix_decode_003 : PackedRawNatGrowth.readList 13 173 ridgeSupport644_rest_003 =
    (ridgeSupport644_suffix_003, ridgeSupport644_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 141
    ridgeSupport644_rest_003 ridgeSupport644_rest_004 ridgeSupport644_rest_009
    ridgeSupport644_003 ridgeSupport644_suffix_004 ridgeSupport644_003_decode ridgeSupport644_suffix_decode_004
theorem ridgeSupport644_suffix_decode_002 : PackedRawNatGrowth.readList 13 205 ridgeSupport644_rest_002 =
    (ridgeSupport644_suffix_002, ridgeSupport644_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 173
    ridgeSupport644_rest_002 ridgeSupport644_rest_003 ridgeSupport644_rest_009
    ridgeSupport644_002 ridgeSupport644_suffix_003 ridgeSupport644_002_decode ridgeSupport644_suffix_decode_003
theorem ridgeSupport644_suffix_decode_001 : PackedRawNatGrowth.readList 13 237 ridgeSupport644_rest_001 =
    (ridgeSupport644_suffix_001, ridgeSupport644_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 205
    ridgeSupport644_rest_001 ridgeSupport644_rest_002 ridgeSupport644_rest_009
    ridgeSupport644_001 ridgeSupport644_suffix_002 ridgeSupport644_001_decode ridgeSupport644_suffix_decode_002
theorem ridgeSupport644_suffix_decode_000 : PackedRawNatGrowth.readList 13 269 ridgeSupport644_rest_000 =
    (ridgeSupport644_suffix_000, ridgeSupport644_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 237
    ridgeSupport644_rest_000 ridgeSupport644_rest_001 ridgeSupport644_rest_009
    ridgeSupport644_000 ridgeSupport644_suffix_001 ridgeSupport644_000_decode ridgeSupport644_suffix_decode_001
theorem ridgeSupport644_eq : candidateRows 644 = ridgeSupport644_suffix_000 := by
  change candidateSupports 644 = ridgeSupport644_suffix_000
  rw [ridgeSupport644_source]
  exact congrArg Prod.fst ridgeSupport644_suffix_decode_000
theorem ridgeTest_large_644 : ridgeTest 644 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport644_eq]
    simp only [ridgeSupport644_suffix_000, ridgeSupport644_suffix_001, ridgeSupport644_suffix_002, ridgeSupport644_suffix_003, ridgeSupport644_suffix_004, ridgeSupport644_suffix_005, ridgeSupport644_suffix_006, ridgeSupport644_suffix_007, ridgeSupport644_suffix_008, ridgeSupport644_suffix_009, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport644_000_mask, ridgeSupport644_001_mask, ridgeSupport644_002_mask, ridgeSupport644_003_mask, ridgeSupport644_004_mask, ridgeSupport644_005_mask, ridgeSupport644_006_mask, ridgeSupport644_007_mask, ridgeSupport644_008_mask]
    decide +kernel
  · rw [ridgeSupport644_eq]
    simp only [ridgeSupport644_suffix_000, ridgeSupport644_suffix_001, ridgeSupport644_suffix_002, ridgeSupport644_suffix_003, ridgeSupport644_suffix_004, ridgeSupport644_suffix_005, ridgeSupport644_suffix_006, ridgeSupport644_suffix_007, ridgeSupport644_suffix_008, ridgeSupport644_suffix_009, List.all_append, List.all_nil, ridgeSupport644_000_checked, ridgeSupport644_001_checked, ridgeSupport644_002_checked, ridgeSupport644_003_checked, ridgeSupport644_004_checked, ridgeSupport644_005_checked, ridgeSupport644_006_checked, ridgeSupport644_007_checked, ridgeSupport644_008_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixExtra02
