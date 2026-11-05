module
prelude
public import RootedSixExtra02GrowthCacheRidgeSupport336Part000
public import RootedSixExtra02GrowthCacheRidgeSupport336Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra02
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport336_suffix_decode_009 : PackedRawNatGrowth.readList 13 0 ridgeSupport336_rest_009 =
    (ridgeSupport336_suffix_009, ridgeSupport336_rest_009) := by rfl
theorem ridgeSupport336_suffix_decode_008 : PackedRawNatGrowth.readList 13 13 ridgeSupport336_rest_008 =
    (ridgeSupport336_suffix_008, ridgeSupport336_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 13 13 0
    ridgeSupport336_rest_008 ridgeSupport336_rest_009 ridgeSupport336_rest_009
    ridgeSupport336_008 ridgeSupport336_suffix_009 ridgeSupport336_008_decode ridgeSupport336_suffix_decode_009
theorem ridgeSupport336_suffix_decode_007 : PackedRawNatGrowth.readList 13 45 ridgeSupport336_rest_007 =
    (ridgeSupport336_suffix_007, ridgeSupport336_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 13
    ridgeSupport336_rest_007 ridgeSupport336_rest_008 ridgeSupport336_rest_009
    ridgeSupport336_007 ridgeSupport336_suffix_008 ridgeSupport336_007_decode ridgeSupport336_suffix_decode_008
theorem ridgeSupport336_suffix_decode_006 : PackedRawNatGrowth.readList 13 77 ridgeSupport336_rest_006 =
    (ridgeSupport336_suffix_006, ridgeSupport336_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 45
    ridgeSupport336_rest_006 ridgeSupport336_rest_007 ridgeSupport336_rest_009
    ridgeSupport336_006 ridgeSupport336_suffix_007 ridgeSupport336_006_decode ridgeSupport336_suffix_decode_007
theorem ridgeSupport336_suffix_decode_005 : PackedRawNatGrowth.readList 13 109 ridgeSupport336_rest_005 =
    (ridgeSupport336_suffix_005, ridgeSupport336_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 77
    ridgeSupport336_rest_005 ridgeSupport336_rest_006 ridgeSupport336_rest_009
    ridgeSupport336_005 ridgeSupport336_suffix_006 ridgeSupport336_005_decode ridgeSupport336_suffix_decode_006
theorem ridgeSupport336_suffix_decode_004 : PackedRawNatGrowth.readList 13 141 ridgeSupport336_rest_004 =
    (ridgeSupport336_suffix_004, ridgeSupport336_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 109
    ridgeSupport336_rest_004 ridgeSupport336_rest_005 ridgeSupport336_rest_009
    ridgeSupport336_004 ridgeSupport336_suffix_005 ridgeSupport336_004_decode ridgeSupport336_suffix_decode_005
theorem ridgeSupport336_suffix_decode_003 : PackedRawNatGrowth.readList 13 173 ridgeSupport336_rest_003 =
    (ridgeSupport336_suffix_003, ridgeSupport336_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 141
    ridgeSupport336_rest_003 ridgeSupport336_rest_004 ridgeSupport336_rest_009
    ridgeSupport336_003 ridgeSupport336_suffix_004 ridgeSupport336_003_decode ridgeSupport336_suffix_decode_004
theorem ridgeSupport336_suffix_decode_002 : PackedRawNatGrowth.readList 13 205 ridgeSupport336_rest_002 =
    (ridgeSupport336_suffix_002, ridgeSupport336_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 173
    ridgeSupport336_rest_002 ridgeSupport336_rest_003 ridgeSupport336_rest_009
    ridgeSupport336_002 ridgeSupport336_suffix_003 ridgeSupport336_002_decode ridgeSupport336_suffix_decode_003
theorem ridgeSupport336_suffix_decode_001 : PackedRawNatGrowth.readList 13 237 ridgeSupport336_rest_001 =
    (ridgeSupport336_suffix_001, ridgeSupport336_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 205
    ridgeSupport336_rest_001 ridgeSupport336_rest_002 ridgeSupport336_rest_009
    ridgeSupport336_001 ridgeSupport336_suffix_002 ridgeSupport336_001_decode ridgeSupport336_suffix_decode_002
theorem ridgeSupport336_suffix_decode_000 : PackedRawNatGrowth.readList 13 269 ridgeSupport336_rest_000 =
    (ridgeSupport336_suffix_000, ridgeSupport336_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 237
    ridgeSupport336_rest_000 ridgeSupport336_rest_001 ridgeSupport336_rest_009
    ridgeSupport336_000 ridgeSupport336_suffix_001 ridgeSupport336_000_decode ridgeSupport336_suffix_decode_001
theorem ridgeSupport336_eq : candidateRows 336 = ridgeSupport336_suffix_000 := by
  change candidateSupports 336 = ridgeSupport336_suffix_000
  rw [ridgeSupport336_source]
  exact congrArg Prod.fst ridgeSupport336_suffix_decode_000
theorem ridgeTest_large_336 : ridgeTest 336 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport336_eq]
    simp only [ridgeSupport336_suffix_000, ridgeSupport336_suffix_001, ridgeSupport336_suffix_002, ridgeSupport336_suffix_003, ridgeSupport336_suffix_004, ridgeSupport336_suffix_005, ridgeSupport336_suffix_006, ridgeSupport336_suffix_007, ridgeSupport336_suffix_008, ridgeSupport336_suffix_009, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport336_000_mask, ridgeSupport336_001_mask, ridgeSupport336_002_mask, ridgeSupport336_003_mask, ridgeSupport336_004_mask, ridgeSupport336_005_mask, ridgeSupport336_006_mask, ridgeSupport336_007_mask, ridgeSupport336_008_mask]
    decide +kernel
  · rw [ridgeSupport336_eq]
    simp only [ridgeSupport336_suffix_000, ridgeSupport336_suffix_001, ridgeSupport336_suffix_002, ridgeSupport336_suffix_003, ridgeSupport336_suffix_004, ridgeSupport336_suffix_005, ridgeSupport336_suffix_006, ridgeSupport336_suffix_007, ridgeSupport336_suffix_008, ridgeSupport336_suffix_009, List.all_append, List.all_nil, ridgeSupport336_000_checked, ridgeSupport336_001_checked, ridgeSupport336_002_checked, ridgeSupport336_003_checked, ridgeSupport336_004_checked, ridgeSupport336_005_checked, ridgeSupport336_006_checked, ridgeSupport336_007_checked, ridgeSupport336_008_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixExtra02
