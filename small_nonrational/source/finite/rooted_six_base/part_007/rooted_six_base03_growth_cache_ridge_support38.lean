module
prelude
public import RootedSixBase03GrowthCacheRidgeSupport38Part000
public import RootedSixBase03GrowthCacheRidgeSupport38Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase03
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport38_suffix_decode_011 : PackedRawNatGrowth.readList 13 0 ridgeSupport38_rest_011 =
    (ridgeSupport38_suffix_011, ridgeSupport38_rest_011) := by rfl
theorem ridgeSupport38_suffix_decode_010 : PackedRawNatGrowth.readList 13 21 ridgeSupport38_rest_010 =
    (ridgeSupport38_suffix_010, ridgeSupport38_rest_011) :=
  PackedRawNatGrowth.readList_append_of_eq 13 21 0
    ridgeSupport38_rest_010 ridgeSupport38_rest_011 ridgeSupport38_rest_011
    ridgeSupport38_010 ridgeSupport38_suffix_011 ridgeSupport38_010_decode ridgeSupport38_suffix_decode_011
theorem ridgeSupport38_suffix_decode_009 : PackedRawNatGrowth.readList 13 53 ridgeSupport38_rest_009 =
    (ridgeSupport38_suffix_009, ridgeSupport38_rest_011) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 21
    ridgeSupport38_rest_009 ridgeSupport38_rest_010 ridgeSupport38_rest_011
    ridgeSupport38_009 ridgeSupport38_suffix_010 ridgeSupport38_009_decode ridgeSupport38_suffix_decode_010
theorem ridgeSupport38_suffix_decode_008 : PackedRawNatGrowth.readList 13 85 ridgeSupport38_rest_008 =
    (ridgeSupport38_suffix_008, ridgeSupport38_rest_011) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 53
    ridgeSupport38_rest_008 ridgeSupport38_rest_009 ridgeSupport38_rest_011
    ridgeSupport38_008 ridgeSupport38_suffix_009 ridgeSupport38_008_decode ridgeSupport38_suffix_decode_009
theorem ridgeSupport38_suffix_decode_007 : PackedRawNatGrowth.readList 13 117 ridgeSupport38_rest_007 =
    (ridgeSupport38_suffix_007, ridgeSupport38_rest_011) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 85
    ridgeSupport38_rest_007 ridgeSupport38_rest_008 ridgeSupport38_rest_011
    ridgeSupport38_007 ridgeSupport38_suffix_008 ridgeSupport38_007_decode ridgeSupport38_suffix_decode_008
theorem ridgeSupport38_suffix_decode_006 : PackedRawNatGrowth.readList 13 149 ridgeSupport38_rest_006 =
    (ridgeSupport38_suffix_006, ridgeSupport38_rest_011) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 117
    ridgeSupport38_rest_006 ridgeSupport38_rest_007 ridgeSupport38_rest_011
    ridgeSupport38_006 ridgeSupport38_suffix_007 ridgeSupport38_006_decode ridgeSupport38_suffix_decode_007
theorem ridgeSupport38_suffix_decode_005 : PackedRawNatGrowth.readList 13 181 ridgeSupport38_rest_005 =
    (ridgeSupport38_suffix_005, ridgeSupport38_rest_011) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 149
    ridgeSupport38_rest_005 ridgeSupport38_rest_006 ridgeSupport38_rest_011
    ridgeSupport38_005 ridgeSupport38_suffix_006 ridgeSupport38_005_decode ridgeSupport38_suffix_decode_006
theorem ridgeSupport38_suffix_decode_004 : PackedRawNatGrowth.readList 13 213 ridgeSupport38_rest_004 =
    (ridgeSupport38_suffix_004, ridgeSupport38_rest_011) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 181
    ridgeSupport38_rest_004 ridgeSupport38_rest_005 ridgeSupport38_rest_011
    ridgeSupport38_004 ridgeSupport38_suffix_005 ridgeSupport38_004_decode ridgeSupport38_suffix_decode_005
theorem ridgeSupport38_suffix_decode_003 : PackedRawNatGrowth.readList 13 245 ridgeSupport38_rest_003 =
    (ridgeSupport38_suffix_003, ridgeSupport38_rest_011) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 213
    ridgeSupport38_rest_003 ridgeSupport38_rest_004 ridgeSupport38_rest_011
    ridgeSupport38_003 ridgeSupport38_suffix_004 ridgeSupport38_003_decode ridgeSupport38_suffix_decode_004
theorem ridgeSupport38_suffix_decode_002 : PackedRawNatGrowth.readList 13 277 ridgeSupport38_rest_002 =
    (ridgeSupport38_suffix_002, ridgeSupport38_rest_011) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 245
    ridgeSupport38_rest_002 ridgeSupport38_rest_003 ridgeSupport38_rest_011
    ridgeSupport38_002 ridgeSupport38_suffix_003 ridgeSupport38_002_decode ridgeSupport38_suffix_decode_003
theorem ridgeSupport38_suffix_decode_001 : PackedRawNatGrowth.readList 13 309 ridgeSupport38_rest_001 =
    (ridgeSupport38_suffix_001, ridgeSupport38_rest_011) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 277
    ridgeSupport38_rest_001 ridgeSupport38_rest_002 ridgeSupport38_rest_011
    ridgeSupport38_001 ridgeSupport38_suffix_002 ridgeSupport38_001_decode ridgeSupport38_suffix_decode_002
theorem ridgeSupport38_suffix_decode_000 : PackedRawNatGrowth.readList 13 341 ridgeSupport38_rest_000 =
    (ridgeSupport38_suffix_000, ridgeSupport38_rest_011) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 309
    ridgeSupport38_rest_000 ridgeSupport38_rest_001 ridgeSupport38_rest_011
    ridgeSupport38_000 ridgeSupport38_suffix_001 ridgeSupport38_000_decode ridgeSupport38_suffix_decode_001
theorem ridgeSupport38_eq : candidateSupports 38 = ridgeSupport38_suffix_000 := by
  rw [ridgeSupport38_source]
  exact congrArg Prod.fst ridgeSupport38_suffix_decode_000
theorem ridgeTest_large_38 : ridgeTest 38 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [show candidateRows 38 = ridgeSupport38_suffix_000 from ridgeSupport38_eq]
    simp only [ridgeSupport38_suffix_000, ridgeSupport38_suffix_001, ridgeSupport38_suffix_002, ridgeSupport38_suffix_003, ridgeSupport38_suffix_004, ridgeSupport38_suffix_005, ridgeSupport38_suffix_006, ridgeSupport38_suffix_007, ridgeSupport38_suffix_008, ridgeSupport38_suffix_009, ridgeSupport38_suffix_010, ridgeSupport38_suffix_011, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport38_000_mask, ridgeSupport38_001_mask, ridgeSupport38_002_mask, ridgeSupport38_003_mask, ridgeSupport38_004_mask, ridgeSupport38_005_mask, ridgeSupport38_006_mask, ridgeSupport38_007_mask, ridgeSupport38_008_mask, ridgeSupport38_009_mask, ridgeSupport38_010_mask]
    decide +kernel
  · rw [show candidateRows 38 = ridgeSupport38_suffix_000 from ridgeSupport38_eq]
    simp only [ridgeSupport38_suffix_000, ridgeSupport38_suffix_001, ridgeSupport38_suffix_002, ridgeSupport38_suffix_003, ridgeSupport38_suffix_004, ridgeSupport38_suffix_005, ridgeSupport38_suffix_006, ridgeSupport38_suffix_007, ridgeSupport38_suffix_008, ridgeSupport38_suffix_009, ridgeSupport38_suffix_010, ridgeSupport38_suffix_011, List.all_append, List.all_nil, ridgeSupport38_000_checked, ridgeSupport38_001_checked, ridgeSupport38_002_checked, ridgeSupport38_003_checked, ridgeSupport38_004_checked, ridgeSupport38_005_checked, ridgeSupport38_006_checked, ridgeSupport38_007_checked, ridgeSupport38_008_checked, ridgeSupport38_009_checked, ridgeSupport38_010_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase03
