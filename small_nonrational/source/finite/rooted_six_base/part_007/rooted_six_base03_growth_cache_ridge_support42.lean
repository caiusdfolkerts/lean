module
prelude
public import RootedSixBase03GrowthCacheRidgeSupport42Part000
public import RootedSixBase03GrowthCacheRidgeSupport42Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase03
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport42_suffix_decode_011 : PackedRawNatGrowth.readList 13 0 ridgeSupport42_rest_011 =
    (ridgeSupport42_suffix_011, ridgeSupport42_rest_011) := by rfl
theorem ridgeSupport42_suffix_decode_010 : PackedRawNatGrowth.readList 13 21 ridgeSupport42_rest_010 =
    (ridgeSupport42_suffix_010, ridgeSupport42_rest_011) :=
  PackedRawNatGrowth.readList_append_of_eq 13 21 0
    ridgeSupport42_rest_010 ridgeSupport42_rest_011 ridgeSupport42_rest_011
    ridgeSupport42_010 ridgeSupport42_suffix_011 ridgeSupport42_010_decode ridgeSupport42_suffix_decode_011
theorem ridgeSupport42_suffix_decode_009 : PackedRawNatGrowth.readList 13 53 ridgeSupport42_rest_009 =
    (ridgeSupport42_suffix_009, ridgeSupport42_rest_011) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 21
    ridgeSupport42_rest_009 ridgeSupport42_rest_010 ridgeSupport42_rest_011
    ridgeSupport42_009 ridgeSupport42_suffix_010 ridgeSupport42_009_decode ridgeSupport42_suffix_decode_010
theorem ridgeSupport42_suffix_decode_008 : PackedRawNatGrowth.readList 13 85 ridgeSupport42_rest_008 =
    (ridgeSupport42_suffix_008, ridgeSupport42_rest_011) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 53
    ridgeSupport42_rest_008 ridgeSupport42_rest_009 ridgeSupport42_rest_011
    ridgeSupport42_008 ridgeSupport42_suffix_009 ridgeSupport42_008_decode ridgeSupport42_suffix_decode_009
theorem ridgeSupport42_suffix_decode_007 : PackedRawNatGrowth.readList 13 117 ridgeSupport42_rest_007 =
    (ridgeSupport42_suffix_007, ridgeSupport42_rest_011) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 85
    ridgeSupport42_rest_007 ridgeSupport42_rest_008 ridgeSupport42_rest_011
    ridgeSupport42_007 ridgeSupport42_suffix_008 ridgeSupport42_007_decode ridgeSupport42_suffix_decode_008
theorem ridgeSupport42_suffix_decode_006 : PackedRawNatGrowth.readList 13 149 ridgeSupport42_rest_006 =
    (ridgeSupport42_suffix_006, ridgeSupport42_rest_011) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 117
    ridgeSupport42_rest_006 ridgeSupport42_rest_007 ridgeSupport42_rest_011
    ridgeSupport42_006 ridgeSupport42_suffix_007 ridgeSupport42_006_decode ridgeSupport42_suffix_decode_007
theorem ridgeSupport42_suffix_decode_005 : PackedRawNatGrowth.readList 13 181 ridgeSupport42_rest_005 =
    (ridgeSupport42_suffix_005, ridgeSupport42_rest_011) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 149
    ridgeSupport42_rest_005 ridgeSupport42_rest_006 ridgeSupport42_rest_011
    ridgeSupport42_005 ridgeSupport42_suffix_006 ridgeSupport42_005_decode ridgeSupport42_suffix_decode_006
theorem ridgeSupport42_suffix_decode_004 : PackedRawNatGrowth.readList 13 213 ridgeSupport42_rest_004 =
    (ridgeSupport42_suffix_004, ridgeSupport42_rest_011) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 181
    ridgeSupport42_rest_004 ridgeSupport42_rest_005 ridgeSupport42_rest_011
    ridgeSupport42_004 ridgeSupport42_suffix_005 ridgeSupport42_004_decode ridgeSupport42_suffix_decode_005
theorem ridgeSupport42_suffix_decode_003 : PackedRawNatGrowth.readList 13 245 ridgeSupport42_rest_003 =
    (ridgeSupport42_suffix_003, ridgeSupport42_rest_011) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 213
    ridgeSupport42_rest_003 ridgeSupport42_rest_004 ridgeSupport42_rest_011
    ridgeSupport42_003 ridgeSupport42_suffix_004 ridgeSupport42_003_decode ridgeSupport42_suffix_decode_004
theorem ridgeSupport42_suffix_decode_002 : PackedRawNatGrowth.readList 13 277 ridgeSupport42_rest_002 =
    (ridgeSupport42_suffix_002, ridgeSupport42_rest_011) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 245
    ridgeSupport42_rest_002 ridgeSupport42_rest_003 ridgeSupport42_rest_011
    ridgeSupport42_002 ridgeSupport42_suffix_003 ridgeSupport42_002_decode ridgeSupport42_suffix_decode_003
theorem ridgeSupport42_suffix_decode_001 : PackedRawNatGrowth.readList 13 309 ridgeSupport42_rest_001 =
    (ridgeSupport42_suffix_001, ridgeSupport42_rest_011) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 277
    ridgeSupport42_rest_001 ridgeSupport42_rest_002 ridgeSupport42_rest_011
    ridgeSupport42_001 ridgeSupport42_suffix_002 ridgeSupport42_001_decode ridgeSupport42_suffix_decode_002
theorem ridgeSupport42_suffix_decode_000 : PackedRawNatGrowth.readList 13 341 ridgeSupport42_rest_000 =
    (ridgeSupport42_suffix_000, ridgeSupport42_rest_011) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 309
    ridgeSupport42_rest_000 ridgeSupport42_rest_001 ridgeSupport42_rest_011
    ridgeSupport42_000 ridgeSupport42_suffix_001 ridgeSupport42_000_decode ridgeSupport42_suffix_decode_001
theorem ridgeSupport42_eq : candidateSupports 42 = ridgeSupport42_suffix_000 := by
  rw [ridgeSupport42_source]
  exact congrArg Prod.fst ridgeSupport42_suffix_decode_000
theorem ridgeTest_large_42 : ridgeTest 42 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [show candidateRows 42 = ridgeSupport42_suffix_000 from ridgeSupport42_eq]
    simp only [ridgeSupport42_suffix_000, ridgeSupport42_suffix_001, ridgeSupport42_suffix_002, ridgeSupport42_suffix_003, ridgeSupport42_suffix_004, ridgeSupport42_suffix_005, ridgeSupport42_suffix_006, ridgeSupport42_suffix_007, ridgeSupport42_suffix_008, ridgeSupport42_suffix_009, ridgeSupport42_suffix_010, ridgeSupport42_suffix_011, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport42_000_mask, ridgeSupport42_001_mask, ridgeSupport42_002_mask, ridgeSupport42_003_mask, ridgeSupport42_004_mask, ridgeSupport42_005_mask, ridgeSupport42_006_mask, ridgeSupport42_007_mask, ridgeSupport42_008_mask, ridgeSupport42_009_mask, ridgeSupport42_010_mask]
    decide +kernel
  · rw [show candidateRows 42 = ridgeSupport42_suffix_000 from ridgeSupport42_eq]
    simp only [ridgeSupport42_suffix_000, ridgeSupport42_suffix_001, ridgeSupport42_suffix_002, ridgeSupport42_suffix_003, ridgeSupport42_suffix_004, ridgeSupport42_suffix_005, ridgeSupport42_suffix_006, ridgeSupport42_suffix_007, ridgeSupport42_suffix_008, ridgeSupport42_suffix_009, ridgeSupport42_suffix_010, ridgeSupport42_suffix_011, List.all_append, List.all_nil, ridgeSupport42_000_checked, ridgeSupport42_001_checked, ridgeSupport42_002_checked, ridgeSupport42_003_checked, ridgeSupport42_004_checked, ridgeSupport42_005_checked, ridgeSupport42_006_checked, ridgeSupport42_007_checked, ridgeSupport42_008_checked, ridgeSupport42_009_checked, ridgeSupport42_010_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase03
