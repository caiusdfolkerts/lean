module
prelude
public import RootedSevenTwoSix13GrowthCacheRidgeSupport112Part000
public import RootedSevenTwoSix13GrowthCacheRidgeSupport112Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSevenTwoSix13
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport112_suffix_decode_012 : PackedRawNatGrowth.readList 11 0 ridgeSupport112_rest_012 =
    (ridgeSupport112_suffix_012, ridgeSupport112_rest_012) := by rfl
theorem ridgeSupport112_suffix_decode_011 : PackedRawNatGrowth.readList 11 21 ridgeSupport112_rest_011 =
    (ridgeSupport112_suffix_011, ridgeSupport112_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 11 21 0
    ridgeSupport112_rest_011 ridgeSupport112_rest_012 ridgeSupport112_rest_012
    ridgeSupport112_011 ridgeSupport112_suffix_012 ridgeSupport112_011_decode ridgeSupport112_suffix_decode_012
theorem ridgeSupport112_suffix_decode_010 : PackedRawNatGrowth.readList 11 53 ridgeSupport112_rest_010 =
    (ridgeSupport112_suffix_010, ridgeSupport112_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 11 32 21
    ridgeSupport112_rest_010 ridgeSupport112_rest_011 ridgeSupport112_rest_012
    ridgeSupport112_010 ridgeSupport112_suffix_011 ridgeSupport112_010_decode ridgeSupport112_suffix_decode_011
theorem ridgeSupport112_suffix_decode_009 : PackedRawNatGrowth.readList 11 85 ridgeSupport112_rest_009 =
    (ridgeSupport112_suffix_009, ridgeSupport112_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 11 32 53
    ridgeSupport112_rest_009 ridgeSupport112_rest_010 ridgeSupport112_rest_012
    ridgeSupport112_009 ridgeSupport112_suffix_010 ridgeSupport112_009_decode ridgeSupport112_suffix_decode_010
theorem ridgeSupport112_suffix_decode_008 : PackedRawNatGrowth.readList 11 117 ridgeSupport112_rest_008 =
    (ridgeSupport112_suffix_008, ridgeSupport112_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 11 32 85
    ridgeSupport112_rest_008 ridgeSupport112_rest_009 ridgeSupport112_rest_012
    ridgeSupport112_008 ridgeSupport112_suffix_009 ridgeSupport112_008_decode ridgeSupport112_suffix_decode_009
theorem ridgeSupport112_suffix_decode_007 : PackedRawNatGrowth.readList 11 149 ridgeSupport112_rest_007 =
    (ridgeSupport112_suffix_007, ridgeSupport112_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 11 32 117
    ridgeSupport112_rest_007 ridgeSupport112_rest_008 ridgeSupport112_rest_012
    ridgeSupport112_007 ridgeSupport112_suffix_008 ridgeSupport112_007_decode ridgeSupport112_suffix_decode_008
theorem ridgeSupport112_suffix_decode_006 : PackedRawNatGrowth.readList 11 181 ridgeSupport112_rest_006 =
    (ridgeSupport112_suffix_006, ridgeSupport112_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 11 32 149
    ridgeSupport112_rest_006 ridgeSupport112_rest_007 ridgeSupport112_rest_012
    ridgeSupport112_006 ridgeSupport112_suffix_007 ridgeSupport112_006_decode ridgeSupport112_suffix_decode_007
theorem ridgeSupport112_suffix_decode_005 : PackedRawNatGrowth.readList 11 213 ridgeSupport112_rest_005 =
    (ridgeSupport112_suffix_005, ridgeSupport112_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 11 32 181
    ridgeSupport112_rest_005 ridgeSupport112_rest_006 ridgeSupport112_rest_012
    ridgeSupport112_005 ridgeSupport112_suffix_006 ridgeSupport112_005_decode ridgeSupport112_suffix_decode_006
theorem ridgeSupport112_suffix_decode_004 : PackedRawNatGrowth.readList 11 245 ridgeSupport112_rest_004 =
    (ridgeSupport112_suffix_004, ridgeSupport112_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 11 32 213
    ridgeSupport112_rest_004 ridgeSupport112_rest_005 ridgeSupport112_rest_012
    ridgeSupport112_004 ridgeSupport112_suffix_005 ridgeSupport112_004_decode ridgeSupport112_suffix_decode_005
theorem ridgeSupport112_suffix_decode_003 : PackedRawNatGrowth.readList 11 277 ridgeSupport112_rest_003 =
    (ridgeSupport112_suffix_003, ridgeSupport112_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 11 32 245
    ridgeSupport112_rest_003 ridgeSupport112_rest_004 ridgeSupport112_rest_012
    ridgeSupport112_003 ridgeSupport112_suffix_004 ridgeSupport112_003_decode ridgeSupport112_suffix_decode_004
theorem ridgeSupport112_suffix_decode_002 : PackedRawNatGrowth.readList 11 309 ridgeSupport112_rest_002 =
    (ridgeSupport112_suffix_002, ridgeSupport112_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 11 32 277
    ridgeSupport112_rest_002 ridgeSupport112_rest_003 ridgeSupport112_rest_012
    ridgeSupport112_002 ridgeSupport112_suffix_003 ridgeSupport112_002_decode ridgeSupport112_suffix_decode_003
theorem ridgeSupport112_suffix_decode_001 : PackedRawNatGrowth.readList 11 341 ridgeSupport112_rest_001 =
    (ridgeSupport112_suffix_001, ridgeSupport112_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 11 32 309
    ridgeSupport112_rest_001 ridgeSupport112_rest_002 ridgeSupport112_rest_012
    ridgeSupport112_001 ridgeSupport112_suffix_002 ridgeSupport112_001_decode ridgeSupport112_suffix_decode_002
theorem ridgeSupport112_suffix_decode_000 : PackedRawNatGrowth.readList 11 373 ridgeSupport112_rest_000 =
    (ridgeSupport112_suffix_000, ridgeSupport112_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 11 32 341
    ridgeSupport112_rest_000 ridgeSupport112_rest_001 ridgeSupport112_rest_012
    ridgeSupport112_000 ridgeSupport112_suffix_001 ridgeSupport112_000_decode ridgeSupport112_suffix_decode_001
theorem ridgeSupport112_eq : candidateRows 112 = ridgeSupport112_suffix_000 := by
  rw [ridgeSupport112_source]
  exact congrArg Prod.fst ridgeSupport112_suffix_decode_000
theorem ridgeTest_large_112 : ridgeTest 112 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport112_eq]
    simp only [ridgeSupport112_suffix_000, ridgeSupport112_suffix_001, ridgeSupport112_suffix_002, ridgeSupport112_suffix_003, ridgeSupport112_suffix_004, ridgeSupport112_suffix_005, ridgeSupport112_suffix_006, ridgeSupport112_suffix_007, ridgeSupport112_suffix_008, ridgeSupport112_suffix_009, ridgeSupport112_suffix_010, ridgeSupport112_suffix_011, ridgeSupport112_suffix_012, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport112_000_mask, ridgeSupport112_001_mask, ridgeSupport112_002_mask, ridgeSupport112_003_mask, ridgeSupport112_004_mask, ridgeSupport112_005_mask, ridgeSupport112_006_mask, ridgeSupport112_007_mask, ridgeSupport112_008_mask, ridgeSupport112_009_mask, ridgeSupport112_010_mask, ridgeSupport112_011_mask]
    decide +kernel
  · rw [ridgeSupport112_eq]
    simp only [ridgeSupport112_suffix_000, ridgeSupport112_suffix_001, ridgeSupport112_suffix_002, ridgeSupport112_suffix_003, ridgeSupport112_suffix_004, ridgeSupport112_suffix_005, ridgeSupport112_suffix_006, ridgeSupport112_suffix_007, ridgeSupport112_suffix_008, ridgeSupport112_suffix_009, ridgeSupport112_suffix_010, ridgeSupport112_suffix_011, ridgeSupport112_suffix_012, List.all_append, List.all_nil, ridgeSupport112_000_checked, ridgeSupport112_001_checked, ridgeSupport112_002_checked, ridgeSupport112_003_checked, ridgeSupport112_004_checked, ridgeSupport112_005_checked, ridgeSupport112_006_checked, ridgeSupport112_007_checked, ridgeSupport112_008_checked, ridgeSupport112_009_checked, ridgeSupport112_010_checked, ridgeSupport112_011_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSevenTwoSix13
