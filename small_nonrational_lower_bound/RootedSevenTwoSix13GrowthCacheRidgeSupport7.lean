module
prelude
public import RootedSevenTwoSix13GrowthCacheRidgeSupport7Part000
public import RootedSevenTwoSix13GrowthCacheRidgeSupport7Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSevenTwoSix13
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport7_suffix_decode_012 : PackedRawNatGrowth.readList 11 0 ridgeSupport7_rest_012 =
    (ridgeSupport7_suffix_012, ridgeSupport7_rest_012) := by rfl
theorem ridgeSupport7_suffix_decode_011 : PackedRawNatGrowth.readList 11 21 ridgeSupport7_rest_011 =
    (ridgeSupport7_suffix_011, ridgeSupport7_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 11 21 0
    ridgeSupport7_rest_011 ridgeSupport7_rest_012 ridgeSupport7_rest_012
    ridgeSupport7_011 ridgeSupport7_suffix_012 ridgeSupport7_011_decode ridgeSupport7_suffix_decode_012
theorem ridgeSupport7_suffix_decode_010 : PackedRawNatGrowth.readList 11 53 ridgeSupport7_rest_010 =
    (ridgeSupport7_suffix_010, ridgeSupport7_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 11 32 21
    ridgeSupport7_rest_010 ridgeSupport7_rest_011 ridgeSupport7_rest_012
    ridgeSupport7_010 ridgeSupport7_suffix_011 ridgeSupport7_010_decode ridgeSupport7_suffix_decode_011
theorem ridgeSupport7_suffix_decode_009 : PackedRawNatGrowth.readList 11 85 ridgeSupport7_rest_009 =
    (ridgeSupport7_suffix_009, ridgeSupport7_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 11 32 53
    ridgeSupport7_rest_009 ridgeSupport7_rest_010 ridgeSupport7_rest_012
    ridgeSupport7_009 ridgeSupport7_suffix_010 ridgeSupport7_009_decode ridgeSupport7_suffix_decode_010
theorem ridgeSupport7_suffix_decode_008 : PackedRawNatGrowth.readList 11 117 ridgeSupport7_rest_008 =
    (ridgeSupport7_suffix_008, ridgeSupport7_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 11 32 85
    ridgeSupport7_rest_008 ridgeSupport7_rest_009 ridgeSupport7_rest_012
    ridgeSupport7_008 ridgeSupport7_suffix_009 ridgeSupport7_008_decode ridgeSupport7_suffix_decode_009
theorem ridgeSupport7_suffix_decode_007 : PackedRawNatGrowth.readList 11 149 ridgeSupport7_rest_007 =
    (ridgeSupport7_suffix_007, ridgeSupport7_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 11 32 117
    ridgeSupport7_rest_007 ridgeSupport7_rest_008 ridgeSupport7_rest_012
    ridgeSupport7_007 ridgeSupport7_suffix_008 ridgeSupport7_007_decode ridgeSupport7_suffix_decode_008
theorem ridgeSupport7_suffix_decode_006 : PackedRawNatGrowth.readList 11 181 ridgeSupport7_rest_006 =
    (ridgeSupport7_suffix_006, ridgeSupport7_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 11 32 149
    ridgeSupport7_rest_006 ridgeSupport7_rest_007 ridgeSupport7_rest_012
    ridgeSupport7_006 ridgeSupport7_suffix_007 ridgeSupport7_006_decode ridgeSupport7_suffix_decode_007
theorem ridgeSupport7_suffix_decode_005 : PackedRawNatGrowth.readList 11 213 ridgeSupport7_rest_005 =
    (ridgeSupport7_suffix_005, ridgeSupport7_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 11 32 181
    ridgeSupport7_rest_005 ridgeSupport7_rest_006 ridgeSupport7_rest_012
    ridgeSupport7_005 ridgeSupport7_suffix_006 ridgeSupport7_005_decode ridgeSupport7_suffix_decode_006
theorem ridgeSupport7_suffix_decode_004 : PackedRawNatGrowth.readList 11 245 ridgeSupport7_rest_004 =
    (ridgeSupport7_suffix_004, ridgeSupport7_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 11 32 213
    ridgeSupport7_rest_004 ridgeSupport7_rest_005 ridgeSupport7_rest_012
    ridgeSupport7_004 ridgeSupport7_suffix_005 ridgeSupport7_004_decode ridgeSupport7_suffix_decode_005
theorem ridgeSupport7_suffix_decode_003 : PackedRawNatGrowth.readList 11 277 ridgeSupport7_rest_003 =
    (ridgeSupport7_suffix_003, ridgeSupport7_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 11 32 245
    ridgeSupport7_rest_003 ridgeSupport7_rest_004 ridgeSupport7_rest_012
    ridgeSupport7_003 ridgeSupport7_suffix_004 ridgeSupport7_003_decode ridgeSupport7_suffix_decode_004
theorem ridgeSupport7_suffix_decode_002 : PackedRawNatGrowth.readList 11 309 ridgeSupport7_rest_002 =
    (ridgeSupport7_suffix_002, ridgeSupport7_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 11 32 277
    ridgeSupport7_rest_002 ridgeSupport7_rest_003 ridgeSupport7_rest_012
    ridgeSupport7_002 ridgeSupport7_suffix_003 ridgeSupport7_002_decode ridgeSupport7_suffix_decode_003
theorem ridgeSupport7_suffix_decode_001 : PackedRawNatGrowth.readList 11 341 ridgeSupport7_rest_001 =
    (ridgeSupport7_suffix_001, ridgeSupport7_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 11 32 309
    ridgeSupport7_rest_001 ridgeSupport7_rest_002 ridgeSupport7_rest_012
    ridgeSupport7_001 ridgeSupport7_suffix_002 ridgeSupport7_001_decode ridgeSupport7_suffix_decode_002
theorem ridgeSupport7_suffix_decode_000 : PackedRawNatGrowth.readList 11 373 ridgeSupport7_rest_000 =
    (ridgeSupport7_suffix_000, ridgeSupport7_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 11 32 341
    ridgeSupport7_rest_000 ridgeSupport7_rest_001 ridgeSupport7_rest_012
    ridgeSupport7_000 ridgeSupport7_suffix_001 ridgeSupport7_000_decode ridgeSupport7_suffix_decode_001
theorem ridgeSupport7_eq : candidateRows 7 = ridgeSupport7_suffix_000 := by
  rw [ridgeSupport7_source]
  exact congrArg Prod.fst ridgeSupport7_suffix_decode_000
theorem ridgeTest_large_7 : ridgeTest 7 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport7_eq]
    simp only [ridgeSupport7_suffix_000, ridgeSupport7_suffix_001, ridgeSupport7_suffix_002, ridgeSupport7_suffix_003, ridgeSupport7_suffix_004, ridgeSupport7_suffix_005, ridgeSupport7_suffix_006, ridgeSupport7_suffix_007, ridgeSupport7_suffix_008, ridgeSupport7_suffix_009, ridgeSupport7_suffix_010, ridgeSupport7_suffix_011, ridgeSupport7_suffix_012, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport7_000_mask, ridgeSupport7_001_mask, ridgeSupport7_002_mask, ridgeSupport7_003_mask, ridgeSupport7_004_mask, ridgeSupport7_005_mask, ridgeSupport7_006_mask, ridgeSupport7_007_mask, ridgeSupport7_008_mask, ridgeSupport7_009_mask, ridgeSupport7_010_mask, ridgeSupport7_011_mask]
    decide +kernel
  · rw [ridgeSupport7_eq]
    simp only [ridgeSupport7_suffix_000, ridgeSupport7_suffix_001, ridgeSupport7_suffix_002, ridgeSupport7_suffix_003, ridgeSupport7_suffix_004, ridgeSupport7_suffix_005, ridgeSupport7_suffix_006, ridgeSupport7_suffix_007, ridgeSupport7_suffix_008, ridgeSupport7_suffix_009, ridgeSupport7_suffix_010, ridgeSupport7_suffix_011, ridgeSupport7_suffix_012, List.all_append, List.all_nil, ridgeSupport7_000_checked, ridgeSupport7_001_checked, ridgeSupport7_002_checked, ridgeSupport7_003_checked, ridgeSupport7_004_checked, ridgeSupport7_005_checked, ridgeSupport7_006_checked, ridgeSupport7_007_checked, ridgeSupport7_008_checked, ridgeSupport7_009_checked, ridgeSupport7_010_checked, ridgeSupport7_011_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSevenTwoSix13
