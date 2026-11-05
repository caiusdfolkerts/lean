module
prelude
public import RootedSixBase01GrowthCacheRidgeSupport834Part000
public import RootedSixBase01GrowthCacheRidgeSupport834Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport834_suffix_decode_012 : PackedRawNatGrowth.readList 14 0 ridgeSupport834_rest_012 =
    (ridgeSupport834_suffix_012, ridgeSupport834_rest_012) := by rfl
theorem ridgeSupport834_suffix_decode_011 : PackedRawNatGrowth.readList 14 5 ridgeSupport834_rest_011 =
    (ridgeSupport834_suffix_011, ridgeSupport834_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 14 5 0
    ridgeSupport834_rest_011 ridgeSupport834_rest_012 ridgeSupport834_rest_012
    ridgeSupport834_011 ridgeSupport834_suffix_012 ridgeSupport834_011_decode ridgeSupport834_suffix_decode_012
theorem ridgeSupport834_suffix_decode_010 : PackedRawNatGrowth.readList 14 37 ridgeSupport834_rest_010 =
    (ridgeSupport834_suffix_010, ridgeSupport834_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 5
    ridgeSupport834_rest_010 ridgeSupport834_rest_011 ridgeSupport834_rest_012
    ridgeSupport834_010 ridgeSupport834_suffix_011 ridgeSupport834_010_decode ridgeSupport834_suffix_decode_011
theorem ridgeSupport834_suffix_decode_009 : PackedRawNatGrowth.readList 14 69 ridgeSupport834_rest_009 =
    (ridgeSupport834_suffix_009, ridgeSupport834_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 37
    ridgeSupport834_rest_009 ridgeSupport834_rest_010 ridgeSupport834_rest_012
    ridgeSupport834_009 ridgeSupport834_suffix_010 ridgeSupport834_009_decode ridgeSupport834_suffix_decode_010
theorem ridgeSupport834_suffix_decode_008 : PackedRawNatGrowth.readList 14 101 ridgeSupport834_rest_008 =
    (ridgeSupport834_suffix_008, ridgeSupport834_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 69
    ridgeSupport834_rest_008 ridgeSupport834_rest_009 ridgeSupport834_rest_012
    ridgeSupport834_008 ridgeSupport834_suffix_009 ridgeSupport834_008_decode ridgeSupport834_suffix_decode_009
theorem ridgeSupport834_suffix_decode_007 : PackedRawNatGrowth.readList 14 133 ridgeSupport834_rest_007 =
    (ridgeSupport834_suffix_007, ridgeSupport834_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 101
    ridgeSupport834_rest_007 ridgeSupport834_rest_008 ridgeSupport834_rest_012
    ridgeSupport834_007 ridgeSupport834_suffix_008 ridgeSupport834_007_decode ridgeSupport834_suffix_decode_008
theorem ridgeSupport834_suffix_decode_006 : PackedRawNatGrowth.readList 14 165 ridgeSupport834_rest_006 =
    (ridgeSupport834_suffix_006, ridgeSupport834_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 133
    ridgeSupport834_rest_006 ridgeSupport834_rest_007 ridgeSupport834_rest_012
    ridgeSupport834_006 ridgeSupport834_suffix_007 ridgeSupport834_006_decode ridgeSupport834_suffix_decode_007
theorem ridgeSupport834_suffix_decode_005 : PackedRawNatGrowth.readList 14 197 ridgeSupport834_rest_005 =
    (ridgeSupport834_suffix_005, ridgeSupport834_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 165
    ridgeSupport834_rest_005 ridgeSupport834_rest_006 ridgeSupport834_rest_012
    ridgeSupport834_005 ridgeSupport834_suffix_006 ridgeSupport834_005_decode ridgeSupport834_suffix_decode_006
theorem ridgeSupport834_suffix_decode_004 : PackedRawNatGrowth.readList 14 229 ridgeSupport834_rest_004 =
    (ridgeSupport834_suffix_004, ridgeSupport834_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 197
    ridgeSupport834_rest_004 ridgeSupport834_rest_005 ridgeSupport834_rest_012
    ridgeSupport834_004 ridgeSupport834_suffix_005 ridgeSupport834_004_decode ridgeSupport834_suffix_decode_005
theorem ridgeSupport834_suffix_decode_003 : PackedRawNatGrowth.readList 14 261 ridgeSupport834_rest_003 =
    (ridgeSupport834_suffix_003, ridgeSupport834_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 229
    ridgeSupport834_rest_003 ridgeSupport834_rest_004 ridgeSupport834_rest_012
    ridgeSupport834_003 ridgeSupport834_suffix_004 ridgeSupport834_003_decode ridgeSupport834_suffix_decode_004
theorem ridgeSupport834_suffix_decode_002 : PackedRawNatGrowth.readList 14 293 ridgeSupport834_rest_002 =
    (ridgeSupport834_suffix_002, ridgeSupport834_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 261
    ridgeSupport834_rest_002 ridgeSupport834_rest_003 ridgeSupport834_rest_012
    ridgeSupport834_002 ridgeSupport834_suffix_003 ridgeSupport834_002_decode ridgeSupport834_suffix_decode_003
theorem ridgeSupport834_suffix_decode_001 : PackedRawNatGrowth.readList 14 325 ridgeSupport834_rest_001 =
    (ridgeSupport834_suffix_001, ridgeSupport834_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 293
    ridgeSupport834_rest_001 ridgeSupport834_rest_002 ridgeSupport834_rest_012
    ridgeSupport834_001 ridgeSupport834_suffix_002 ridgeSupport834_001_decode ridgeSupport834_suffix_decode_002
theorem ridgeSupport834_suffix_decode_000 : PackedRawNatGrowth.readList 14 357 ridgeSupport834_rest_000 =
    (ridgeSupport834_suffix_000, ridgeSupport834_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 325
    ridgeSupport834_rest_000 ridgeSupport834_rest_001 ridgeSupport834_rest_012
    ridgeSupport834_000 ridgeSupport834_suffix_001 ridgeSupport834_000_decode ridgeSupport834_suffix_decode_001
theorem ridgeSupport834_eq : candidateRows 834 = ridgeSupport834_suffix_000 := by
  rw [ridgeSupport834_source]
  exact congrArg Prod.fst ridgeSupport834_suffix_decode_000
theorem ridgeTest_large_834 : ridgeTest 834 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport834_eq]
    simp only [ridgeSupport834_suffix_000, ridgeSupport834_suffix_001, ridgeSupport834_suffix_002, ridgeSupport834_suffix_003, ridgeSupport834_suffix_004, ridgeSupport834_suffix_005, ridgeSupport834_suffix_006, ridgeSupport834_suffix_007, ridgeSupport834_suffix_008, ridgeSupport834_suffix_009, ridgeSupport834_suffix_010, ridgeSupport834_suffix_011, ridgeSupport834_suffix_012, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport834_000_mask, ridgeSupport834_001_mask, ridgeSupport834_002_mask, ridgeSupport834_003_mask, ridgeSupport834_004_mask, ridgeSupport834_005_mask, ridgeSupport834_006_mask, ridgeSupport834_007_mask, ridgeSupport834_008_mask, ridgeSupport834_009_mask, ridgeSupport834_010_mask, ridgeSupport834_011_mask]
    decide +kernel
  · rw [ridgeSupport834_eq]
    simp only [ridgeSupport834_suffix_000, ridgeSupport834_suffix_001, ridgeSupport834_suffix_002, ridgeSupport834_suffix_003, ridgeSupport834_suffix_004, ridgeSupport834_suffix_005, ridgeSupport834_suffix_006, ridgeSupport834_suffix_007, ridgeSupport834_suffix_008, ridgeSupport834_suffix_009, ridgeSupport834_suffix_010, ridgeSupport834_suffix_011, ridgeSupport834_suffix_012, List.all_append, List.all_nil, ridgeSupport834_000_checked, ridgeSupport834_001_checked, ridgeSupport834_002_checked, ridgeSupport834_003_checked, ridgeSupport834_004_checked, ridgeSupport834_005_checked, ridgeSupport834_006_checked, ridgeSupport834_007_checked, ridgeSupport834_008_checked, ridgeSupport834_009_checked, ridgeSupport834_010_checked, ridgeSupport834_011_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase01
