module
prelude
public import RootedSevenTwoSix13GrowthCacheRidgeSupport104Part000
public import RootedSevenTwoSix13GrowthCacheRidgeSupport104Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSevenTwoSix13
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport104_suffix_decode_012 : PackedRawNatGrowth.readList 11 0 ridgeSupport104_rest_012 =
    (ridgeSupport104_suffix_012, ridgeSupport104_rest_012) := by rfl
theorem ridgeSupport104_suffix_decode_011 : PackedRawNatGrowth.readList 11 21 ridgeSupport104_rest_011 =
    (ridgeSupport104_suffix_011, ridgeSupport104_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 11 21 0
    ridgeSupport104_rest_011 ridgeSupport104_rest_012 ridgeSupport104_rest_012
    ridgeSupport104_011 ridgeSupport104_suffix_012 ridgeSupport104_011_decode ridgeSupport104_suffix_decode_012
theorem ridgeSupport104_suffix_decode_010 : PackedRawNatGrowth.readList 11 53 ridgeSupport104_rest_010 =
    (ridgeSupport104_suffix_010, ridgeSupport104_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 11 32 21
    ridgeSupport104_rest_010 ridgeSupport104_rest_011 ridgeSupport104_rest_012
    ridgeSupport104_010 ridgeSupport104_suffix_011 ridgeSupport104_010_decode ridgeSupport104_suffix_decode_011
theorem ridgeSupport104_suffix_decode_009 : PackedRawNatGrowth.readList 11 85 ridgeSupport104_rest_009 =
    (ridgeSupport104_suffix_009, ridgeSupport104_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 11 32 53
    ridgeSupport104_rest_009 ridgeSupport104_rest_010 ridgeSupport104_rest_012
    ridgeSupport104_009 ridgeSupport104_suffix_010 ridgeSupport104_009_decode ridgeSupport104_suffix_decode_010
theorem ridgeSupport104_suffix_decode_008 : PackedRawNatGrowth.readList 11 117 ridgeSupport104_rest_008 =
    (ridgeSupport104_suffix_008, ridgeSupport104_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 11 32 85
    ridgeSupport104_rest_008 ridgeSupport104_rest_009 ridgeSupport104_rest_012
    ridgeSupport104_008 ridgeSupport104_suffix_009 ridgeSupport104_008_decode ridgeSupport104_suffix_decode_009
theorem ridgeSupport104_suffix_decode_007 : PackedRawNatGrowth.readList 11 149 ridgeSupport104_rest_007 =
    (ridgeSupport104_suffix_007, ridgeSupport104_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 11 32 117
    ridgeSupport104_rest_007 ridgeSupport104_rest_008 ridgeSupport104_rest_012
    ridgeSupport104_007 ridgeSupport104_suffix_008 ridgeSupport104_007_decode ridgeSupport104_suffix_decode_008
theorem ridgeSupport104_suffix_decode_006 : PackedRawNatGrowth.readList 11 181 ridgeSupport104_rest_006 =
    (ridgeSupport104_suffix_006, ridgeSupport104_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 11 32 149
    ridgeSupport104_rest_006 ridgeSupport104_rest_007 ridgeSupport104_rest_012
    ridgeSupport104_006 ridgeSupport104_suffix_007 ridgeSupport104_006_decode ridgeSupport104_suffix_decode_007
theorem ridgeSupport104_suffix_decode_005 : PackedRawNatGrowth.readList 11 213 ridgeSupport104_rest_005 =
    (ridgeSupport104_suffix_005, ridgeSupport104_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 11 32 181
    ridgeSupport104_rest_005 ridgeSupport104_rest_006 ridgeSupport104_rest_012
    ridgeSupport104_005 ridgeSupport104_suffix_006 ridgeSupport104_005_decode ridgeSupport104_suffix_decode_006
theorem ridgeSupport104_suffix_decode_004 : PackedRawNatGrowth.readList 11 245 ridgeSupport104_rest_004 =
    (ridgeSupport104_suffix_004, ridgeSupport104_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 11 32 213
    ridgeSupport104_rest_004 ridgeSupport104_rest_005 ridgeSupport104_rest_012
    ridgeSupport104_004 ridgeSupport104_suffix_005 ridgeSupport104_004_decode ridgeSupport104_suffix_decode_005
theorem ridgeSupport104_suffix_decode_003 : PackedRawNatGrowth.readList 11 277 ridgeSupport104_rest_003 =
    (ridgeSupport104_suffix_003, ridgeSupport104_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 11 32 245
    ridgeSupport104_rest_003 ridgeSupport104_rest_004 ridgeSupport104_rest_012
    ridgeSupport104_003 ridgeSupport104_suffix_004 ridgeSupport104_003_decode ridgeSupport104_suffix_decode_004
theorem ridgeSupport104_suffix_decode_002 : PackedRawNatGrowth.readList 11 309 ridgeSupport104_rest_002 =
    (ridgeSupport104_suffix_002, ridgeSupport104_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 11 32 277
    ridgeSupport104_rest_002 ridgeSupport104_rest_003 ridgeSupport104_rest_012
    ridgeSupport104_002 ridgeSupport104_suffix_003 ridgeSupport104_002_decode ridgeSupport104_suffix_decode_003
theorem ridgeSupport104_suffix_decode_001 : PackedRawNatGrowth.readList 11 341 ridgeSupport104_rest_001 =
    (ridgeSupport104_suffix_001, ridgeSupport104_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 11 32 309
    ridgeSupport104_rest_001 ridgeSupport104_rest_002 ridgeSupport104_rest_012
    ridgeSupport104_001 ridgeSupport104_suffix_002 ridgeSupport104_001_decode ridgeSupport104_suffix_decode_002
theorem ridgeSupport104_suffix_decode_000 : PackedRawNatGrowth.readList 11 373 ridgeSupport104_rest_000 =
    (ridgeSupport104_suffix_000, ridgeSupport104_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 11 32 341
    ridgeSupport104_rest_000 ridgeSupport104_rest_001 ridgeSupport104_rest_012
    ridgeSupport104_000 ridgeSupport104_suffix_001 ridgeSupport104_000_decode ridgeSupport104_suffix_decode_001
theorem ridgeSupport104_eq : candidateRows 104 = ridgeSupport104_suffix_000 := by
  rw [ridgeSupport104_source]
  exact congrArg Prod.fst ridgeSupport104_suffix_decode_000
theorem ridgeTest_large_104 : ridgeTest 104 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport104_eq]
    simp only [ridgeSupport104_suffix_000, ridgeSupport104_suffix_001, ridgeSupport104_suffix_002, ridgeSupport104_suffix_003, ridgeSupport104_suffix_004, ridgeSupport104_suffix_005, ridgeSupport104_suffix_006, ridgeSupport104_suffix_007, ridgeSupport104_suffix_008, ridgeSupport104_suffix_009, ridgeSupport104_suffix_010, ridgeSupport104_suffix_011, ridgeSupport104_suffix_012, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport104_000_mask, ridgeSupport104_001_mask, ridgeSupport104_002_mask, ridgeSupport104_003_mask, ridgeSupport104_004_mask, ridgeSupport104_005_mask, ridgeSupport104_006_mask, ridgeSupport104_007_mask, ridgeSupport104_008_mask, ridgeSupport104_009_mask, ridgeSupport104_010_mask, ridgeSupport104_011_mask]
    decide +kernel
  · rw [ridgeSupport104_eq]
    simp only [ridgeSupport104_suffix_000, ridgeSupport104_suffix_001, ridgeSupport104_suffix_002, ridgeSupport104_suffix_003, ridgeSupport104_suffix_004, ridgeSupport104_suffix_005, ridgeSupport104_suffix_006, ridgeSupport104_suffix_007, ridgeSupport104_suffix_008, ridgeSupport104_suffix_009, ridgeSupport104_suffix_010, ridgeSupport104_suffix_011, ridgeSupport104_suffix_012, List.all_append, List.all_nil, ridgeSupport104_000_checked, ridgeSupport104_001_checked, ridgeSupport104_002_checked, ridgeSupport104_003_checked, ridgeSupport104_004_checked, ridgeSupport104_005_checked, ridgeSupport104_006_checked, ridgeSupport104_007_checked, ridgeSupport104_008_checked, ridgeSupport104_009_checked, ridgeSupport104_010_checked, ridgeSupport104_011_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSevenTwoSix13
