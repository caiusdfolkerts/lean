module
prelude
public import RootedSixBase01GrowthCacheRidgeSupport706Part000
public import RootedSixBase01GrowthCacheRidgeSupport706Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport706_suffix_decode_012 : PackedRawNatGrowth.readList 14 0 ridgeSupport706_rest_012 =
    (ridgeSupport706_suffix_012, ridgeSupport706_rest_012) := by rfl
theorem ridgeSupport706_suffix_decode_011 : PackedRawNatGrowth.readList 14 5 ridgeSupport706_rest_011 =
    (ridgeSupport706_suffix_011, ridgeSupport706_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 14 5 0
    ridgeSupport706_rest_011 ridgeSupport706_rest_012 ridgeSupport706_rest_012
    ridgeSupport706_011 ridgeSupport706_suffix_012 ridgeSupport706_011_decode ridgeSupport706_suffix_decode_012
theorem ridgeSupport706_suffix_decode_010 : PackedRawNatGrowth.readList 14 37 ridgeSupport706_rest_010 =
    (ridgeSupport706_suffix_010, ridgeSupport706_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 5
    ridgeSupport706_rest_010 ridgeSupport706_rest_011 ridgeSupport706_rest_012
    ridgeSupport706_010 ridgeSupport706_suffix_011 ridgeSupport706_010_decode ridgeSupport706_suffix_decode_011
theorem ridgeSupport706_suffix_decode_009 : PackedRawNatGrowth.readList 14 69 ridgeSupport706_rest_009 =
    (ridgeSupport706_suffix_009, ridgeSupport706_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 37
    ridgeSupport706_rest_009 ridgeSupport706_rest_010 ridgeSupport706_rest_012
    ridgeSupport706_009 ridgeSupport706_suffix_010 ridgeSupport706_009_decode ridgeSupport706_suffix_decode_010
theorem ridgeSupport706_suffix_decode_008 : PackedRawNatGrowth.readList 14 101 ridgeSupport706_rest_008 =
    (ridgeSupport706_suffix_008, ridgeSupport706_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 69
    ridgeSupport706_rest_008 ridgeSupport706_rest_009 ridgeSupport706_rest_012
    ridgeSupport706_008 ridgeSupport706_suffix_009 ridgeSupport706_008_decode ridgeSupport706_suffix_decode_009
theorem ridgeSupport706_suffix_decode_007 : PackedRawNatGrowth.readList 14 133 ridgeSupport706_rest_007 =
    (ridgeSupport706_suffix_007, ridgeSupport706_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 101
    ridgeSupport706_rest_007 ridgeSupport706_rest_008 ridgeSupport706_rest_012
    ridgeSupport706_007 ridgeSupport706_suffix_008 ridgeSupport706_007_decode ridgeSupport706_suffix_decode_008
theorem ridgeSupport706_suffix_decode_006 : PackedRawNatGrowth.readList 14 165 ridgeSupport706_rest_006 =
    (ridgeSupport706_suffix_006, ridgeSupport706_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 133
    ridgeSupport706_rest_006 ridgeSupport706_rest_007 ridgeSupport706_rest_012
    ridgeSupport706_006 ridgeSupport706_suffix_007 ridgeSupport706_006_decode ridgeSupport706_suffix_decode_007
theorem ridgeSupport706_suffix_decode_005 : PackedRawNatGrowth.readList 14 197 ridgeSupport706_rest_005 =
    (ridgeSupport706_suffix_005, ridgeSupport706_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 165
    ridgeSupport706_rest_005 ridgeSupport706_rest_006 ridgeSupport706_rest_012
    ridgeSupport706_005 ridgeSupport706_suffix_006 ridgeSupport706_005_decode ridgeSupport706_suffix_decode_006
theorem ridgeSupport706_suffix_decode_004 : PackedRawNatGrowth.readList 14 229 ridgeSupport706_rest_004 =
    (ridgeSupport706_suffix_004, ridgeSupport706_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 197
    ridgeSupport706_rest_004 ridgeSupport706_rest_005 ridgeSupport706_rest_012
    ridgeSupport706_004 ridgeSupport706_suffix_005 ridgeSupport706_004_decode ridgeSupport706_suffix_decode_005
theorem ridgeSupport706_suffix_decode_003 : PackedRawNatGrowth.readList 14 261 ridgeSupport706_rest_003 =
    (ridgeSupport706_suffix_003, ridgeSupport706_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 229
    ridgeSupport706_rest_003 ridgeSupport706_rest_004 ridgeSupport706_rest_012
    ridgeSupport706_003 ridgeSupport706_suffix_004 ridgeSupport706_003_decode ridgeSupport706_suffix_decode_004
theorem ridgeSupport706_suffix_decode_002 : PackedRawNatGrowth.readList 14 293 ridgeSupport706_rest_002 =
    (ridgeSupport706_suffix_002, ridgeSupport706_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 261
    ridgeSupport706_rest_002 ridgeSupport706_rest_003 ridgeSupport706_rest_012
    ridgeSupport706_002 ridgeSupport706_suffix_003 ridgeSupport706_002_decode ridgeSupport706_suffix_decode_003
theorem ridgeSupport706_suffix_decode_001 : PackedRawNatGrowth.readList 14 325 ridgeSupport706_rest_001 =
    (ridgeSupport706_suffix_001, ridgeSupport706_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 293
    ridgeSupport706_rest_001 ridgeSupport706_rest_002 ridgeSupport706_rest_012
    ridgeSupport706_001 ridgeSupport706_suffix_002 ridgeSupport706_001_decode ridgeSupport706_suffix_decode_002
theorem ridgeSupport706_suffix_decode_000 : PackedRawNatGrowth.readList 14 357 ridgeSupport706_rest_000 =
    (ridgeSupport706_suffix_000, ridgeSupport706_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 325
    ridgeSupport706_rest_000 ridgeSupport706_rest_001 ridgeSupport706_rest_012
    ridgeSupport706_000 ridgeSupport706_suffix_001 ridgeSupport706_000_decode ridgeSupport706_suffix_decode_001
theorem ridgeSupport706_eq : candidateRows 706 = ridgeSupport706_suffix_000 := by
  rw [ridgeSupport706_source]
  exact congrArg Prod.fst ridgeSupport706_suffix_decode_000
theorem ridgeTest_large_706 : ridgeTest 706 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport706_eq]
    simp only [ridgeSupport706_suffix_000, ridgeSupport706_suffix_001, ridgeSupport706_suffix_002, ridgeSupport706_suffix_003, ridgeSupport706_suffix_004, ridgeSupport706_suffix_005, ridgeSupport706_suffix_006, ridgeSupport706_suffix_007, ridgeSupport706_suffix_008, ridgeSupport706_suffix_009, ridgeSupport706_suffix_010, ridgeSupport706_suffix_011, ridgeSupport706_suffix_012, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport706_000_mask, ridgeSupport706_001_mask, ridgeSupport706_002_mask, ridgeSupport706_003_mask, ridgeSupport706_004_mask, ridgeSupport706_005_mask, ridgeSupport706_006_mask, ridgeSupport706_007_mask, ridgeSupport706_008_mask, ridgeSupport706_009_mask, ridgeSupport706_010_mask, ridgeSupport706_011_mask]
    decide +kernel
  · rw [ridgeSupport706_eq]
    simp only [ridgeSupport706_suffix_000, ridgeSupport706_suffix_001, ridgeSupport706_suffix_002, ridgeSupport706_suffix_003, ridgeSupport706_suffix_004, ridgeSupport706_suffix_005, ridgeSupport706_suffix_006, ridgeSupport706_suffix_007, ridgeSupport706_suffix_008, ridgeSupport706_suffix_009, ridgeSupport706_suffix_010, ridgeSupport706_suffix_011, ridgeSupport706_suffix_012, List.all_append, List.all_nil, ridgeSupport706_000_checked, ridgeSupport706_001_checked, ridgeSupport706_002_checked, ridgeSupport706_003_checked, ridgeSupport706_004_checked, ridgeSupport706_005_checked, ridgeSupport706_006_checked, ridgeSupport706_007_checked, ridgeSupport706_008_checked, ridgeSupport706_009_checked, ridgeSupport706_010_checked, ridgeSupport706_011_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase01
