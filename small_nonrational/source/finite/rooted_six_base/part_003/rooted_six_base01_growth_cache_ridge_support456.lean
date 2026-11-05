module
prelude
public import RootedSixBase01GrowthCacheRidgeSupport456Part000
public import RootedSixBase01GrowthCacheRidgeSupport456Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport456_suffix_decode_012 : PackedRawNatGrowth.readList 14 0 ridgeSupport456_rest_012 =
    (ridgeSupport456_suffix_012, ridgeSupport456_rest_012) := by rfl
theorem ridgeSupport456_suffix_decode_011 : PackedRawNatGrowth.readList 14 5 ridgeSupport456_rest_011 =
    (ridgeSupport456_suffix_011, ridgeSupport456_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 14 5 0
    ridgeSupport456_rest_011 ridgeSupport456_rest_012 ridgeSupport456_rest_012
    ridgeSupport456_011 ridgeSupport456_suffix_012 ridgeSupport456_011_decode ridgeSupport456_suffix_decode_012
theorem ridgeSupport456_suffix_decode_010 : PackedRawNatGrowth.readList 14 37 ridgeSupport456_rest_010 =
    (ridgeSupport456_suffix_010, ridgeSupport456_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 5
    ridgeSupport456_rest_010 ridgeSupport456_rest_011 ridgeSupport456_rest_012
    ridgeSupport456_010 ridgeSupport456_suffix_011 ridgeSupport456_010_decode ridgeSupport456_suffix_decode_011
theorem ridgeSupport456_suffix_decode_009 : PackedRawNatGrowth.readList 14 69 ridgeSupport456_rest_009 =
    (ridgeSupport456_suffix_009, ridgeSupport456_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 37
    ridgeSupport456_rest_009 ridgeSupport456_rest_010 ridgeSupport456_rest_012
    ridgeSupport456_009 ridgeSupport456_suffix_010 ridgeSupport456_009_decode ridgeSupport456_suffix_decode_010
theorem ridgeSupport456_suffix_decode_008 : PackedRawNatGrowth.readList 14 101 ridgeSupport456_rest_008 =
    (ridgeSupport456_suffix_008, ridgeSupport456_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 69
    ridgeSupport456_rest_008 ridgeSupport456_rest_009 ridgeSupport456_rest_012
    ridgeSupport456_008 ridgeSupport456_suffix_009 ridgeSupport456_008_decode ridgeSupport456_suffix_decode_009
theorem ridgeSupport456_suffix_decode_007 : PackedRawNatGrowth.readList 14 133 ridgeSupport456_rest_007 =
    (ridgeSupport456_suffix_007, ridgeSupport456_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 101
    ridgeSupport456_rest_007 ridgeSupport456_rest_008 ridgeSupport456_rest_012
    ridgeSupport456_007 ridgeSupport456_suffix_008 ridgeSupport456_007_decode ridgeSupport456_suffix_decode_008
theorem ridgeSupport456_suffix_decode_006 : PackedRawNatGrowth.readList 14 165 ridgeSupport456_rest_006 =
    (ridgeSupport456_suffix_006, ridgeSupport456_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 133
    ridgeSupport456_rest_006 ridgeSupport456_rest_007 ridgeSupport456_rest_012
    ridgeSupport456_006 ridgeSupport456_suffix_007 ridgeSupport456_006_decode ridgeSupport456_suffix_decode_007
theorem ridgeSupport456_suffix_decode_005 : PackedRawNatGrowth.readList 14 197 ridgeSupport456_rest_005 =
    (ridgeSupport456_suffix_005, ridgeSupport456_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 165
    ridgeSupport456_rest_005 ridgeSupport456_rest_006 ridgeSupport456_rest_012
    ridgeSupport456_005 ridgeSupport456_suffix_006 ridgeSupport456_005_decode ridgeSupport456_suffix_decode_006
theorem ridgeSupport456_suffix_decode_004 : PackedRawNatGrowth.readList 14 229 ridgeSupport456_rest_004 =
    (ridgeSupport456_suffix_004, ridgeSupport456_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 197
    ridgeSupport456_rest_004 ridgeSupport456_rest_005 ridgeSupport456_rest_012
    ridgeSupport456_004 ridgeSupport456_suffix_005 ridgeSupport456_004_decode ridgeSupport456_suffix_decode_005
theorem ridgeSupport456_suffix_decode_003 : PackedRawNatGrowth.readList 14 261 ridgeSupport456_rest_003 =
    (ridgeSupport456_suffix_003, ridgeSupport456_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 229
    ridgeSupport456_rest_003 ridgeSupport456_rest_004 ridgeSupport456_rest_012
    ridgeSupport456_003 ridgeSupport456_suffix_004 ridgeSupport456_003_decode ridgeSupport456_suffix_decode_004
theorem ridgeSupport456_suffix_decode_002 : PackedRawNatGrowth.readList 14 293 ridgeSupport456_rest_002 =
    (ridgeSupport456_suffix_002, ridgeSupport456_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 261
    ridgeSupport456_rest_002 ridgeSupport456_rest_003 ridgeSupport456_rest_012
    ridgeSupport456_002 ridgeSupport456_suffix_003 ridgeSupport456_002_decode ridgeSupport456_suffix_decode_003
theorem ridgeSupport456_suffix_decode_001 : PackedRawNatGrowth.readList 14 325 ridgeSupport456_rest_001 =
    (ridgeSupport456_suffix_001, ridgeSupport456_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 293
    ridgeSupport456_rest_001 ridgeSupport456_rest_002 ridgeSupport456_rest_012
    ridgeSupport456_001 ridgeSupport456_suffix_002 ridgeSupport456_001_decode ridgeSupport456_suffix_decode_002
theorem ridgeSupport456_suffix_decode_000 : PackedRawNatGrowth.readList 14 357 ridgeSupport456_rest_000 =
    (ridgeSupport456_suffix_000, ridgeSupport456_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 325
    ridgeSupport456_rest_000 ridgeSupport456_rest_001 ridgeSupport456_rest_012
    ridgeSupport456_000 ridgeSupport456_suffix_001 ridgeSupport456_000_decode ridgeSupport456_suffix_decode_001
theorem ridgeSupport456_eq : candidateRows 456 = ridgeSupport456_suffix_000 := by
  rw [ridgeSupport456_source]
  exact congrArg Prod.fst ridgeSupport456_suffix_decode_000
theorem ridgeTest_large_456 : ridgeTest 456 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport456_eq]
    simp only [ridgeSupport456_suffix_000, ridgeSupport456_suffix_001, ridgeSupport456_suffix_002, ridgeSupport456_suffix_003, ridgeSupport456_suffix_004, ridgeSupport456_suffix_005, ridgeSupport456_suffix_006, ridgeSupport456_suffix_007, ridgeSupport456_suffix_008, ridgeSupport456_suffix_009, ridgeSupport456_suffix_010, ridgeSupport456_suffix_011, ridgeSupport456_suffix_012, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport456_000_mask, ridgeSupport456_001_mask, ridgeSupport456_002_mask, ridgeSupport456_003_mask, ridgeSupport456_004_mask, ridgeSupport456_005_mask, ridgeSupport456_006_mask, ridgeSupport456_007_mask, ridgeSupport456_008_mask, ridgeSupport456_009_mask, ridgeSupport456_010_mask, ridgeSupport456_011_mask]
    decide +kernel
  · rw [ridgeSupport456_eq]
    simp only [ridgeSupport456_suffix_000, ridgeSupport456_suffix_001, ridgeSupport456_suffix_002, ridgeSupport456_suffix_003, ridgeSupport456_suffix_004, ridgeSupport456_suffix_005, ridgeSupport456_suffix_006, ridgeSupport456_suffix_007, ridgeSupport456_suffix_008, ridgeSupport456_suffix_009, ridgeSupport456_suffix_010, ridgeSupport456_suffix_011, ridgeSupport456_suffix_012, List.all_append, List.all_nil, ridgeSupport456_000_checked, ridgeSupport456_001_checked, ridgeSupport456_002_checked, ridgeSupport456_003_checked, ridgeSupport456_004_checked, ridgeSupport456_005_checked, ridgeSupport456_006_checked, ridgeSupport456_007_checked, ridgeSupport456_008_checked, ridgeSupport456_009_checked, ridgeSupport456_010_checked, ridgeSupport456_011_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase01
