module
prelude
public import RootedSixBase01GrowthCacheRidgeSupport904Part000
public import RootedSixBase01GrowthCacheRidgeSupport904Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport904_suffix_decode_012 : PackedRawNatGrowth.readList 14 0 ridgeSupport904_rest_012 =
    (ridgeSupport904_suffix_012, ridgeSupport904_rest_012) := by rfl
theorem ridgeSupport904_suffix_decode_011 : PackedRawNatGrowth.readList 14 5 ridgeSupport904_rest_011 =
    (ridgeSupport904_suffix_011, ridgeSupport904_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 14 5 0
    ridgeSupport904_rest_011 ridgeSupport904_rest_012 ridgeSupport904_rest_012
    ridgeSupport904_011 ridgeSupport904_suffix_012 ridgeSupport904_011_decode ridgeSupport904_suffix_decode_012
theorem ridgeSupport904_suffix_decode_010 : PackedRawNatGrowth.readList 14 37 ridgeSupport904_rest_010 =
    (ridgeSupport904_suffix_010, ridgeSupport904_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 5
    ridgeSupport904_rest_010 ridgeSupport904_rest_011 ridgeSupport904_rest_012
    ridgeSupport904_010 ridgeSupport904_suffix_011 ridgeSupport904_010_decode ridgeSupport904_suffix_decode_011
theorem ridgeSupport904_suffix_decode_009 : PackedRawNatGrowth.readList 14 69 ridgeSupport904_rest_009 =
    (ridgeSupport904_suffix_009, ridgeSupport904_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 37
    ridgeSupport904_rest_009 ridgeSupport904_rest_010 ridgeSupport904_rest_012
    ridgeSupport904_009 ridgeSupport904_suffix_010 ridgeSupport904_009_decode ridgeSupport904_suffix_decode_010
theorem ridgeSupport904_suffix_decode_008 : PackedRawNatGrowth.readList 14 101 ridgeSupport904_rest_008 =
    (ridgeSupport904_suffix_008, ridgeSupport904_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 69
    ridgeSupport904_rest_008 ridgeSupport904_rest_009 ridgeSupport904_rest_012
    ridgeSupport904_008 ridgeSupport904_suffix_009 ridgeSupport904_008_decode ridgeSupport904_suffix_decode_009
theorem ridgeSupport904_suffix_decode_007 : PackedRawNatGrowth.readList 14 133 ridgeSupport904_rest_007 =
    (ridgeSupport904_suffix_007, ridgeSupport904_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 101
    ridgeSupport904_rest_007 ridgeSupport904_rest_008 ridgeSupport904_rest_012
    ridgeSupport904_007 ridgeSupport904_suffix_008 ridgeSupport904_007_decode ridgeSupport904_suffix_decode_008
theorem ridgeSupport904_suffix_decode_006 : PackedRawNatGrowth.readList 14 165 ridgeSupport904_rest_006 =
    (ridgeSupport904_suffix_006, ridgeSupport904_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 133
    ridgeSupport904_rest_006 ridgeSupport904_rest_007 ridgeSupport904_rest_012
    ridgeSupport904_006 ridgeSupport904_suffix_007 ridgeSupport904_006_decode ridgeSupport904_suffix_decode_007
theorem ridgeSupport904_suffix_decode_005 : PackedRawNatGrowth.readList 14 197 ridgeSupport904_rest_005 =
    (ridgeSupport904_suffix_005, ridgeSupport904_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 165
    ridgeSupport904_rest_005 ridgeSupport904_rest_006 ridgeSupport904_rest_012
    ridgeSupport904_005 ridgeSupport904_suffix_006 ridgeSupport904_005_decode ridgeSupport904_suffix_decode_006
theorem ridgeSupport904_suffix_decode_004 : PackedRawNatGrowth.readList 14 229 ridgeSupport904_rest_004 =
    (ridgeSupport904_suffix_004, ridgeSupport904_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 197
    ridgeSupport904_rest_004 ridgeSupport904_rest_005 ridgeSupport904_rest_012
    ridgeSupport904_004 ridgeSupport904_suffix_005 ridgeSupport904_004_decode ridgeSupport904_suffix_decode_005
theorem ridgeSupport904_suffix_decode_003 : PackedRawNatGrowth.readList 14 261 ridgeSupport904_rest_003 =
    (ridgeSupport904_suffix_003, ridgeSupport904_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 229
    ridgeSupport904_rest_003 ridgeSupport904_rest_004 ridgeSupport904_rest_012
    ridgeSupport904_003 ridgeSupport904_suffix_004 ridgeSupport904_003_decode ridgeSupport904_suffix_decode_004
theorem ridgeSupport904_suffix_decode_002 : PackedRawNatGrowth.readList 14 293 ridgeSupport904_rest_002 =
    (ridgeSupport904_suffix_002, ridgeSupport904_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 261
    ridgeSupport904_rest_002 ridgeSupport904_rest_003 ridgeSupport904_rest_012
    ridgeSupport904_002 ridgeSupport904_suffix_003 ridgeSupport904_002_decode ridgeSupport904_suffix_decode_003
theorem ridgeSupport904_suffix_decode_001 : PackedRawNatGrowth.readList 14 325 ridgeSupport904_rest_001 =
    (ridgeSupport904_suffix_001, ridgeSupport904_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 293
    ridgeSupport904_rest_001 ridgeSupport904_rest_002 ridgeSupport904_rest_012
    ridgeSupport904_001 ridgeSupport904_suffix_002 ridgeSupport904_001_decode ridgeSupport904_suffix_decode_002
theorem ridgeSupport904_suffix_decode_000 : PackedRawNatGrowth.readList 14 357 ridgeSupport904_rest_000 =
    (ridgeSupport904_suffix_000, ridgeSupport904_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 325
    ridgeSupport904_rest_000 ridgeSupport904_rest_001 ridgeSupport904_rest_012
    ridgeSupport904_000 ridgeSupport904_suffix_001 ridgeSupport904_000_decode ridgeSupport904_suffix_decode_001
theorem ridgeSupport904_eq : candidateRows 904 = ridgeSupport904_suffix_000 := by
  rw [ridgeSupport904_source]
  exact congrArg Prod.fst ridgeSupport904_suffix_decode_000
theorem ridgeTest_large_904 : ridgeTest 904 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport904_eq]
    simp only [ridgeSupport904_suffix_000, ridgeSupport904_suffix_001, ridgeSupport904_suffix_002, ridgeSupport904_suffix_003, ridgeSupport904_suffix_004, ridgeSupport904_suffix_005, ridgeSupport904_suffix_006, ridgeSupport904_suffix_007, ridgeSupport904_suffix_008, ridgeSupport904_suffix_009, ridgeSupport904_suffix_010, ridgeSupport904_suffix_011, ridgeSupport904_suffix_012, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport904_000_mask, ridgeSupport904_001_mask, ridgeSupport904_002_mask, ridgeSupport904_003_mask, ridgeSupport904_004_mask, ridgeSupport904_005_mask, ridgeSupport904_006_mask, ridgeSupport904_007_mask, ridgeSupport904_008_mask, ridgeSupport904_009_mask, ridgeSupport904_010_mask, ridgeSupport904_011_mask]
    decide +kernel
  · rw [ridgeSupport904_eq]
    simp only [ridgeSupport904_suffix_000, ridgeSupport904_suffix_001, ridgeSupport904_suffix_002, ridgeSupport904_suffix_003, ridgeSupport904_suffix_004, ridgeSupport904_suffix_005, ridgeSupport904_suffix_006, ridgeSupport904_suffix_007, ridgeSupport904_suffix_008, ridgeSupport904_suffix_009, ridgeSupport904_suffix_010, ridgeSupport904_suffix_011, ridgeSupport904_suffix_012, List.all_append, List.all_nil, ridgeSupport904_000_checked, ridgeSupport904_001_checked, ridgeSupport904_002_checked, ridgeSupport904_003_checked, ridgeSupport904_004_checked, ridgeSupport904_005_checked, ridgeSupport904_006_checked, ridgeSupport904_007_checked, ridgeSupport904_008_checked, ridgeSupport904_009_checked, ridgeSupport904_010_checked, ridgeSupport904_011_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase01
