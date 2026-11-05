module
prelude
public import RootedSixBase03GrowthCacheRidgeSupport578Part000
public import RootedSixBase03GrowthCacheRidgeSupport578Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase03
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport578_suffix_decode_012 : PackedRawNatGrowth.readList 13 0 ridgeSupport578_rest_012 =
    (ridgeSupport578_suffix_012, ridgeSupport578_rest_012) := by rfl
theorem ridgeSupport578_suffix_decode_011 : PackedRawNatGrowth.readList 13 26 ridgeSupport578_rest_011 =
    (ridgeSupport578_suffix_011, ridgeSupport578_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 13 26 0
    ridgeSupport578_rest_011 ridgeSupport578_rest_012 ridgeSupport578_rest_012
    ridgeSupport578_011 ridgeSupport578_suffix_012 ridgeSupport578_011_decode ridgeSupport578_suffix_decode_012
theorem ridgeSupport578_suffix_decode_010 : PackedRawNatGrowth.readList 13 58 ridgeSupport578_rest_010 =
    (ridgeSupport578_suffix_010, ridgeSupport578_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 26
    ridgeSupport578_rest_010 ridgeSupport578_rest_011 ridgeSupport578_rest_012
    ridgeSupport578_010 ridgeSupport578_suffix_011 ridgeSupport578_010_decode ridgeSupport578_suffix_decode_011
theorem ridgeSupport578_suffix_decode_009 : PackedRawNatGrowth.readList 13 90 ridgeSupport578_rest_009 =
    (ridgeSupport578_suffix_009, ridgeSupport578_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 58
    ridgeSupport578_rest_009 ridgeSupport578_rest_010 ridgeSupport578_rest_012
    ridgeSupport578_009 ridgeSupport578_suffix_010 ridgeSupport578_009_decode ridgeSupport578_suffix_decode_010
theorem ridgeSupport578_suffix_decode_008 : PackedRawNatGrowth.readList 13 122 ridgeSupport578_rest_008 =
    (ridgeSupport578_suffix_008, ridgeSupport578_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 90
    ridgeSupport578_rest_008 ridgeSupport578_rest_009 ridgeSupport578_rest_012
    ridgeSupport578_008 ridgeSupport578_suffix_009 ridgeSupport578_008_decode ridgeSupport578_suffix_decode_009
theorem ridgeSupport578_suffix_decode_007 : PackedRawNatGrowth.readList 13 154 ridgeSupport578_rest_007 =
    (ridgeSupport578_suffix_007, ridgeSupport578_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 122
    ridgeSupport578_rest_007 ridgeSupport578_rest_008 ridgeSupport578_rest_012
    ridgeSupport578_007 ridgeSupport578_suffix_008 ridgeSupport578_007_decode ridgeSupport578_suffix_decode_008
theorem ridgeSupport578_suffix_decode_006 : PackedRawNatGrowth.readList 13 186 ridgeSupport578_rest_006 =
    (ridgeSupport578_suffix_006, ridgeSupport578_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 154
    ridgeSupport578_rest_006 ridgeSupport578_rest_007 ridgeSupport578_rest_012
    ridgeSupport578_006 ridgeSupport578_suffix_007 ridgeSupport578_006_decode ridgeSupport578_suffix_decode_007
theorem ridgeSupport578_suffix_decode_005 : PackedRawNatGrowth.readList 13 218 ridgeSupport578_rest_005 =
    (ridgeSupport578_suffix_005, ridgeSupport578_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 186
    ridgeSupport578_rest_005 ridgeSupport578_rest_006 ridgeSupport578_rest_012
    ridgeSupport578_005 ridgeSupport578_suffix_006 ridgeSupport578_005_decode ridgeSupport578_suffix_decode_006
theorem ridgeSupport578_suffix_decode_004 : PackedRawNatGrowth.readList 13 250 ridgeSupport578_rest_004 =
    (ridgeSupport578_suffix_004, ridgeSupport578_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 218
    ridgeSupport578_rest_004 ridgeSupport578_rest_005 ridgeSupport578_rest_012
    ridgeSupport578_004 ridgeSupport578_suffix_005 ridgeSupport578_004_decode ridgeSupport578_suffix_decode_005
theorem ridgeSupport578_suffix_decode_003 : PackedRawNatGrowth.readList 13 282 ridgeSupport578_rest_003 =
    (ridgeSupport578_suffix_003, ridgeSupport578_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 250
    ridgeSupport578_rest_003 ridgeSupport578_rest_004 ridgeSupport578_rest_012
    ridgeSupport578_003 ridgeSupport578_suffix_004 ridgeSupport578_003_decode ridgeSupport578_suffix_decode_004
theorem ridgeSupport578_suffix_decode_002 : PackedRawNatGrowth.readList 13 314 ridgeSupport578_rest_002 =
    (ridgeSupport578_suffix_002, ridgeSupport578_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 282
    ridgeSupport578_rest_002 ridgeSupport578_rest_003 ridgeSupport578_rest_012
    ridgeSupport578_002 ridgeSupport578_suffix_003 ridgeSupport578_002_decode ridgeSupport578_suffix_decode_003
theorem ridgeSupport578_suffix_decode_001 : PackedRawNatGrowth.readList 13 346 ridgeSupport578_rest_001 =
    (ridgeSupport578_suffix_001, ridgeSupport578_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 314
    ridgeSupport578_rest_001 ridgeSupport578_rest_002 ridgeSupport578_rest_012
    ridgeSupport578_001 ridgeSupport578_suffix_002 ridgeSupport578_001_decode ridgeSupport578_suffix_decode_002
theorem ridgeSupport578_suffix_decode_000 : PackedRawNatGrowth.readList 13 378 ridgeSupport578_rest_000 =
    (ridgeSupport578_suffix_000, ridgeSupport578_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 346
    ridgeSupport578_rest_000 ridgeSupport578_rest_001 ridgeSupport578_rest_012
    ridgeSupport578_000 ridgeSupport578_suffix_001 ridgeSupport578_000_decode ridgeSupport578_suffix_decode_001
theorem ridgeSupport578_eq : candidateSupports 578 = ridgeSupport578_suffix_000 := by
  rw [ridgeSupport578_source]
  exact congrArg Prod.fst ridgeSupport578_suffix_decode_000
theorem ridgeTest_large_578 : ridgeTest 578 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [show candidateRows 578 = ridgeSupport578_suffix_000 from ridgeSupport578_eq]
    simp only [ridgeSupport578_suffix_000, ridgeSupport578_suffix_001, ridgeSupport578_suffix_002, ridgeSupport578_suffix_003, ridgeSupport578_suffix_004, ridgeSupport578_suffix_005, ridgeSupport578_suffix_006, ridgeSupport578_suffix_007, ridgeSupport578_suffix_008, ridgeSupport578_suffix_009, ridgeSupport578_suffix_010, ridgeSupport578_suffix_011, ridgeSupport578_suffix_012, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport578_000_mask, ridgeSupport578_001_mask, ridgeSupport578_002_mask, ridgeSupport578_003_mask, ridgeSupport578_004_mask, ridgeSupport578_005_mask, ridgeSupport578_006_mask, ridgeSupport578_007_mask, ridgeSupport578_008_mask, ridgeSupport578_009_mask, ridgeSupport578_010_mask, ridgeSupport578_011_mask]
    decide +kernel
  · rw [show candidateRows 578 = ridgeSupport578_suffix_000 from ridgeSupport578_eq]
    simp only [ridgeSupport578_suffix_000, ridgeSupport578_suffix_001, ridgeSupport578_suffix_002, ridgeSupport578_suffix_003, ridgeSupport578_suffix_004, ridgeSupport578_suffix_005, ridgeSupport578_suffix_006, ridgeSupport578_suffix_007, ridgeSupport578_suffix_008, ridgeSupport578_suffix_009, ridgeSupport578_suffix_010, ridgeSupport578_suffix_011, ridgeSupport578_suffix_012, List.all_append, List.all_nil, ridgeSupport578_000_checked, ridgeSupport578_001_checked, ridgeSupport578_002_checked, ridgeSupport578_003_checked, ridgeSupport578_004_checked, ridgeSupport578_005_checked, ridgeSupport578_006_checked, ridgeSupport578_007_checked, ridgeSupport578_008_checked, ridgeSupport578_009_checked, ridgeSupport578_010_checked, ridgeSupport578_011_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase03
