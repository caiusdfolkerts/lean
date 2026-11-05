module
prelude
public import RootedSixBase03GrowthCacheRidgeSupport322Part000
public import RootedSixBase03GrowthCacheRidgeSupport322Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase03
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport322_suffix_decode_012 : PackedRawNatGrowth.readList 13 0 ridgeSupport322_rest_012 =
    (ridgeSupport322_suffix_012, ridgeSupport322_rest_012) := by rfl
theorem ridgeSupport322_suffix_decode_011 : PackedRawNatGrowth.readList 13 26 ridgeSupport322_rest_011 =
    (ridgeSupport322_suffix_011, ridgeSupport322_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 13 26 0
    ridgeSupport322_rest_011 ridgeSupport322_rest_012 ridgeSupport322_rest_012
    ridgeSupport322_011 ridgeSupport322_suffix_012 ridgeSupport322_011_decode ridgeSupport322_suffix_decode_012
theorem ridgeSupport322_suffix_decode_010 : PackedRawNatGrowth.readList 13 58 ridgeSupport322_rest_010 =
    (ridgeSupport322_suffix_010, ridgeSupport322_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 26
    ridgeSupport322_rest_010 ridgeSupport322_rest_011 ridgeSupport322_rest_012
    ridgeSupport322_010 ridgeSupport322_suffix_011 ridgeSupport322_010_decode ridgeSupport322_suffix_decode_011
theorem ridgeSupport322_suffix_decode_009 : PackedRawNatGrowth.readList 13 90 ridgeSupport322_rest_009 =
    (ridgeSupport322_suffix_009, ridgeSupport322_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 58
    ridgeSupport322_rest_009 ridgeSupport322_rest_010 ridgeSupport322_rest_012
    ridgeSupport322_009 ridgeSupport322_suffix_010 ridgeSupport322_009_decode ridgeSupport322_suffix_decode_010
theorem ridgeSupport322_suffix_decode_008 : PackedRawNatGrowth.readList 13 122 ridgeSupport322_rest_008 =
    (ridgeSupport322_suffix_008, ridgeSupport322_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 90
    ridgeSupport322_rest_008 ridgeSupport322_rest_009 ridgeSupport322_rest_012
    ridgeSupport322_008 ridgeSupport322_suffix_009 ridgeSupport322_008_decode ridgeSupport322_suffix_decode_009
theorem ridgeSupport322_suffix_decode_007 : PackedRawNatGrowth.readList 13 154 ridgeSupport322_rest_007 =
    (ridgeSupport322_suffix_007, ridgeSupport322_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 122
    ridgeSupport322_rest_007 ridgeSupport322_rest_008 ridgeSupport322_rest_012
    ridgeSupport322_007 ridgeSupport322_suffix_008 ridgeSupport322_007_decode ridgeSupport322_suffix_decode_008
theorem ridgeSupport322_suffix_decode_006 : PackedRawNatGrowth.readList 13 186 ridgeSupport322_rest_006 =
    (ridgeSupport322_suffix_006, ridgeSupport322_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 154
    ridgeSupport322_rest_006 ridgeSupport322_rest_007 ridgeSupport322_rest_012
    ridgeSupport322_006 ridgeSupport322_suffix_007 ridgeSupport322_006_decode ridgeSupport322_suffix_decode_007
theorem ridgeSupport322_suffix_decode_005 : PackedRawNatGrowth.readList 13 218 ridgeSupport322_rest_005 =
    (ridgeSupport322_suffix_005, ridgeSupport322_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 186
    ridgeSupport322_rest_005 ridgeSupport322_rest_006 ridgeSupport322_rest_012
    ridgeSupport322_005 ridgeSupport322_suffix_006 ridgeSupport322_005_decode ridgeSupport322_suffix_decode_006
theorem ridgeSupport322_suffix_decode_004 : PackedRawNatGrowth.readList 13 250 ridgeSupport322_rest_004 =
    (ridgeSupport322_suffix_004, ridgeSupport322_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 218
    ridgeSupport322_rest_004 ridgeSupport322_rest_005 ridgeSupport322_rest_012
    ridgeSupport322_004 ridgeSupport322_suffix_005 ridgeSupport322_004_decode ridgeSupport322_suffix_decode_005
theorem ridgeSupport322_suffix_decode_003 : PackedRawNatGrowth.readList 13 282 ridgeSupport322_rest_003 =
    (ridgeSupport322_suffix_003, ridgeSupport322_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 250
    ridgeSupport322_rest_003 ridgeSupport322_rest_004 ridgeSupport322_rest_012
    ridgeSupport322_003 ridgeSupport322_suffix_004 ridgeSupport322_003_decode ridgeSupport322_suffix_decode_004
theorem ridgeSupport322_suffix_decode_002 : PackedRawNatGrowth.readList 13 314 ridgeSupport322_rest_002 =
    (ridgeSupport322_suffix_002, ridgeSupport322_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 282
    ridgeSupport322_rest_002 ridgeSupport322_rest_003 ridgeSupport322_rest_012
    ridgeSupport322_002 ridgeSupport322_suffix_003 ridgeSupport322_002_decode ridgeSupport322_suffix_decode_003
theorem ridgeSupport322_suffix_decode_001 : PackedRawNatGrowth.readList 13 346 ridgeSupport322_rest_001 =
    (ridgeSupport322_suffix_001, ridgeSupport322_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 314
    ridgeSupport322_rest_001 ridgeSupport322_rest_002 ridgeSupport322_rest_012
    ridgeSupport322_001 ridgeSupport322_suffix_002 ridgeSupport322_001_decode ridgeSupport322_suffix_decode_002
theorem ridgeSupport322_suffix_decode_000 : PackedRawNatGrowth.readList 13 378 ridgeSupport322_rest_000 =
    (ridgeSupport322_suffix_000, ridgeSupport322_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 346
    ridgeSupport322_rest_000 ridgeSupport322_rest_001 ridgeSupport322_rest_012
    ridgeSupport322_000 ridgeSupport322_suffix_001 ridgeSupport322_000_decode ridgeSupport322_suffix_decode_001
theorem ridgeSupport322_eq : candidateSupports 322 = ridgeSupport322_suffix_000 := by
  rw [ridgeSupport322_source]
  exact congrArg Prod.fst ridgeSupport322_suffix_decode_000
theorem ridgeTest_large_322 : ridgeTest 322 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [show candidateRows 322 = ridgeSupport322_suffix_000 from ridgeSupport322_eq]
    simp only [ridgeSupport322_suffix_000, ridgeSupport322_suffix_001, ridgeSupport322_suffix_002, ridgeSupport322_suffix_003, ridgeSupport322_suffix_004, ridgeSupport322_suffix_005, ridgeSupport322_suffix_006, ridgeSupport322_suffix_007, ridgeSupport322_suffix_008, ridgeSupport322_suffix_009, ridgeSupport322_suffix_010, ridgeSupport322_suffix_011, ridgeSupport322_suffix_012, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport322_000_mask, ridgeSupport322_001_mask, ridgeSupport322_002_mask, ridgeSupport322_003_mask, ridgeSupport322_004_mask, ridgeSupport322_005_mask, ridgeSupport322_006_mask, ridgeSupport322_007_mask, ridgeSupport322_008_mask, ridgeSupport322_009_mask, ridgeSupport322_010_mask, ridgeSupport322_011_mask]
    decide +kernel
  · rw [show candidateRows 322 = ridgeSupport322_suffix_000 from ridgeSupport322_eq]
    simp only [ridgeSupport322_suffix_000, ridgeSupport322_suffix_001, ridgeSupport322_suffix_002, ridgeSupport322_suffix_003, ridgeSupport322_suffix_004, ridgeSupport322_suffix_005, ridgeSupport322_suffix_006, ridgeSupport322_suffix_007, ridgeSupport322_suffix_008, ridgeSupport322_suffix_009, ridgeSupport322_suffix_010, ridgeSupport322_suffix_011, ridgeSupport322_suffix_012, List.all_append, List.all_nil, ridgeSupport322_000_checked, ridgeSupport322_001_checked, ridgeSupport322_002_checked, ridgeSupport322_003_checked, ridgeSupport322_004_checked, ridgeSupport322_005_checked, ridgeSupport322_006_checked, ridgeSupport322_007_checked, ridgeSupport322_008_checked, ridgeSupport322_009_checked, ridgeSupport322_010_checked, ridgeSupport322_011_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase03
