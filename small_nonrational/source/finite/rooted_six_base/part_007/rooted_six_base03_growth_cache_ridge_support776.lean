module
prelude
public import RootedSixBase03GrowthCacheRidgeSupport776Part000
public import RootedSixBase03GrowthCacheRidgeSupport776Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase03
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport776_suffix_decode_011 : PackedRawNatGrowth.readList 13 0 ridgeSupport776_rest_011 =
    (ridgeSupport776_suffix_011, ridgeSupport776_rest_011) := by rfl
theorem ridgeSupport776_suffix_decode_010 : PackedRawNatGrowth.readList 13 26 ridgeSupport776_rest_010 =
    (ridgeSupport776_suffix_010, ridgeSupport776_rest_011) :=
  PackedRawNatGrowth.readList_append_of_eq 13 26 0
    ridgeSupport776_rest_010 ridgeSupport776_rest_011 ridgeSupport776_rest_011
    ridgeSupport776_010 ridgeSupport776_suffix_011 ridgeSupport776_010_decode ridgeSupport776_suffix_decode_011
theorem ridgeSupport776_suffix_decode_009 : PackedRawNatGrowth.readList 13 58 ridgeSupport776_rest_009 =
    (ridgeSupport776_suffix_009, ridgeSupport776_rest_011) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 26
    ridgeSupport776_rest_009 ridgeSupport776_rest_010 ridgeSupport776_rest_011
    ridgeSupport776_009 ridgeSupport776_suffix_010 ridgeSupport776_009_decode ridgeSupport776_suffix_decode_010
theorem ridgeSupport776_suffix_decode_008 : PackedRawNatGrowth.readList 13 90 ridgeSupport776_rest_008 =
    (ridgeSupport776_suffix_008, ridgeSupport776_rest_011) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 58
    ridgeSupport776_rest_008 ridgeSupport776_rest_009 ridgeSupport776_rest_011
    ridgeSupport776_008 ridgeSupport776_suffix_009 ridgeSupport776_008_decode ridgeSupport776_suffix_decode_009
theorem ridgeSupport776_suffix_decode_007 : PackedRawNatGrowth.readList 13 122 ridgeSupport776_rest_007 =
    (ridgeSupport776_suffix_007, ridgeSupport776_rest_011) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 90
    ridgeSupport776_rest_007 ridgeSupport776_rest_008 ridgeSupport776_rest_011
    ridgeSupport776_007 ridgeSupport776_suffix_008 ridgeSupport776_007_decode ridgeSupport776_suffix_decode_008
theorem ridgeSupport776_suffix_decode_006 : PackedRawNatGrowth.readList 13 154 ridgeSupport776_rest_006 =
    (ridgeSupport776_suffix_006, ridgeSupport776_rest_011) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 122
    ridgeSupport776_rest_006 ridgeSupport776_rest_007 ridgeSupport776_rest_011
    ridgeSupport776_006 ridgeSupport776_suffix_007 ridgeSupport776_006_decode ridgeSupport776_suffix_decode_007
theorem ridgeSupport776_suffix_decode_005 : PackedRawNatGrowth.readList 13 186 ridgeSupport776_rest_005 =
    (ridgeSupport776_suffix_005, ridgeSupport776_rest_011) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 154
    ridgeSupport776_rest_005 ridgeSupport776_rest_006 ridgeSupport776_rest_011
    ridgeSupport776_005 ridgeSupport776_suffix_006 ridgeSupport776_005_decode ridgeSupport776_suffix_decode_006
theorem ridgeSupport776_suffix_decode_004 : PackedRawNatGrowth.readList 13 218 ridgeSupport776_rest_004 =
    (ridgeSupport776_suffix_004, ridgeSupport776_rest_011) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 186
    ridgeSupport776_rest_004 ridgeSupport776_rest_005 ridgeSupport776_rest_011
    ridgeSupport776_004 ridgeSupport776_suffix_005 ridgeSupport776_004_decode ridgeSupport776_suffix_decode_005
theorem ridgeSupport776_suffix_decode_003 : PackedRawNatGrowth.readList 13 250 ridgeSupport776_rest_003 =
    (ridgeSupport776_suffix_003, ridgeSupport776_rest_011) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 218
    ridgeSupport776_rest_003 ridgeSupport776_rest_004 ridgeSupport776_rest_011
    ridgeSupport776_003 ridgeSupport776_suffix_004 ridgeSupport776_003_decode ridgeSupport776_suffix_decode_004
theorem ridgeSupport776_suffix_decode_002 : PackedRawNatGrowth.readList 13 282 ridgeSupport776_rest_002 =
    (ridgeSupport776_suffix_002, ridgeSupport776_rest_011) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 250
    ridgeSupport776_rest_002 ridgeSupport776_rest_003 ridgeSupport776_rest_011
    ridgeSupport776_002 ridgeSupport776_suffix_003 ridgeSupport776_002_decode ridgeSupport776_suffix_decode_003
theorem ridgeSupport776_suffix_decode_001 : PackedRawNatGrowth.readList 13 314 ridgeSupport776_rest_001 =
    (ridgeSupport776_suffix_001, ridgeSupport776_rest_011) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 282
    ridgeSupport776_rest_001 ridgeSupport776_rest_002 ridgeSupport776_rest_011
    ridgeSupport776_001 ridgeSupport776_suffix_002 ridgeSupport776_001_decode ridgeSupport776_suffix_decode_002
theorem ridgeSupport776_suffix_decode_000 : PackedRawNatGrowth.readList 13 346 ridgeSupport776_rest_000 =
    (ridgeSupport776_suffix_000, ridgeSupport776_rest_011) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 314
    ridgeSupport776_rest_000 ridgeSupport776_rest_001 ridgeSupport776_rest_011
    ridgeSupport776_000 ridgeSupport776_suffix_001 ridgeSupport776_000_decode ridgeSupport776_suffix_decode_001
theorem ridgeSupport776_eq : candidateSupports 776 = ridgeSupport776_suffix_000 := by
  rw [ridgeSupport776_source]
  exact congrArg Prod.fst ridgeSupport776_suffix_decode_000
theorem ridgeTest_large_776 : ridgeTest 776 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [show candidateRows 776 = ridgeSupport776_suffix_000 from ridgeSupport776_eq]
    simp only [ridgeSupport776_suffix_000, ridgeSupport776_suffix_001, ridgeSupport776_suffix_002, ridgeSupport776_suffix_003, ridgeSupport776_suffix_004, ridgeSupport776_suffix_005, ridgeSupport776_suffix_006, ridgeSupport776_suffix_007, ridgeSupport776_suffix_008, ridgeSupport776_suffix_009, ridgeSupport776_suffix_010, ridgeSupport776_suffix_011, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport776_000_mask, ridgeSupport776_001_mask, ridgeSupport776_002_mask, ridgeSupport776_003_mask, ridgeSupport776_004_mask, ridgeSupport776_005_mask, ridgeSupport776_006_mask, ridgeSupport776_007_mask, ridgeSupport776_008_mask, ridgeSupport776_009_mask, ridgeSupport776_010_mask]
    decide +kernel
  · rw [show candidateRows 776 = ridgeSupport776_suffix_000 from ridgeSupport776_eq]
    simp only [ridgeSupport776_suffix_000, ridgeSupport776_suffix_001, ridgeSupport776_suffix_002, ridgeSupport776_suffix_003, ridgeSupport776_suffix_004, ridgeSupport776_suffix_005, ridgeSupport776_suffix_006, ridgeSupport776_suffix_007, ridgeSupport776_suffix_008, ridgeSupport776_suffix_009, ridgeSupport776_suffix_010, ridgeSupport776_suffix_011, List.all_append, List.all_nil, ridgeSupport776_000_checked, ridgeSupport776_001_checked, ridgeSupport776_002_checked, ridgeSupport776_003_checked, ridgeSupport776_004_checked, ridgeSupport776_005_checked, ridgeSupport776_006_checked, ridgeSupport776_007_checked, ridgeSupport776_008_checked, ridgeSupport776_009_checked, ridgeSupport776_010_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase03
