module
prelude
public import RootedSixBase03GrowthCacheRidgeSupport388Part000
public import RootedSixBase03GrowthCacheRidgeSupport388Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase03
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport388_suffix_decode_011 : PackedRawNatGrowth.readList 13 0 ridgeSupport388_rest_011 =
    (ridgeSupport388_suffix_011, ridgeSupport388_rest_011) := by rfl
theorem ridgeSupport388_suffix_decode_010 : PackedRawNatGrowth.readList 13 26 ridgeSupport388_rest_010 =
    (ridgeSupport388_suffix_010, ridgeSupport388_rest_011) :=
  PackedRawNatGrowth.readList_append_of_eq 13 26 0
    ridgeSupport388_rest_010 ridgeSupport388_rest_011 ridgeSupport388_rest_011
    ridgeSupport388_010 ridgeSupport388_suffix_011 ridgeSupport388_010_decode ridgeSupport388_suffix_decode_011
theorem ridgeSupport388_suffix_decode_009 : PackedRawNatGrowth.readList 13 58 ridgeSupport388_rest_009 =
    (ridgeSupport388_suffix_009, ridgeSupport388_rest_011) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 26
    ridgeSupport388_rest_009 ridgeSupport388_rest_010 ridgeSupport388_rest_011
    ridgeSupport388_009 ridgeSupport388_suffix_010 ridgeSupport388_009_decode ridgeSupport388_suffix_decode_010
theorem ridgeSupport388_suffix_decode_008 : PackedRawNatGrowth.readList 13 90 ridgeSupport388_rest_008 =
    (ridgeSupport388_suffix_008, ridgeSupport388_rest_011) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 58
    ridgeSupport388_rest_008 ridgeSupport388_rest_009 ridgeSupport388_rest_011
    ridgeSupport388_008 ridgeSupport388_suffix_009 ridgeSupport388_008_decode ridgeSupport388_suffix_decode_009
theorem ridgeSupport388_suffix_decode_007 : PackedRawNatGrowth.readList 13 122 ridgeSupport388_rest_007 =
    (ridgeSupport388_suffix_007, ridgeSupport388_rest_011) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 90
    ridgeSupport388_rest_007 ridgeSupport388_rest_008 ridgeSupport388_rest_011
    ridgeSupport388_007 ridgeSupport388_suffix_008 ridgeSupport388_007_decode ridgeSupport388_suffix_decode_008
theorem ridgeSupport388_suffix_decode_006 : PackedRawNatGrowth.readList 13 154 ridgeSupport388_rest_006 =
    (ridgeSupport388_suffix_006, ridgeSupport388_rest_011) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 122
    ridgeSupport388_rest_006 ridgeSupport388_rest_007 ridgeSupport388_rest_011
    ridgeSupport388_006 ridgeSupport388_suffix_007 ridgeSupport388_006_decode ridgeSupport388_suffix_decode_007
theorem ridgeSupport388_suffix_decode_005 : PackedRawNatGrowth.readList 13 186 ridgeSupport388_rest_005 =
    (ridgeSupport388_suffix_005, ridgeSupport388_rest_011) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 154
    ridgeSupport388_rest_005 ridgeSupport388_rest_006 ridgeSupport388_rest_011
    ridgeSupport388_005 ridgeSupport388_suffix_006 ridgeSupport388_005_decode ridgeSupport388_suffix_decode_006
theorem ridgeSupport388_suffix_decode_004 : PackedRawNatGrowth.readList 13 218 ridgeSupport388_rest_004 =
    (ridgeSupport388_suffix_004, ridgeSupport388_rest_011) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 186
    ridgeSupport388_rest_004 ridgeSupport388_rest_005 ridgeSupport388_rest_011
    ridgeSupport388_004 ridgeSupport388_suffix_005 ridgeSupport388_004_decode ridgeSupport388_suffix_decode_005
theorem ridgeSupport388_suffix_decode_003 : PackedRawNatGrowth.readList 13 250 ridgeSupport388_rest_003 =
    (ridgeSupport388_suffix_003, ridgeSupport388_rest_011) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 218
    ridgeSupport388_rest_003 ridgeSupport388_rest_004 ridgeSupport388_rest_011
    ridgeSupport388_003 ridgeSupport388_suffix_004 ridgeSupport388_003_decode ridgeSupport388_suffix_decode_004
theorem ridgeSupport388_suffix_decode_002 : PackedRawNatGrowth.readList 13 282 ridgeSupport388_rest_002 =
    (ridgeSupport388_suffix_002, ridgeSupport388_rest_011) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 250
    ridgeSupport388_rest_002 ridgeSupport388_rest_003 ridgeSupport388_rest_011
    ridgeSupport388_002 ridgeSupport388_suffix_003 ridgeSupport388_002_decode ridgeSupport388_suffix_decode_003
theorem ridgeSupport388_suffix_decode_001 : PackedRawNatGrowth.readList 13 314 ridgeSupport388_rest_001 =
    (ridgeSupport388_suffix_001, ridgeSupport388_rest_011) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 282
    ridgeSupport388_rest_001 ridgeSupport388_rest_002 ridgeSupport388_rest_011
    ridgeSupport388_001 ridgeSupport388_suffix_002 ridgeSupport388_001_decode ridgeSupport388_suffix_decode_002
theorem ridgeSupport388_suffix_decode_000 : PackedRawNatGrowth.readList 13 346 ridgeSupport388_rest_000 =
    (ridgeSupport388_suffix_000, ridgeSupport388_rest_011) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 314
    ridgeSupport388_rest_000 ridgeSupport388_rest_001 ridgeSupport388_rest_011
    ridgeSupport388_000 ridgeSupport388_suffix_001 ridgeSupport388_000_decode ridgeSupport388_suffix_decode_001
theorem ridgeSupport388_eq : candidateSupports 388 = ridgeSupport388_suffix_000 := by
  rw [ridgeSupport388_source]
  exact congrArg Prod.fst ridgeSupport388_suffix_decode_000
theorem ridgeTest_large_388 : ridgeTest 388 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [show candidateRows 388 = ridgeSupport388_suffix_000 from ridgeSupport388_eq]
    simp only [ridgeSupport388_suffix_000, ridgeSupport388_suffix_001, ridgeSupport388_suffix_002, ridgeSupport388_suffix_003, ridgeSupport388_suffix_004, ridgeSupport388_suffix_005, ridgeSupport388_suffix_006, ridgeSupport388_suffix_007, ridgeSupport388_suffix_008, ridgeSupport388_suffix_009, ridgeSupport388_suffix_010, ridgeSupport388_suffix_011, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport388_000_mask, ridgeSupport388_001_mask, ridgeSupport388_002_mask, ridgeSupport388_003_mask, ridgeSupport388_004_mask, ridgeSupport388_005_mask, ridgeSupport388_006_mask, ridgeSupport388_007_mask, ridgeSupport388_008_mask, ridgeSupport388_009_mask, ridgeSupport388_010_mask]
    decide +kernel
  · rw [show candidateRows 388 = ridgeSupport388_suffix_000 from ridgeSupport388_eq]
    simp only [ridgeSupport388_suffix_000, ridgeSupport388_suffix_001, ridgeSupport388_suffix_002, ridgeSupport388_suffix_003, ridgeSupport388_suffix_004, ridgeSupport388_suffix_005, ridgeSupport388_suffix_006, ridgeSupport388_suffix_007, ridgeSupport388_suffix_008, ridgeSupport388_suffix_009, ridgeSupport388_suffix_010, ridgeSupport388_suffix_011, List.all_append, List.all_nil, ridgeSupport388_000_checked, ridgeSupport388_001_checked, ridgeSupport388_002_checked, ridgeSupport388_003_checked, ridgeSupport388_004_checked, ridgeSupport388_005_checked, ridgeSupport388_006_checked, ridgeSupport388_007_checked, ridgeSupport388_008_checked, ridgeSupport388_009_checked, ridgeSupport388_010_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase03
