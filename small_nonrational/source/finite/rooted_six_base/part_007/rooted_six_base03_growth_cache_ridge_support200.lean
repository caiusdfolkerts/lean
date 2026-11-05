module
prelude
public import RootedSixBase03GrowthCacheRidgeSupport200Part000
public import RootedSixBase03GrowthCacheRidgeSupport200Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase03
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport200_suffix_decode_011 : PackedRawNatGrowth.readList 13 0 ridgeSupport200_rest_011 =
    (ridgeSupport200_suffix_011, ridgeSupport200_rest_011) := by rfl
theorem ridgeSupport200_suffix_decode_010 : PackedRawNatGrowth.readList 13 26 ridgeSupport200_rest_010 =
    (ridgeSupport200_suffix_010, ridgeSupport200_rest_011) :=
  PackedRawNatGrowth.readList_append_of_eq 13 26 0
    ridgeSupport200_rest_010 ridgeSupport200_rest_011 ridgeSupport200_rest_011
    ridgeSupport200_010 ridgeSupport200_suffix_011 ridgeSupport200_010_decode ridgeSupport200_suffix_decode_011
theorem ridgeSupport200_suffix_decode_009 : PackedRawNatGrowth.readList 13 58 ridgeSupport200_rest_009 =
    (ridgeSupport200_suffix_009, ridgeSupport200_rest_011) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 26
    ridgeSupport200_rest_009 ridgeSupport200_rest_010 ridgeSupport200_rest_011
    ridgeSupport200_009 ridgeSupport200_suffix_010 ridgeSupport200_009_decode ridgeSupport200_suffix_decode_010
theorem ridgeSupport200_suffix_decode_008 : PackedRawNatGrowth.readList 13 90 ridgeSupport200_rest_008 =
    (ridgeSupport200_suffix_008, ridgeSupport200_rest_011) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 58
    ridgeSupport200_rest_008 ridgeSupport200_rest_009 ridgeSupport200_rest_011
    ridgeSupport200_008 ridgeSupport200_suffix_009 ridgeSupport200_008_decode ridgeSupport200_suffix_decode_009
theorem ridgeSupport200_suffix_decode_007 : PackedRawNatGrowth.readList 13 122 ridgeSupport200_rest_007 =
    (ridgeSupport200_suffix_007, ridgeSupport200_rest_011) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 90
    ridgeSupport200_rest_007 ridgeSupport200_rest_008 ridgeSupport200_rest_011
    ridgeSupport200_007 ridgeSupport200_suffix_008 ridgeSupport200_007_decode ridgeSupport200_suffix_decode_008
theorem ridgeSupport200_suffix_decode_006 : PackedRawNatGrowth.readList 13 154 ridgeSupport200_rest_006 =
    (ridgeSupport200_suffix_006, ridgeSupport200_rest_011) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 122
    ridgeSupport200_rest_006 ridgeSupport200_rest_007 ridgeSupport200_rest_011
    ridgeSupport200_006 ridgeSupport200_suffix_007 ridgeSupport200_006_decode ridgeSupport200_suffix_decode_007
theorem ridgeSupport200_suffix_decode_005 : PackedRawNatGrowth.readList 13 186 ridgeSupport200_rest_005 =
    (ridgeSupport200_suffix_005, ridgeSupport200_rest_011) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 154
    ridgeSupport200_rest_005 ridgeSupport200_rest_006 ridgeSupport200_rest_011
    ridgeSupport200_005 ridgeSupport200_suffix_006 ridgeSupport200_005_decode ridgeSupport200_suffix_decode_006
theorem ridgeSupport200_suffix_decode_004 : PackedRawNatGrowth.readList 13 218 ridgeSupport200_rest_004 =
    (ridgeSupport200_suffix_004, ridgeSupport200_rest_011) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 186
    ridgeSupport200_rest_004 ridgeSupport200_rest_005 ridgeSupport200_rest_011
    ridgeSupport200_004 ridgeSupport200_suffix_005 ridgeSupport200_004_decode ridgeSupport200_suffix_decode_005
theorem ridgeSupport200_suffix_decode_003 : PackedRawNatGrowth.readList 13 250 ridgeSupport200_rest_003 =
    (ridgeSupport200_suffix_003, ridgeSupport200_rest_011) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 218
    ridgeSupport200_rest_003 ridgeSupport200_rest_004 ridgeSupport200_rest_011
    ridgeSupport200_003 ridgeSupport200_suffix_004 ridgeSupport200_003_decode ridgeSupport200_suffix_decode_004
theorem ridgeSupport200_suffix_decode_002 : PackedRawNatGrowth.readList 13 282 ridgeSupport200_rest_002 =
    (ridgeSupport200_suffix_002, ridgeSupport200_rest_011) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 250
    ridgeSupport200_rest_002 ridgeSupport200_rest_003 ridgeSupport200_rest_011
    ridgeSupport200_002 ridgeSupport200_suffix_003 ridgeSupport200_002_decode ridgeSupport200_suffix_decode_003
theorem ridgeSupport200_suffix_decode_001 : PackedRawNatGrowth.readList 13 314 ridgeSupport200_rest_001 =
    (ridgeSupport200_suffix_001, ridgeSupport200_rest_011) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 282
    ridgeSupport200_rest_001 ridgeSupport200_rest_002 ridgeSupport200_rest_011
    ridgeSupport200_001 ridgeSupport200_suffix_002 ridgeSupport200_001_decode ridgeSupport200_suffix_decode_002
theorem ridgeSupport200_suffix_decode_000 : PackedRawNatGrowth.readList 13 346 ridgeSupport200_rest_000 =
    (ridgeSupport200_suffix_000, ridgeSupport200_rest_011) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 314
    ridgeSupport200_rest_000 ridgeSupport200_rest_001 ridgeSupport200_rest_011
    ridgeSupport200_000 ridgeSupport200_suffix_001 ridgeSupport200_000_decode ridgeSupport200_suffix_decode_001
theorem ridgeSupport200_eq : candidateSupports 200 = ridgeSupport200_suffix_000 := by
  rw [ridgeSupport200_source]
  exact congrArg Prod.fst ridgeSupport200_suffix_decode_000
theorem ridgeTest_large_200 : ridgeTest 200 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [show candidateRows 200 = ridgeSupport200_suffix_000 from ridgeSupport200_eq]
    simp only [ridgeSupport200_suffix_000, ridgeSupport200_suffix_001, ridgeSupport200_suffix_002, ridgeSupport200_suffix_003, ridgeSupport200_suffix_004, ridgeSupport200_suffix_005, ridgeSupport200_suffix_006, ridgeSupport200_suffix_007, ridgeSupport200_suffix_008, ridgeSupport200_suffix_009, ridgeSupport200_suffix_010, ridgeSupport200_suffix_011, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport200_000_mask, ridgeSupport200_001_mask, ridgeSupport200_002_mask, ridgeSupport200_003_mask, ridgeSupport200_004_mask, ridgeSupport200_005_mask, ridgeSupport200_006_mask, ridgeSupport200_007_mask, ridgeSupport200_008_mask, ridgeSupport200_009_mask, ridgeSupport200_010_mask]
    decide +kernel
  · rw [show candidateRows 200 = ridgeSupport200_suffix_000 from ridgeSupport200_eq]
    simp only [ridgeSupport200_suffix_000, ridgeSupport200_suffix_001, ridgeSupport200_suffix_002, ridgeSupport200_suffix_003, ridgeSupport200_suffix_004, ridgeSupport200_suffix_005, ridgeSupport200_suffix_006, ridgeSupport200_suffix_007, ridgeSupport200_suffix_008, ridgeSupport200_suffix_009, ridgeSupport200_suffix_010, ridgeSupport200_suffix_011, List.all_append, List.all_nil, ridgeSupport200_000_checked, ridgeSupport200_001_checked, ridgeSupport200_002_checked, ridgeSupport200_003_checked, ridgeSupport200_004_checked, ridgeSupport200_005_checked, ridgeSupport200_006_checked, ridgeSupport200_007_checked, ridgeSupport200_008_checked, ridgeSupport200_009_checked, ridgeSupport200_010_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase03
