module
prelude
public import RootedSixBase03GrowthCacheRidgeSupport580Part000
public import RootedSixBase03GrowthCacheRidgeSupport580Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase03
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport580_suffix_decode_011 : PackedRawNatGrowth.readList 13 0 ridgeSupport580_rest_011 =
    (ridgeSupport580_suffix_011, ridgeSupport580_rest_011) := by rfl
theorem ridgeSupport580_suffix_decode_010 : PackedRawNatGrowth.readList 13 26 ridgeSupport580_rest_010 =
    (ridgeSupport580_suffix_010, ridgeSupport580_rest_011) :=
  PackedRawNatGrowth.readList_append_of_eq 13 26 0
    ridgeSupport580_rest_010 ridgeSupport580_rest_011 ridgeSupport580_rest_011
    ridgeSupport580_010 ridgeSupport580_suffix_011 ridgeSupport580_010_decode ridgeSupport580_suffix_decode_011
theorem ridgeSupport580_suffix_decode_009 : PackedRawNatGrowth.readList 13 58 ridgeSupport580_rest_009 =
    (ridgeSupport580_suffix_009, ridgeSupport580_rest_011) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 26
    ridgeSupport580_rest_009 ridgeSupport580_rest_010 ridgeSupport580_rest_011
    ridgeSupport580_009 ridgeSupport580_suffix_010 ridgeSupport580_009_decode ridgeSupport580_suffix_decode_010
theorem ridgeSupport580_suffix_decode_008 : PackedRawNatGrowth.readList 13 90 ridgeSupport580_rest_008 =
    (ridgeSupport580_suffix_008, ridgeSupport580_rest_011) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 58
    ridgeSupport580_rest_008 ridgeSupport580_rest_009 ridgeSupport580_rest_011
    ridgeSupport580_008 ridgeSupport580_suffix_009 ridgeSupport580_008_decode ridgeSupport580_suffix_decode_009
theorem ridgeSupport580_suffix_decode_007 : PackedRawNatGrowth.readList 13 122 ridgeSupport580_rest_007 =
    (ridgeSupport580_suffix_007, ridgeSupport580_rest_011) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 90
    ridgeSupport580_rest_007 ridgeSupport580_rest_008 ridgeSupport580_rest_011
    ridgeSupport580_007 ridgeSupport580_suffix_008 ridgeSupport580_007_decode ridgeSupport580_suffix_decode_008
theorem ridgeSupport580_suffix_decode_006 : PackedRawNatGrowth.readList 13 154 ridgeSupport580_rest_006 =
    (ridgeSupport580_suffix_006, ridgeSupport580_rest_011) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 122
    ridgeSupport580_rest_006 ridgeSupport580_rest_007 ridgeSupport580_rest_011
    ridgeSupport580_006 ridgeSupport580_suffix_007 ridgeSupport580_006_decode ridgeSupport580_suffix_decode_007
theorem ridgeSupport580_suffix_decode_005 : PackedRawNatGrowth.readList 13 186 ridgeSupport580_rest_005 =
    (ridgeSupport580_suffix_005, ridgeSupport580_rest_011) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 154
    ridgeSupport580_rest_005 ridgeSupport580_rest_006 ridgeSupport580_rest_011
    ridgeSupport580_005 ridgeSupport580_suffix_006 ridgeSupport580_005_decode ridgeSupport580_suffix_decode_006
theorem ridgeSupport580_suffix_decode_004 : PackedRawNatGrowth.readList 13 218 ridgeSupport580_rest_004 =
    (ridgeSupport580_suffix_004, ridgeSupport580_rest_011) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 186
    ridgeSupport580_rest_004 ridgeSupport580_rest_005 ridgeSupport580_rest_011
    ridgeSupport580_004 ridgeSupport580_suffix_005 ridgeSupport580_004_decode ridgeSupport580_suffix_decode_005
theorem ridgeSupport580_suffix_decode_003 : PackedRawNatGrowth.readList 13 250 ridgeSupport580_rest_003 =
    (ridgeSupport580_suffix_003, ridgeSupport580_rest_011) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 218
    ridgeSupport580_rest_003 ridgeSupport580_rest_004 ridgeSupport580_rest_011
    ridgeSupport580_003 ridgeSupport580_suffix_004 ridgeSupport580_003_decode ridgeSupport580_suffix_decode_004
theorem ridgeSupport580_suffix_decode_002 : PackedRawNatGrowth.readList 13 282 ridgeSupport580_rest_002 =
    (ridgeSupport580_suffix_002, ridgeSupport580_rest_011) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 250
    ridgeSupport580_rest_002 ridgeSupport580_rest_003 ridgeSupport580_rest_011
    ridgeSupport580_002 ridgeSupport580_suffix_003 ridgeSupport580_002_decode ridgeSupport580_suffix_decode_003
theorem ridgeSupport580_suffix_decode_001 : PackedRawNatGrowth.readList 13 314 ridgeSupport580_rest_001 =
    (ridgeSupport580_suffix_001, ridgeSupport580_rest_011) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 282
    ridgeSupport580_rest_001 ridgeSupport580_rest_002 ridgeSupport580_rest_011
    ridgeSupport580_001 ridgeSupport580_suffix_002 ridgeSupport580_001_decode ridgeSupport580_suffix_decode_002
theorem ridgeSupport580_suffix_decode_000 : PackedRawNatGrowth.readList 13 346 ridgeSupport580_rest_000 =
    (ridgeSupport580_suffix_000, ridgeSupport580_rest_011) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 314
    ridgeSupport580_rest_000 ridgeSupport580_rest_001 ridgeSupport580_rest_011
    ridgeSupport580_000 ridgeSupport580_suffix_001 ridgeSupport580_000_decode ridgeSupport580_suffix_decode_001
theorem ridgeSupport580_eq : candidateSupports 580 = ridgeSupport580_suffix_000 := by
  rw [ridgeSupport580_source]
  exact congrArg Prod.fst ridgeSupport580_suffix_decode_000
theorem ridgeTest_large_580 : ridgeTest 580 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [show candidateRows 580 = ridgeSupport580_suffix_000 from ridgeSupport580_eq]
    simp only [ridgeSupport580_suffix_000, ridgeSupport580_suffix_001, ridgeSupport580_suffix_002, ridgeSupport580_suffix_003, ridgeSupport580_suffix_004, ridgeSupport580_suffix_005, ridgeSupport580_suffix_006, ridgeSupport580_suffix_007, ridgeSupport580_suffix_008, ridgeSupport580_suffix_009, ridgeSupport580_suffix_010, ridgeSupport580_suffix_011, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport580_000_mask, ridgeSupport580_001_mask, ridgeSupport580_002_mask, ridgeSupport580_003_mask, ridgeSupport580_004_mask, ridgeSupport580_005_mask, ridgeSupport580_006_mask, ridgeSupport580_007_mask, ridgeSupport580_008_mask, ridgeSupport580_009_mask, ridgeSupport580_010_mask]
    decide +kernel
  · rw [show candidateRows 580 = ridgeSupport580_suffix_000 from ridgeSupport580_eq]
    simp only [ridgeSupport580_suffix_000, ridgeSupport580_suffix_001, ridgeSupport580_suffix_002, ridgeSupport580_suffix_003, ridgeSupport580_suffix_004, ridgeSupport580_suffix_005, ridgeSupport580_suffix_006, ridgeSupport580_suffix_007, ridgeSupport580_suffix_008, ridgeSupport580_suffix_009, ridgeSupport580_suffix_010, ridgeSupport580_suffix_011, List.all_append, List.all_nil, ridgeSupport580_000_checked, ridgeSupport580_001_checked, ridgeSupport580_002_checked, ridgeSupport580_003_checked, ridgeSupport580_004_checked, ridgeSupport580_005_checked, ridgeSupport580_006_checked, ridgeSupport580_007_checked, ridgeSupport580_008_checked, ridgeSupport580_009_checked, ridgeSupport580_010_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase03
