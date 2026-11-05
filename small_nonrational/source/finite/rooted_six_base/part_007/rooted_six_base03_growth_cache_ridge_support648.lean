module
prelude
public import RootedSixBase03GrowthCacheRidgeSupport648Part000
public import RootedSixBase03GrowthCacheRidgeSupport648Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase03
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport648_suffix_decode_011 : PackedRawNatGrowth.readList 13 0 ridgeSupport648_rest_011 =
    (ridgeSupport648_suffix_011, ridgeSupport648_rest_011) := by rfl
theorem ridgeSupport648_suffix_decode_010 : PackedRawNatGrowth.readList 13 26 ridgeSupport648_rest_010 =
    (ridgeSupport648_suffix_010, ridgeSupport648_rest_011) :=
  PackedRawNatGrowth.readList_append_of_eq 13 26 0
    ridgeSupport648_rest_010 ridgeSupport648_rest_011 ridgeSupport648_rest_011
    ridgeSupport648_010 ridgeSupport648_suffix_011 ridgeSupport648_010_decode ridgeSupport648_suffix_decode_011
theorem ridgeSupport648_suffix_decode_009 : PackedRawNatGrowth.readList 13 58 ridgeSupport648_rest_009 =
    (ridgeSupport648_suffix_009, ridgeSupport648_rest_011) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 26
    ridgeSupport648_rest_009 ridgeSupport648_rest_010 ridgeSupport648_rest_011
    ridgeSupport648_009 ridgeSupport648_suffix_010 ridgeSupport648_009_decode ridgeSupport648_suffix_decode_010
theorem ridgeSupport648_suffix_decode_008 : PackedRawNatGrowth.readList 13 90 ridgeSupport648_rest_008 =
    (ridgeSupport648_suffix_008, ridgeSupport648_rest_011) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 58
    ridgeSupport648_rest_008 ridgeSupport648_rest_009 ridgeSupport648_rest_011
    ridgeSupport648_008 ridgeSupport648_suffix_009 ridgeSupport648_008_decode ridgeSupport648_suffix_decode_009
theorem ridgeSupport648_suffix_decode_007 : PackedRawNatGrowth.readList 13 122 ridgeSupport648_rest_007 =
    (ridgeSupport648_suffix_007, ridgeSupport648_rest_011) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 90
    ridgeSupport648_rest_007 ridgeSupport648_rest_008 ridgeSupport648_rest_011
    ridgeSupport648_007 ridgeSupport648_suffix_008 ridgeSupport648_007_decode ridgeSupport648_suffix_decode_008
theorem ridgeSupport648_suffix_decode_006 : PackedRawNatGrowth.readList 13 154 ridgeSupport648_rest_006 =
    (ridgeSupport648_suffix_006, ridgeSupport648_rest_011) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 122
    ridgeSupport648_rest_006 ridgeSupport648_rest_007 ridgeSupport648_rest_011
    ridgeSupport648_006 ridgeSupport648_suffix_007 ridgeSupport648_006_decode ridgeSupport648_suffix_decode_007
theorem ridgeSupport648_suffix_decode_005 : PackedRawNatGrowth.readList 13 186 ridgeSupport648_rest_005 =
    (ridgeSupport648_suffix_005, ridgeSupport648_rest_011) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 154
    ridgeSupport648_rest_005 ridgeSupport648_rest_006 ridgeSupport648_rest_011
    ridgeSupport648_005 ridgeSupport648_suffix_006 ridgeSupport648_005_decode ridgeSupport648_suffix_decode_006
theorem ridgeSupport648_suffix_decode_004 : PackedRawNatGrowth.readList 13 218 ridgeSupport648_rest_004 =
    (ridgeSupport648_suffix_004, ridgeSupport648_rest_011) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 186
    ridgeSupport648_rest_004 ridgeSupport648_rest_005 ridgeSupport648_rest_011
    ridgeSupport648_004 ridgeSupport648_suffix_005 ridgeSupport648_004_decode ridgeSupport648_suffix_decode_005
theorem ridgeSupport648_suffix_decode_003 : PackedRawNatGrowth.readList 13 250 ridgeSupport648_rest_003 =
    (ridgeSupport648_suffix_003, ridgeSupport648_rest_011) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 218
    ridgeSupport648_rest_003 ridgeSupport648_rest_004 ridgeSupport648_rest_011
    ridgeSupport648_003 ridgeSupport648_suffix_004 ridgeSupport648_003_decode ridgeSupport648_suffix_decode_004
theorem ridgeSupport648_suffix_decode_002 : PackedRawNatGrowth.readList 13 282 ridgeSupport648_rest_002 =
    (ridgeSupport648_suffix_002, ridgeSupport648_rest_011) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 250
    ridgeSupport648_rest_002 ridgeSupport648_rest_003 ridgeSupport648_rest_011
    ridgeSupport648_002 ridgeSupport648_suffix_003 ridgeSupport648_002_decode ridgeSupport648_suffix_decode_003
theorem ridgeSupport648_suffix_decode_001 : PackedRawNatGrowth.readList 13 314 ridgeSupport648_rest_001 =
    (ridgeSupport648_suffix_001, ridgeSupport648_rest_011) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 282
    ridgeSupport648_rest_001 ridgeSupport648_rest_002 ridgeSupport648_rest_011
    ridgeSupport648_001 ridgeSupport648_suffix_002 ridgeSupport648_001_decode ridgeSupport648_suffix_decode_002
theorem ridgeSupport648_suffix_decode_000 : PackedRawNatGrowth.readList 13 346 ridgeSupport648_rest_000 =
    (ridgeSupport648_suffix_000, ridgeSupport648_rest_011) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 314
    ridgeSupport648_rest_000 ridgeSupport648_rest_001 ridgeSupport648_rest_011
    ridgeSupport648_000 ridgeSupport648_suffix_001 ridgeSupport648_000_decode ridgeSupport648_suffix_decode_001
theorem ridgeSupport648_eq : candidateSupports 648 = ridgeSupport648_suffix_000 := by
  rw [ridgeSupport648_source]
  exact congrArg Prod.fst ridgeSupport648_suffix_decode_000
theorem ridgeTest_large_648 : ridgeTest 648 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [show candidateRows 648 = ridgeSupport648_suffix_000 from ridgeSupport648_eq]
    simp only [ridgeSupport648_suffix_000, ridgeSupport648_suffix_001, ridgeSupport648_suffix_002, ridgeSupport648_suffix_003, ridgeSupport648_suffix_004, ridgeSupport648_suffix_005, ridgeSupport648_suffix_006, ridgeSupport648_suffix_007, ridgeSupport648_suffix_008, ridgeSupport648_suffix_009, ridgeSupport648_suffix_010, ridgeSupport648_suffix_011, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport648_000_mask, ridgeSupport648_001_mask, ridgeSupport648_002_mask, ridgeSupport648_003_mask, ridgeSupport648_004_mask, ridgeSupport648_005_mask, ridgeSupport648_006_mask, ridgeSupport648_007_mask, ridgeSupport648_008_mask, ridgeSupport648_009_mask, ridgeSupport648_010_mask]
    decide +kernel
  · rw [show candidateRows 648 = ridgeSupport648_suffix_000 from ridgeSupport648_eq]
    simp only [ridgeSupport648_suffix_000, ridgeSupport648_suffix_001, ridgeSupport648_suffix_002, ridgeSupport648_suffix_003, ridgeSupport648_suffix_004, ridgeSupport648_suffix_005, ridgeSupport648_suffix_006, ridgeSupport648_suffix_007, ridgeSupport648_suffix_008, ridgeSupport648_suffix_009, ridgeSupport648_suffix_010, ridgeSupport648_suffix_011, List.all_append, List.all_nil, ridgeSupport648_000_checked, ridgeSupport648_001_checked, ridgeSupport648_002_checked, ridgeSupport648_003_checked, ridgeSupport648_004_checked, ridgeSupport648_005_checked, ridgeSupport648_006_checked, ridgeSupport648_007_checked, ridgeSupport648_008_checked, ridgeSupport648_009_checked, ridgeSupport648_010_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase03
