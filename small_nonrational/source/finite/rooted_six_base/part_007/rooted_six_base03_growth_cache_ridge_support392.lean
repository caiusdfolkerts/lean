module
prelude
public import RootedSixBase03GrowthCacheRidgeSupport392Part000
public import RootedSixBase03GrowthCacheRidgeSupport392Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase03
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport392_suffix_decode_011 : PackedRawNatGrowth.readList 13 0 ridgeSupport392_rest_011 =
    (ridgeSupport392_suffix_011, ridgeSupport392_rest_011) := by rfl
theorem ridgeSupport392_suffix_decode_010 : PackedRawNatGrowth.readList 13 26 ridgeSupport392_rest_010 =
    (ridgeSupport392_suffix_010, ridgeSupport392_rest_011) :=
  PackedRawNatGrowth.readList_append_of_eq 13 26 0
    ridgeSupport392_rest_010 ridgeSupport392_rest_011 ridgeSupport392_rest_011
    ridgeSupport392_010 ridgeSupport392_suffix_011 ridgeSupport392_010_decode ridgeSupport392_suffix_decode_011
theorem ridgeSupport392_suffix_decode_009 : PackedRawNatGrowth.readList 13 58 ridgeSupport392_rest_009 =
    (ridgeSupport392_suffix_009, ridgeSupport392_rest_011) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 26
    ridgeSupport392_rest_009 ridgeSupport392_rest_010 ridgeSupport392_rest_011
    ridgeSupport392_009 ridgeSupport392_suffix_010 ridgeSupport392_009_decode ridgeSupport392_suffix_decode_010
theorem ridgeSupport392_suffix_decode_008 : PackedRawNatGrowth.readList 13 90 ridgeSupport392_rest_008 =
    (ridgeSupport392_suffix_008, ridgeSupport392_rest_011) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 58
    ridgeSupport392_rest_008 ridgeSupport392_rest_009 ridgeSupport392_rest_011
    ridgeSupport392_008 ridgeSupport392_suffix_009 ridgeSupport392_008_decode ridgeSupport392_suffix_decode_009
theorem ridgeSupport392_suffix_decode_007 : PackedRawNatGrowth.readList 13 122 ridgeSupport392_rest_007 =
    (ridgeSupport392_suffix_007, ridgeSupport392_rest_011) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 90
    ridgeSupport392_rest_007 ridgeSupport392_rest_008 ridgeSupport392_rest_011
    ridgeSupport392_007 ridgeSupport392_suffix_008 ridgeSupport392_007_decode ridgeSupport392_suffix_decode_008
theorem ridgeSupport392_suffix_decode_006 : PackedRawNatGrowth.readList 13 154 ridgeSupport392_rest_006 =
    (ridgeSupport392_suffix_006, ridgeSupport392_rest_011) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 122
    ridgeSupport392_rest_006 ridgeSupport392_rest_007 ridgeSupport392_rest_011
    ridgeSupport392_006 ridgeSupport392_suffix_007 ridgeSupport392_006_decode ridgeSupport392_suffix_decode_007
theorem ridgeSupport392_suffix_decode_005 : PackedRawNatGrowth.readList 13 186 ridgeSupport392_rest_005 =
    (ridgeSupport392_suffix_005, ridgeSupport392_rest_011) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 154
    ridgeSupport392_rest_005 ridgeSupport392_rest_006 ridgeSupport392_rest_011
    ridgeSupport392_005 ridgeSupport392_suffix_006 ridgeSupport392_005_decode ridgeSupport392_suffix_decode_006
theorem ridgeSupport392_suffix_decode_004 : PackedRawNatGrowth.readList 13 218 ridgeSupport392_rest_004 =
    (ridgeSupport392_suffix_004, ridgeSupport392_rest_011) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 186
    ridgeSupport392_rest_004 ridgeSupport392_rest_005 ridgeSupport392_rest_011
    ridgeSupport392_004 ridgeSupport392_suffix_005 ridgeSupport392_004_decode ridgeSupport392_suffix_decode_005
theorem ridgeSupport392_suffix_decode_003 : PackedRawNatGrowth.readList 13 250 ridgeSupport392_rest_003 =
    (ridgeSupport392_suffix_003, ridgeSupport392_rest_011) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 218
    ridgeSupport392_rest_003 ridgeSupport392_rest_004 ridgeSupport392_rest_011
    ridgeSupport392_003 ridgeSupport392_suffix_004 ridgeSupport392_003_decode ridgeSupport392_suffix_decode_004
theorem ridgeSupport392_suffix_decode_002 : PackedRawNatGrowth.readList 13 282 ridgeSupport392_rest_002 =
    (ridgeSupport392_suffix_002, ridgeSupport392_rest_011) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 250
    ridgeSupport392_rest_002 ridgeSupport392_rest_003 ridgeSupport392_rest_011
    ridgeSupport392_002 ridgeSupport392_suffix_003 ridgeSupport392_002_decode ridgeSupport392_suffix_decode_003
theorem ridgeSupport392_suffix_decode_001 : PackedRawNatGrowth.readList 13 314 ridgeSupport392_rest_001 =
    (ridgeSupport392_suffix_001, ridgeSupport392_rest_011) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 282
    ridgeSupport392_rest_001 ridgeSupport392_rest_002 ridgeSupport392_rest_011
    ridgeSupport392_001 ridgeSupport392_suffix_002 ridgeSupport392_001_decode ridgeSupport392_suffix_decode_002
theorem ridgeSupport392_suffix_decode_000 : PackedRawNatGrowth.readList 13 346 ridgeSupport392_rest_000 =
    (ridgeSupport392_suffix_000, ridgeSupport392_rest_011) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 314
    ridgeSupport392_rest_000 ridgeSupport392_rest_001 ridgeSupport392_rest_011
    ridgeSupport392_000 ridgeSupport392_suffix_001 ridgeSupport392_000_decode ridgeSupport392_suffix_decode_001
theorem ridgeSupport392_eq : candidateSupports 392 = ridgeSupport392_suffix_000 := by
  rw [ridgeSupport392_source]
  exact congrArg Prod.fst ridgeSupport392_suffix_decode_000
theorem ridgeTest_large_392 : ridgeTest 392 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [show candidateRows 392 = ridgeSupport392_suffix_000 from ridgeSupport392_eq]
    simp only [ridgeSupport392_suffix_000, ridgeSupport392_suffix_001, ridgeSupport392_suffix_002, ridgeSupport392_suffix_003, ridgeSupport392_suffix_004, ridgeSupport392_suffix_005, ridgeSupport392_suffix_006, ridgeSupport392_suffix_007, ridgeSupport392_suffix_008, ridgeSupport392_suffix_009, ridgeSupport392_suffix_010, ridgeSupport392_suffix_011, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport392_000_mask, ridgeSupport392_001_mask, ridgeSupport392_002_mask, ridgeSupport392_003_mask, ridgeSupport392_004_mask, ridgeSupport392_005_mask, ridgeSupport392_006_mask, ridgeSupport392_007_mask, ridgeSupport392_008_mask, ridgeSupport392_009_mask, ridgeSupport392_010_mask]
    decide +kernel
  · rw [show candidateRows 392 = ridgeSupport392_suffix_000 from ridgeSupport392_eq]
    simp only [ridgeSupport392_suffix_000, ridgeSupport392_suffix_001, ridgeSupport392_suffix_002, ridgeSupport392_suffix_003, ridgeSupport392_suffix_004, ridgeSupport392_suffix_005, ridgeSupport392_suffix_006, ridgeSupport392_suffix_007, ridgeSupport392_suffix_008, ridgeSupport392_suffix_009, ridgeSupport392_suffix_010, ridgeSupport392_suffix_011, List.all_append, List.all_nil, ridgeSupport392_000_checked, ridgeSupport392_001_checked, ridgeSupport392_002_checked, ridgeSupport392_003_checked, ridgeSupport392_004_checked, ridgeSupport392_005_checked, ridgeSupport392_006_checked, ridgeSupport392_007_checked, ridgeSupport392_008_checked, ridgeSupport392_009_checked, ridgeSupport392_010_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase03
