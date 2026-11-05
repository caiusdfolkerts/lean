module
prelude
public import RootedSixBase03GrowthCacheRidgeSupport328Part000
public import RootedSixBase03GrowthCacheRidgeSupport328Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase03
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport328_suffix_decode_011 : PackedRawNatGrowth.readList 13 0 ridgeSupport328_rest_011 =
    (ridgeSupport328_suffix_011, ridgeSupport328_rest_011) := by rfl
theorem ridgeSupport328_suffix_decode_010 : PackedRawNatGrowth.readList 13 26 ridgeSupport328_rest_010 =
    (ridgeSupport328_suffix_010, ridgeSupport328_rest_011) :=
  PackedRawNatGrowth.readList_append_of_eq 13 26 0
    ridgeSupport328_rest_010 ridgeSupport328_rest_011 ridgeSupport328_rest_011
    ridgeSupport328_010 ridgeSupport328_suffix_011 ridgeSupport328_010_decode ridgeSupport328_suffix_decode_011
theorem ridgeSupport328_suffix_decode_009 : PackedRawNatGrowth.readList 13 58 ridgeSupport328_rest_009 =
    (ridgeSupport328_suffix_009, ridgeSupport328_rest_011) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 26
    ridgeSupport328_rest_009 ridgeSupport328_rest_010 ridgeSupport328_rest_011
    ridgeSupport328_009 ridgeSupport328_suffix_010 ridgeSupport328_009_decode ridgeSupport328_suffix_decode_010
theorem ridgeSupport328_suffix_decode_008 : PackedRawNatGrowth.readList 13 90 ridgeSupport328_rest_008 =
    (ridgeSupport328_suffix_008, ridgeSupport328_rest_011) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 58
    ridgeSupport328_rest_008 ridgeSupport328_rest_009 ridgeSupport328_rest_011
    ridgeSupport328_008 ridgeSupport328_suffix_009 ridgeSupport328_008_decode ridgeSupport328_suffix_decode_009
theorem ridgeSupport328_suffix_decode_007 : PackedRawNatGrowth.readList 13 122 ridgeSupport328_rest_007 =
    (ridgeSupport328_suffix_007, ridgeSupport328_rest_011) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 90
    ridgeSupport328_rest_007 ridgeSupport328_rest_008 ridgeSupport328_rest_011
    ridgeSupport328_007 ridgeSupport328_suffix_008 ridgeSupport328_007_decode ridgeSupport328_suffix_decode_008
theorem ridgeSupport328_suffix_decode_006 : PackedRawNatGrowth.readList 13 154 ridgeSupport328_rest_006 =
    (ridgeSupport328_suffix_006, ridgeSupport328_rest_011) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 122
    ridgeSupport328_rest_006 ridgeSupport328_rest_007 ridgeSupport328_rest_011
    ridgeSupport328_006 ridgeSupport328_suffix_007 ridgeSupport328_006_decode ridgeSupport328_suffix_decode_007
theorem ridgeSupport328_suffix_decode_005 : PackedRawNatGrowth.readList 13 186 ridgeSupport328_rest_005 =
    (ridgeSupport328_suffix_005, ridgeSupport328_rest_011) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 154
    ridgeSupport328_rest_005 ridgeSupport328_rest_006 ridgeSupport328_rest_011
    ridgeSupport328_005 ridgeSupport328_suffix_006 ridgeSupport328_005_decode ridgeSupport328_suffix_decode_006
theorem ridgeSupport328_suffix_decode_004 : PackedRawNatGrowth.readList 13 218 ridgeSupport328_rest_004 =
    (ridgeSupport328_suffix_004, ridgeSupport328_rest_011) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 186
    ridgeSupport328_rest_004 ridgeSupport328_rest_005 ridgeSupport328_rest_011
    ridgeSupport328_004 ridgeSupport328_suffix_005 ridgeSupport328_004_decode ridgeSupport328_suffix_decode_005
theorem ridgeSupport328_suffix_decode_003 : PackedRawNatGrowth.readList 13 250 ridgeSupport328_rest_003 =
    (ridgeSupport328_suffix_003, ridgeSupport328_rest_011) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 218
    ridgeSupport328_rest_003 ridgeSupport328_rest_004 ridgeSupport328_rest_011
    ridgeSupport328_003 ridgeSupport328_suffix_004 ridgeSupport328_003_decode ridgeSupport328_suffix_decode_004
theorem ridgeSupport328_suffix_decode_002 : PackedRawNatGrowth.readList 13 282 ridgeSupport328_rest_002 =
    (ridgeSupport328_suffix_002, ridgeSupport328_rest_011) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 250
    ridgeSupport328_rest_002 ridgeSupport328_rest_003 ridgeSupport328_rest_011
    ridgeSupport328_002 ridgeSupport328_suffix_003 ridgeSupport328_002_decode ridgeSupport328_suffix_decode_003
theorem ridgeSupport328_suffix_decode_001 : PackedRawNatGrowth.readList 13 314 ridgeSupport328_rest_001 =
    (ridgeSupport328_suffix_001, ridgeSupport328_rest_011) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 282
    ridgeSupport328_rest_001 ridgeSupport328_rest_002 ridgeSupport328_rest_011
    ridgeSupport328_001 ridgeSupport328_suffix_002 ridgeSupport328_001_decode ridgeSupport328_suffix_decode_002
theorem ridgeSupport328_suffix_decode_000 : PackedRawNatGrowth.readList 13 346 ridgeSupport328_rest_000 =
    (ridgeSupport328_suffix_000, ridgeSupport328_rest_011) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 314
    ridgeSupport328_rest_000 ridgeSupport328_rest_001 ridgeSupport328_rest_011
    ridgeSupport328_000 ridgeSupport328_suffix_001 ridgeSupport328_000_decode ridgeSupport328_suffix_decode_001
theorem ridgeSupport328_eq : candidateSupports 328 = ridgeSupport328_suffix_000 := by
  rw [ridgeSupport328_source]
  exact congrArg Prod.fst ridgeSupport328_suffix_decode_000
theorem ridgeTest_large_328 : ridgeTest 328 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [show candidateRows 328 = ridgeSupport328_suffix_000 from ridgeSupport328_eq]
    simp only [ridgeSupport328_suffix_000, ridgeSupport328_suffix_001, ridgeSupport328_suffix_002, ridgeSupport328_suffix_003, ridgeSupport328_suffix_004, ridgeSupport328_suffix_005, ridgeSupport328_suffix_006, ridgeSupport328_suffix_007, ridgeSupport328_suffix_008, ridgeSupport328_suffix_009, ridgeSupport328_suffix_010, ridgeSupport328_suffix_011, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport328_000_mask, ridgeSupport328_001_mask, ridgeSupport328_002_mask, ridgeSupport328_003_mask, ridgeSupport328_004_mask, ridgeSupport328_005_mask, ridgeSupport328_006_mask, ridgeSupport328_007_mask, ridgeSupport328_008_mask, ridgeSupport328_009_mask, ridgeSupport328_010_mask]
    decide +kernel
  · rw [show candidateRows 328 = ridgeSupport328_suffix_000 from ridgeSupport328_eq]
    simp only [ridgeSupport328_suffix_000, ridgeSupport328_suffix_001, ridgeSupport328_suffix_002, ridgeSupport328_suffix_003, ridgeSupport328_suffix_004, ridgeSupport328_suffix_005, ridgeSupport328_suffix_006, ridgeSupport328_suffix_007, ridgeSupport328_suffix_008, ridgeSupport328_suffix_009, ridgeSupport328_suffix_010, ridgeSupport328_suffix_011, List.all_append, List.all_nil, ridgeSupport328_000_checked, ridgeSupport328_001_checked, ridgeSupport328_002_checked, ridgeSupport328_003_checked, ridgeSupport328_004_checked, ridgeSupport328_005_checked, ridgeSupport328_006_checked, ridgeSupport328_007_checked, ridgeSupport328_008_checked, ridgeSupport328_009_checked, ridgeSupport328_010_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase03
