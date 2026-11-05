module
prelude
public import RootedSixBase03GrowthCacheRidgeSupport352Part000
public import RootedSixBase03GrowthCacheRidgeSupport352Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase03
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport352_suffix_decode_012 : PackedRawNatGrowth.readList 13 0 ridgeSupport352_rest_012 =
    (ridgeSupport352_suffix_012, ridgeSupport352_rest_012) := by rfl
theorem ridgeSupport352_suffix_decode_011 : PackedRawNatGrowth.readList 13 26 ridgeSupport352_rest_011 =
    (ridgeSupport352_suffix_011, ridgeSupport352_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 13 26 0
    ridgeSupport352_rest_011 ridgeSupport352_rest_012 ridgeSupport352_rest_012
    ridgeSupport352_011 ridgeSupport352_suffix_012 ridgeSupport352_011_decode ridgeSupport352_suffix_decode_012
theorem ridgeSupport352_suffix_decode_010 : PackedRawNatGrowth.readList 13 58 ridgeSupport352_rest_010 =
    (ridgeSupport352_suffix_010, ridgeSupport352_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 26
    ridgeSupport352_rest_010 ridgeSupport352_rest_011 ridgeSupport352_rest_012
    ridgeSupport352_010 ridgeSupport352_suffix_011 ridgeSupport352_010_decode ridgeSupport352_suffix_decode_011
theorem ridgeSupport352_suffix_decode_009 : PackedRawNatGrowth.readList 13 90 ridgeSupport352_rest_009 =
    (ridgeSupport352_suffix_009, ridgeSupport352_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 58
    ridgeSupport352_rest_009 ridgeSupport352_rest_010 ridgeSupport352_rest_012
    ridgeSupport352_009 ridgeSupport352_suffix_010 ridgeSupport352_009_decode ridgeSupport352_suffix_decode_010
theorem ridgeSupport352_suffix_decode_008 : PackedRawNatGrowth.readList 13 122 ridgeSupport352_rest_008 =
    (ridgeSupport352_suffix_008, ridgeSupport352_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 90
    ridgeSupport352_rest_008 ridgeSupport352_rest_009 ridgeSupport352_rest_012
    ridgeSupport352_008 ridgeSupport352_suffix_009 ridgeSupport352_008_decode ridgeSupport352_suffix_decode_009
theorem ridgeSupport352_suffix_decode_007 : PackedRawNatGrowth.readList 13 154 ridgeSupport352_rest_007 =
    (ridgeSupport352_suffix_007, ridgeSupport352_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 122
    ridgeSupport352_rest_007 ridgeSupport352_rest_008 ridgeSupport352_rest_012
    ridgeSupport352_007 ridgeSupport352_suffix_008 ridgeSupport352_007_decode ridgeSupport352_suffix_decode_008
theorem ridgeSupport352_suffix_decode_006 : PackedRawNatGrowth.readList 13 186 ridgeSupport352_rest_006 =
    (ridgeSupport352_suffix_006, ridgeSupport352_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 154
    ridgeSupport352_rest_006 ridgeSupport352_rest_007 ridgeSupport352_rest_012
    ridgeSupport352_006 ridgeSupport352_suffix_007 ridgeSupport352_006_decode ridgeSupport352_suffix_decode_007
theorem ridgeSupport352_suffix_decode_005 : PackedRawNatGrowth.readList 13 218 ridgeSupport352_rest_005 =
    (ridgeSupport352_suffix_005, ridgeSupport352_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 186
    ridgeSupport352_rest_005 ridgeSupport352_rest_006 ridgeSupport352_rest_012
    ridgeSupport352_005 ridgeSupport352_suffix_006 ridgeSupport352_005_decode ridgeSupport352_suffix_decode_006
theorem ridgeSupport352_suffix_decode_004 : PackedRawNatGrowth.readList 13 250 ridgeSupport352_rest_004 =
    (ridgeSupport352_suffix_004, ridgeSupport352_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 218
    ridgeSupport352_rest_004 ridgeSupport352_rest_005 ridgeSupport352_rest_012
    ridgeSupport352_004 ridgeSupport352_suffix_005 ridgeSupport352_004_decode ridgeSupport352_suffix_decode_005
theorem ridgeSupport352_suffix_decode_003 : PackedRawNatGrowth.readList 13 282 ridgeSupport352_rest_003 =
    (ridgeSupport352_suffix_003, ridgeSupport352_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 250
    ridgeSupport352_rest_003 ridgeSupport352_rest_004 ridgeSupport352_rest_012
    ridgeSupport352_003 ridgeSupport352_suffix_004 ridgeSupport352_003_decode ridgeSupport352_suffix_decode_004
theorem ridgeSupport352_suffix_decode_002 : PackedRawNatGrowth.readList 13 314 ridgeSupport352_rest_002 =
    (ridgeSupport352_suffix_002, ridgeSupport352_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 282
    ridgeSupport352_rest_002 ridgeSupport352_rest_003 ridgeSupport352_rest_012
    ridgeSupport352_002 ridgeSupport352_suffix_003 ridgeSupport352_002_decode ridgeSupport352_suffix_decode_003
theorem ridgeSupport352_suffix_decode_001 : PackedRawNatGrowth.readList 13 346 ridgeSupport352_rest_001 =
    (ridgeSupport352_suffix_001, ridgeSupport352_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 314
    ridgeSupport352_rest_001 ridgeSupport352_rest_002 ridgeSupport352_rest_012
    ridgeSupport352_001 ridgeSupport352_suffix_002 ridgeSupport352_001_decode ridgeSupport352_suffix_decode_002
theorem ridgeSupport352_suffix_decode_000 : PackedRawNatGrowth.readList 13 378 ridgeSupport352_rest_000 =
    (ridgeSupport352_suffix_000, ridgeSupport352_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 346
    ridgeSupport352_rest_000 ridgeSupport352_rest_001 ridgeSupport352_rest_012
    ridgeSupport352_000 ridgeSupport352_suffix_001 ridgeSupport352_000_decode ridgeSupport352_suffix_decode_001
theorem ridgeSupport352_eq : candidateSupports 352 = ridgeSupport352_suffix_000 := by
  rw [ridgeSupport352_source]
  exact congrArg Prod.fst ridgeSupport352_suffix_decode_000
theorem ridgeTest_large_352 : ridgeTest 352 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [show candidateRows 352 = ridgeSupport352_suffix_000 from ridgeSupport352_eq]
    simp only [ridgeSupport352_suffix_000, ridgeSupport352_suffix_001, ridgeSupport352_suffix_002, ridgeSupport352_suffix_003, ridgeSupport352_suffix_004, ridgeSupport352_suffix_005, ridgeSupport352_suffix_006, ridgeSupport352_suffix_007, ridgeSupport352_suffix_008, ridgeSupport352_suffix_009, ridgeSupport352_suffix_010, ridgeSupport352_suffix_011, ridgeSupport352_suffix_012, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport352_000_mask, ridgeSupport352_001_mask, ridgeSupport352_002_mask, ridgeSupport352_003_mask, ridgeSupport352_004_mask, ridgeSupport352_005_mask, ridgeSupport352_006_mask, ridgeSupport352_007_mask, ridgeSupport352_008_mask, ridgeSupport352_009_mask, ridgeSupport352_010_mask, ridgeSupport352_011_mask]
    decide +kernel
  · rw [show candidateRows 352 = ridgeSupport352_suffix_000 from ridgeSupport352_eq]
    simp only [ridgeSupport352_suffix_000, ridgeSupport352_suffix_001, ridgeSupport352_suffix_002, ridgeSupport352_suffix_003, ridgeSupport352_suffix_004, ridgeSupport352_suffix_005, ridgeSupport352_suffix_006, ridgeSupport352_suffix_007, ridgeSupport352_suffix_008, ridgeSupport352_suffix_009, ridgeSupport352_suffix_010, ridgeSupport352_suffix_011, ridgeSupport352_suffix_012, List.all_append, List.all_nil, ridgeSupport352_000_checked, ridgeSupport352_001_checked, ridgeSupport352_002_checked, ridgeSupport352_003_checked, ridgeSupport352_004_checked, ridgeSupport352_005_checked, ridgeSupport352_006_checked, ridgeSupport352_007_checked, ridgeSupport352_008_checked, ridgeSupport352_009_checked, ridgeSupport352_010_checked, ridgeSupport352_011_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase03
