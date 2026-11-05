module
prelude
public import RootedSixBase03GrowthCacheRidgeSupport52Part000
public import RootedSixBase03GrowthCacheRidgeSupport52Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase03
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport52_suffix_decode_011 : PackedRawNatGrowth.readList 13 0 ridgeSupport52_rest_011 =
    (ridgeSupport52_suffix_011, ridgeSupport52_rest_011) := by rfl
theorem ridgeSupport52_suffix_decode_010 : PackedRawNatGrowth.readList 13 21 ridgeSupport52_rest_010 =
    (ridgeSupport52_suffix_010, ridgeSupport52_rest_011) :=
  PackedRawNatGrowth.readList_append_of_eq 13 21 0
    ridgeSupport52_rest_010 ridgeSupport52_rest_011 ridgeSupport52_rest_011
    ridgeSupport52_010 ridgeSupport52_suffix_011 ridgeSupport52_010_decode ridgeSupport52_suffix_decode_011
theorem ridgeSupport52_suffix_decode_009 : PackedRawNatGrowth.readList 13 53 ridgeSupport52_rest_009 =
    (ridgeSupport52_suffix_009, ridgeSupport52_rest_011) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 21
    ridgeSupport52_rest_009 ridgeSupport52_rest_010 ridgeSupport52_rest_011
    ridgeSupport52_009 ridgeSupport52_suffix_010 ridgeSupport52_009_decode ridgeSupport52_suffix_decode_010
theorem ridgeSupport52_suffix_decode_008 : PackedRawNatGrowth.readList 13 85 ridgeSupport52_rest_008 =
    (ridgeSupport52_suffix_008, ridgeSupport52_rest_011) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 53
    ridgeSupport52_rest_008 ridgeSupport52_rest_009 ridgeSupport52_rest_011
    ridgeSupport52_008 ridgeSupport52_suffix_009 ridgeSupport52_008_decode ridgeSupport52_suffix_decode_009
theorem ridgeSupport52_suffix_decode_007 : PackedRawNatGrowth.readList 13 117 ridgeSupport52_rest_007 =
    (ridgeSupport52_suffix_007, ridgeSupport52_rest_011) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 85
    ridgeSupport52_rest_007 ridgeSupport52_rest_008 ridgeSupport52_rest_011
    ridgeSupport52_007 ridgeSupport52_suffix_008 ridgeSupport52_007_decode ridgeSupport52_suffix_decode_008
theorem ridgeSupport52_suffix_decode_006 : PackedRawNatGrowth.readList 13 149 ridgeSupport52_rest_006 =
    (ridgeSupport52_suffix_006, ridgeSupport52_rest_011) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 117
    ridgeSupport52_rest_006 ridgeSupport52_rest_007 ridgeSupport52_rest_011
    ridgeSupport52_006 ridgeSupport52_suffix_007 ridgeSupport52_006_decode ridgeSupport52_suffix_decode_007
theorem ridgeSupport52_suffix_decode_005 : PackedRawNatGrowth.readList 13 181 ridgeSupport52_rest_005 =
    (ridgeSupport52_suffix_005, ridgeSupport52_rest_011) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 149
    ridgeSupport52_rest_005 ridgeSupport52_rest_006 ridgeSupport52_rest_011
    ridgeSupport52_005 ridgeSupport52_suffix_006 ridgeSupport52_005_decode ridgeSupport52_suffix_decode_006
theorem ridgeSupport52_suffix_decode_004 : PackedRawNatGrowth.readList 13 213 ridgeSupport52_rest_004 =
    (ridgeSupport52_suffix_004, ridgeSupport52_rest_011) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 181
    ridgeSupport52_rest_004 ridgeSupport52_rest_005 ridgeSupport52_rest_011
    ridgeSupport52_004 ridgeSupport52_suffix_005 ridgeSupport52_004_decode ridgeSupport52_suffix_decode_005
theorem ridgeSupport52_suffix_decode_003 : PackedRawNatGrowth.readList 13 245 ridgeSupport52_rest_003 =
    (ridgeSupport52_suffix_003, ridgeSupport52_rest_011) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 213
    ridgeSupport52_rest_003 ridgeSupport52_rest_004 ridgeSupport52_rest_011
    ridgeSupport52_003 ridgeSupport52_suffix_004 ridgeSupport52_003_decode ridgeSupport52_suffix_decode_004
theorem ridgeSupport52_suffix_decode_002 : PackedRawNatGrowth.readList 13 277 ridgeSupport52_rest_002 =
    (ridgeSupport52_suffix_002, ridgeSupport52_rest_011) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 245
    ridgeSupport52_rest_002 ridgeSupport52_rest_003 ridgeSupport52_rest_011
    ridgeSupport52_002 ridgeSupport52_suffix_003 ridgeSupport52_002_decode ridgeSupport52_suffix_decode_003
theorem ridgeSupport52_suffix_decode_001 : PackedRawNatGrowth.readList 13 309 ridgeSupport52_rest_001 =
    (ridgeSupport52_suffix_001, ridgeSupport52_rest_011) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 277
    ridgeSupport52_rest_001 ridgeSupport52_rest_002 ridgeSupport52_rest_011
    ridgeSupport52_001 ridgeSupport52_suffix_002 ridgeSupport52_001_decode ridgeSupport52_suffix_decode_002
theorem ridgeSupport52_suffix_decode_000 : PackedRawNatGrowth.readList 13 341 ridgeSupport52_rest_000 =
    (ridgeSupport52_suffix_000, ridgeSupport52_rest_011) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 309
    ridgeSupport52_rest_000 ridgeSupport52_rest_001 ridgeSupport52_rest_011
    ridgeSupport52_000 ridgeSupport52_suffix_001 ridgeSupport52_000_decode ridgeSupport52_suffix_decode_001
theorem ridgeSupport52_eq : candidateSupports 52 = ridgeSupport52_suffix_000 := by
  rw [ridgeSupport52_source]
  exact congrArg Prod.fst ridgeSupport52_suffix_decode_000
theorem ridgeTest_large_52 : ridgeTest 52 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [show candidateRows 52 = ridgeSupport52_suffix_000 from ridgeSupport52_eq]
    simp only [ridgeSupport52_suffix_000, ridgeSupport52_suffix_001, ridgeSupport52_suffix_002, ridgeSupport52_suffix_003, ridgeSupport52_suffix_004, ridgeSupport52_suffix_005, ridgeSupport52_suffix_006, ridgeSupport52_suffix_007, ridgeSupport52_suffix_008, ridgeSupport52_suffix_009, ridgeSupport52_suffix_010, ridgeSupport52_suffix_011, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport52_000_mask, ridgeSupport52_001_mask, ridgeSupport52_002_mask, ridgeSupport52_003_mask, ridgeSupport52_004_mask, ridgeSupport52_005_mask, ridgeSupport52_006_mask, ridgeSupport52_007_mask, ridgeSupport52_008_mask, ridgeSupport52_009_mask, ridgeSupport52_010_mask]
    decide +kernel
  · rw [show candidateRows 52 = ridgeSupport52_suffix_000 from ridgeSupport52_eq]
    simp only [ridgeSupport52_suffix_000, ridgeSupport52_suffix_001, ridgeSupport52_suffix_002, ridgeSupport52_suffix_003, ridgeSupport52_suffix_004, ridgeSupport52_suffix_005, ridgeSupport52_suffix_006, ridgeSupport52_suffix_007, ridgeSupport52_suffix_008, ridgeSupport52_suffix_009, ridgeSupport52_suffix_010, ridgeSupport52_suffix_011, List.all_append, List.all_nil, ridgeSupport52_000_checked, ridgeSupport52_001_checked, ridgeSupport52_002_checked, ridgeSupport52_003_checked, ridgeSupport52_004_checked, ridgeSupport52_005_checked, ridgeSupport52_006_checked, ridgeSupport52_007_checked, ridgeSupport52_008_checked, ridgeSupport52_009_checked, ridgeSupport52_010_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase03
