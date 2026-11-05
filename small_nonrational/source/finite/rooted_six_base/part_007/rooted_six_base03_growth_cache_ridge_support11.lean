module
prelude
public import RootedSixBase03GrowthCacheRidgeSupport11Part000
public import RootedSixBase03GrowthCacheRidgeSupport11Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase03
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport11_suffix_decode_011 : PackedRawNatGrowth.readList 13 0 ridgeSupport11_rest_011 =
    (ridgeSupport11_suffix_011, ridgeSupport11_rest_011) := by rfl
theorem ridgeSupport11_suffix_decode_010 : PackedRawNatGrowth.readList 13 21 ridgeSupport11_rest_010 =
    (ridgeSupport11_suffix_010, ridgeSupport11_rest_011) :=
  PackedRawNatGrowth.readList_append_of_eq 13 21 0
    ridgeSupport11_rest_010 ridgeSupport11_rest_011 ridgeSupport11_rest_011
    ridgeSupport11_010 ridgeSupport11_suffix_011 ridgeSupport11_010_decode ridgeSupport11_suffix_decode_011
theorem ridgeSupport11_suffix_decode_009 : PackedRawNatGrowth.readList 13 53 ridgeSupport11_rest_009 =
    (ridgeSupport11_suffix_009, ridgeSupport11_rest_011) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 21
    ridgeSupport11_rest_009 ridgeSupport11_rest_010 ridgeSupport11_rest_011
    ridgeSupport11_009 ridgeSupport11_suffix_010 ridgeSupport11_009_decode ridgeSupport11_suffix_decode_010
theorem ridgeSupport11_suffix_decode_008 : PackedRawNatGrowth.readList 13 85 ridgeSupport11_rest_008 =
    (ridgeSupport11_suffix_008, ridgeSupport11_rest_011) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 53
    ridgeSupport11_rest_008 ridgeSupport11_rest_009 ridgeSupport11_rest_011
    ridgeSupport11_008 ridgeSupport11_suffix_009 ridgeSupport11_008_decode ridgeSupport11_suffix_decode_009
theorem ridgeSupport11_suffix_decode_007 : PackedRawNatGrowth.readList 13 117 ridgeSupport11_rest_007 =
    (ridgeSupport11_suffix_007, ridgeSupport11_rest_011) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 85
    ridgeSupport11_rest_007 ridgeSupport11_rest_008 ridgeSupport11_rest_011
    ridgeSupport11_007 ridgeSupport11_suffix_008 ridgeSupport11_007_decode ridgeSupport11_suffix_decode_008
theorem ridgeSupport11_suffix_decode_006 : PackedRawNatGrowth.readList 13 149 ridgeSupport11_rest_006 =
    (ridgeSupport11_suffix_006, ridgeSupport11_rest_011) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 117
    ridgeSupport11_rest_006 ridgeSupport11_rest_007 ridgeSupport11_rest_011
    ridgeSupport11_006 ridgeSupport11_suffix_007 ridgeSupport11_006_decode ridgeSupport11_suffix_decode_007
theorem ridgeSupport11_suffix_decode_005 : PackedRawNatGrowth.readList 13 181 ridgeSupport11_rest_005 =
    (ridgeSupport11_suffix_005, ridgeSupport11_rest_011) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 149
    ridgeSupport11_rest_005 ridgeSupport11_rest_006 ridgeSupport11_rest_011
    ridgeSupport11_005 ridgeSupport11_suffix_006 ridgeSupport11_005_decode ridgeSupport11_suffix_decode_006
theorem ridgeSupport11_suffix_decode_004 : PackedRawNatGrowth.readList 13 213 ridgeSupport11_rest_004 =
    (ridgeSupport11_suffix_004, ridgeSupport11_rest_011) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 181
    ridgeSupport11_rest_004 ridgeSupport11_rest_005 ridgeSupport11_rest_011
    ridgeSupport11_004 ridgeSupport11_suffix_005 ridgeSupport11_004_decode ridgeSupport11_suffix_decode_005
theorem ridgeSupport11_suffix_decode_003 : PackedRawNatGrowth.readList 13 245 ridgeSupport11_rest_003 =
    (ridgeSupport11_suffix_003, ridgeSupport11_rest_011) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 213
    ridgeSupport11_rest_003 ridgeSupport11_rest_004 ridgeSupport11_rest_011
    ridgeSupport11_003 ridgeSupport11_suffix_004 ridgeSupport11_003_decode ridgeSupport11_suffix_decode_004
theorem ridgeSupport11_suffix_decode_002 : PackedRawNatGrowth.readList 13 277 ridgeSupport11_rest_002 =
    (ridgeSupport11_suffix_002, ridgeSupport11_rest_011) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 245
    ridgeSupport11_rest_002 ridgeSupport11_rest_003 ridgeSupport11_rest_011
    ridgeSupport11_002 ridgeSupport11_suffix_003 ridgeSupport11_002_decode ridgeSupport11_suffix_decode_003
theorem ridgeSupport11_suffix_decode_001 : PackedRawNatGrowth.readList 13 309 ridgeSupport11_rest_001 =
    (ridgeSupport11_suffix_001, ridgeSupport11_rest_011) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 277
    ridgeSupport11_rest_001 ridgeSupport11_rest_002 ridgeSupport11_rest_011
    ridgeSupport11_001 ridgeSupport11_suffix_002 ridgeSupport11_001_decode ridgeSupport11_suffix_decode_002
theorem ridgeSupport11_suffix_decode_000 : PackedRawNatGrowth.readList 13 341 ridgeSupport11_rest_000 =
    (ridgeSupport11_suffix_000, ridgeSupport11_rest_011) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 309
    ridgeSupport11_rest_000 ridgeSupport11_rest_001 ridgeSupport11_rest_011
    ridgeSupport11_000 ridgeSupport11_suffix_001 ridgeSupport11_000_decode ridgeSupport11_suffix_decode_001
theorem ridgeSupport11_eq : candidateSupports 11 = ridgeSupport11_suffix_000 := by
  rw [ridgeSupport11_source]
  exact congrArg Prod.fst ridgeSupport11_suffix_decode_000
theorem ridgeTest_large_11 : ridgeTest 11 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [show candidateRows 11 = ridgeSupport11_suffix_000 from ridgeSupport11_eq]
    simp only [ridgeSupport11_suffix_000, ridgeSupport11_suffix_001, ridgeSupport11_suffix_002, ridgeSupport11_suffix_003, ridgeSupport11_suffix_004, ridgeSupport11_suffix_005, ridgeSupport11_suffix_006, ridgeSupport11_suffix_007, ridgeSupport11_suffix_008, ridgeSupport11_suffix_009, ridgeSupport11_suffix_010, ridgeSupport11_suffix_011, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport11_000_mask, ridgeSupport11_001_mask, ridgeSupport11_002_mask, ridgeSupport11_003_mask, ridgeSupport11_004_mask, ridgeSupport11_005_mask, ridgeSupport11_006_mask, ridgeSupport11_007_mask, ridgeSupport11_008_mask, ridgeSupport11_009_mask, ridgeSupport11_010_mask]
    decide +kernel
  · rw [show candidateRows 11 = ridgeSupport11_suffix_000 from ridgeSupport11_eq]
    simp only [ridgeSupport11_suffix_000, ridgeSupport11_suffix_001, ridgeSupport11_suffix_002, ridgeSupport11_suffix_003, ridgeSupport11_suffix_004, ridgeSupport11_suffix_005, ridgeSupport11_suffix_006, ridgeSupport11_suffix_007, ridgeSupport11_suffix_008, ridgeSupport11_suffix_009, ridgeSupport11_suffix_010, ridgeSupport11_suffix_011, List.all_append, List.all_nil, ridgeSupport11_000_checked, ridgeSupport11_001_checked, ridgeSupport11_002_checked, ridgeSupport11_003_checked, ridgeSupport11_004_checked, ridgeSupport11_005_checked, ridgeSupport11_006_checked, ridgeSupport11_007_checked, ridgeSupport11_008_checked, ridgeSupport11_009_checked, ridgeSupport11_010_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase03
