module
prelude
public import RootedSixBase03GrowthCacheRidgeSupport56Part000
public import RootedSixBase03GrowthCacheRidgeSupport56Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase03
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport56_suffix_decode_011 : PackedRawNatGrowth.readList 13 0 ridgeSupport56_rest_011 =
    (ridgeSupport56_suffix_011, ridgeSupport56_rest_011) := by rfl
theorem ridgeSupport56_suffix_decode_010 : PackedRawNatGrowth.readList 13 21 ridgeSupport56_rest_010 =
    (ridgeSupport56_suffix_010, ridgeSupport56_rest_011) :=
  PackedRawNatGrowth.readList_append_of_eq 13 21 0
    ridgeSupport56_rest_010 ridgeSupport56_rest_011 ridgeSupport56_rest_011
    ridgeSupport56_010 ridgeSupport56_suffix_011 ridgeSupport56_010_decode ridgeSupport56_suffix_decode_011
theorem ridgeSupport56_suffix_decode_009 : PackedRawNatGrowth.readList 13 53 ridgeSupport56_rest_009 =
    (ridgeSupport56_suffix_009, ridgeSupport56_rest_011) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 21
    ridgeSupport56_rest_009 ridgeSupport56_rest_010 ridgeSupport56_rest_011
    ridgeSupport56_009 ridgeSupport56_suffix_010 ridgeSupport56_009_decode ridgeSupport56_suffix_decode_010
theorem ridgeSupport56_suffix_decode_008 : PackedRawNatGrowth.readList 13 85 ridgeSupport56_rest_008 =
    (ridgeSupport56_suffix_008, ridgeSupport56_rest_011) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 53
    ridgeSupport56_rest_008 ridgeSupport56_rest_009 ridgeSupport56_rest_011
    ridgeSupport56_008 ridgeSupport56_suffix_009 ridgeSupport56_008_decode ridgeSupport56_suffix_decode_009
theorem ridgeSupport56_suffix_decode_007 : PackedRawNatGrowth.readList 13 117 ridgeSupport56_rest_007 =
    (ridgeSupport56_suffix_007, ridgeSupport56_rest_011) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 85
    ridgeSupport56_rest_007 ridgeSupport56_rest_008 ridgeSupport56_rest_011
    ridgeSupport56_007 ridgeSupport56_suffix_008 ridgeSupport56_007_decode ridgeSupport56_suffix_decode_008
theorem ridgeSupport56_suffix_decode_006 : PackedRawNatGrowth.readList 13 149 ridgeSupport56_rest_006 =
    (ridgeSupport56_suffix_006, ridgeSupport56_rest_011) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 117
    ridgeSupport56_rest_006 ridgeSupport56_rest_007 ridgeSupport56_rest_011
    ridgeSupport56_006 ridgeSupport56_suffix_007 ridgeSupport56_006_decode ridgeSupport56_suffix_decode_007
theorem ridgeSupport56_suffix_decode_005 : PackedRawNatGrowth.readList 13 181 ridgeSupport56_rest_005 =
    (ridgeSupport56_suffix_005, ridgeSupport56_rest_011) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 149
    ridgeSupport56_rest_005 ridgeSupport56_rest_006 ridgeSupport56_rest_011
    ridgeSupport56_005 ridgeSupport56_suffix_006 ridgeSupport56_005_decode ridgeSupport56_suffix_decode_006
theorem ridgeSupport56_suffix_decode_004 : PackedRawNatGrowth.readList 13 213 ridgeSupport56_rest_004 =
    (ridgeSupport56_suffix_004, ridgeSupport56_rest_011) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 181
    ridgeSupport56_rest_004 ridgeSupport56_rest_005 ridgeSupport56_rest_011
    ridgeSupport56_004 ridgeSupport56_suffix_005 ridgeSupport56_004_decode ridgeSupport56_suffix_decode_005
theorem ridgeSupport56_suffix_decode_003 : PackedRawNatGrowth.readList 13 245 ridgeSupport56_rest_003 =
    (ridgeSupport56_suffix_003, ridgeSupport56_rest_011) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 213
    ridgeSupport56_rest_003 ridgeSupport56_rest_004 ridgeSupport56_rest_011
    ridgeSupport56_003 ridgeSupport56_suffix_004 ridgeSupport56_003_decode ridgeSupport56_suffix_decode_004
theorem ridgeSupport56_suffix_decode_002 : PackedRawNatGrowth.readList 13 277 ridgeSupport56_rest_002 =
    (ridgeSupport56_suffix_002, ridgeSupport56_rest_011) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 245
    ridgeSupport56_rest_002 ridgeSupport56_rest_003 ridgeSupport56_rest_011
    ridgeSupport56_002 ridgeSupport56_suffix_003 ridgeSupport56_002_decode ridgeSupport56_suffix_decode_003
theorem ridgeSupport56_suffix_decode_001 : PackedRawNatGrowth.readList 13 309 ridgeSupport56_rest_001 =
    (ridgeSupport56_suffix_001, ridgeSupport56_rest_011) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 277
    ridgeSupport56_rest_001 ridgeSupport56_rest_002 ridgeSupport56_rest_011
    ridgeSupport56_001 ridgeSupport56_suffix_002 ridgeSupport56_001_decode ridgeSupport56_suffix_decode_002
theorem ridgeSupport56_suffix_decode_000 : PackedRawNatGrowth.readList 13 341 ridgeSupport56_rest_000 =
    (ridgeSupport56_suffix_000, ridgeSupport56_rest_011) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 309
    ridgeSupport56_rest_000 ridgeSupport56_rest_001 ridgeSupport56_rest_011
    ridgeSupport56_000 ridgeSupport56_suffix_001 ridgeSupport56_000_decode ridgeSupport56_suffix_decode_001
theorem ridgeSupport56_eq : candidateSupports 56 = ridgeSupport56_suffix_000 := by
  rw [ridgeSupport56_source]
  exact congrArg Prod.fst ridgeSupport56_suffix_decode_000
theorem ridgeTest_large_56 : ridgeTest 56 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [show candidateRows 56 = ridgeSupport56_suffix_000 from ridgeSupport56_eq]
    simp only [ridgeSupport56_suffix_000, ridgeSupport56_suffix_001, ridgeSupport56_suffix_002, ridgeSupport56_suffix_003, ridgeSupport56_suffix_004, ridgeSupport56_suffix_005, ridgeSupport56_suffix_006, ridgeSupport56_suffix_007, ridgeSupport56_suffix_008, ridgeSupport56_suffix_009, ridgeSupport56_suffix_010, ridgeSupport56_suffix_011, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport56_000_mask, ridgeSupport56_001_mask, ridgeSupport56_002_mask, ridgeSupport56_003_mask, ridgeSupport56_004_mask, ridgeSupport56_005_mask, ridgeSupport56_006_mask, ridgeSupport56_007_mask, ridgeSupport56_008_mask, ridgeSupport56_009_mask, ridgeSupport56_010_mask]
    decide +kernel
  · rw [show candidateRows 56 = ridgeSupport56_suffix_000 from ridgeSupport56_eq]
    simp only [ridgeSupport56_suffix_000, ridgeSupport56_suffix_001, ridgeSupport56_suffix_002, ridgeSupport56_suffix_003, ridgeSupport56_suffix_004, ridgeSupport56_suffix_005, ridgeSupport56_suffix_006, ridgeSupport56_suffix_007, ridgeSupport56_suffix_008, ridgeSupport56_suffix_009, ridgeSupport56_suffix_010, ridgeSupport56_suffix_011, List.all_append, List.all_nil, ridgeSupport56_000_checked, ridgeSupport56_001_checked, ridgeSupport56_002_checked, ridgeSupport56_003_checked, ridgeSupport56_004_checked, ridgeSupport56_005_checked, ridgeSupport56_006_checked, ridgeSupport56_007_checked, ridgeSupport56_008_checked, ridgeSupport56_009_checked, ridgeSupport56_010_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase03
