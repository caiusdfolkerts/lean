module
prelude
public import RootedSixBase02GrowthCacheRidgeSupport193Part000
public import RootedSixBase02GrowthCacheRidgeSupport193Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase02
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport193_suffix_decode_013 : PackedRawNatGrowth.readList 13 0 ridgeSupport193_rest_013 =
    (ridgeSupport193_suffix_013, ridgeSupport193_rest_013) := by rfl
theorem ridgeSupport193_suffix_decode_012 : PackedRawNatGrowth.readList 13 15 ridgeSupport193_rest_012 =
    (ridgeSupport193_suffix_012, ridgeSupport193_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 13 15 0
    ridgeSupport193_rest_012 ridgeSupport193_rest_013 ridgeSupport193_rest_013
    ridgeSupport193_012 ridgeSupport193_suffix_013 ridgeSupport193_012_decode ridgeSupport193_suffix_decode_013
theorem ridgeSupport193_suffix_decode_011 : PackedRawNatGrowth.readList 13 47 ridgeSupport193_rest_011 =
    (ridgeSupport193_suffix_011, ridgeSupport193_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 15
    ridgeSupport193_rest_011 ridgeSupport193_rest_012 ridgeSupport193_rest_013
    ridgeSupport193_011 ridgeSupport193_suffix_012 ridgeSupport193_011_decode ridgeSupport193_suffix_decode_012
theorem ridgeSupport193_suffix_decode_010 : PackedRawNatGrowth.readList 13 79 ridgeSupport193_rest_010 =
    (ridgeSupport193_suffix_010, ridgeSupport193_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 47
    ridgeSupport193_rest_010 ridgeSupport193_rest_011 ridgeSupport193_rest_013
    ridgeSupport193_010 ridgeSupport193_suffix_011 ridgeSupport193_010_decode ridgeSupport193_suffix_decode_011
theorem ridgeSupport193_suffix_decode_009 : PackedRawNatGrowth.readList 13 111 ridgeSupport193_rest_009 =
    (ridgeSupport193_suffix_009, ridgeSupport193_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 79
    ridgeSupport193_rest_009 ridgeSupport193_rest_010 ridgeSupport193_rest_013
    ridgeSupport193_009 ridgeSupport193_suffix_010 ridgeSupport193_009_decode ridgeSupport193_suffix_decode_010
theorem ridgeSupport193_suffix_decode_008 : PackedRawNatGrowth.readList 13 143 ridgeSupport193_rest_008 =
    (ridgeSupport193_suffix_008, ridgeSupport193_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 111
    ridgeSupport193_rest_008 ridgeSupport193_rest_009 ridgeSupport193_rest_013
    ridgeSupport193_008 ridgeSupport193_suffix_009 ridgeSupport193_008_decode ridgeSupport193_suffix_decode_009
theorem ridgeSupport193_suffix_decode_007 : PackedRawNatGrowth.readList 13 175 ridgeSupport193_rest_007 =
    (ridgeSupport193_suffix_007, ridgeSupport193_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 143
    ridgeSupport193_rest_007 ridgeSupport193_rest_008 ridgeSupport193_rest_013
    ridgeSupport193_007 ridgeSupport193_suffix_008 ridgeSupport193_007_decode ridgeSupport193_suffix_decode_008
theorem ridgeSupport193_suffix_decode_006 : PackedRawNatGrowth.readList 13 207 ridgeSupport193_rest_006 =
    (ridgeSupport193_suffix_006, ridgeSupport193_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 175
    ridgeSupport193_rest_006 ridgeSupport193_rest_007 ridgeSupport193_rest_013
    ridgeSupport193_006 ridgeSupport193_suffix_007 ridgeSupport193_006_decode ridgeSupport193_suffix_decode_007
theorem ridgeSupport193_suffix_decode_005 : PackedRawNatGrowth.readList 13 239 ridgeSupport193_rest_005 =
    (ridgeSupport193_suffix_005, ridgeSupport193_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 207
    ridgeSupport193_rest_005 ridgeSupport193_rest_006 ridgeSupport193_rest_013
    ridgeSupport193_005 ridgeSupport193_suffix_006 ridgeSupport193_005_decode ridgeSupport193_suffix_decode_006
theorem ridgeSupport193_suffix_decode_004 : PackedRawNatGrowth.readList 13 271 ridgeSupport193_rest_004 =
    (ridgeSupport193_suffix_004, ridgeSupport193_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 239
    ridgeSupport193_rest_004 ridgeSupport193_rest_005 ridgeSupport193_rest_013
    ridgeSupport193_004 ridgeSupport193_suffix_005 ridgeSupport193_004_decode ridgeSupport193_suffix_decode_005
theorem ridgeSupport193_suffix_decode_003 : PackedRawNatGrowth.readList 13 303 ridgeSupport193_rest_003 =
    (ridgeSupport193_suffix_003, ridgeSupport193_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 271
    ridgeSupport193_rest_003 ridgeSupport193_rest_004 ridgeSupport193_rest_013
    ridgeSupport193_003 ridgeSupport193_suffix_004 ridgeSupport193_003_decode ridgeSupport193_suffix_decode_004
theorem ridgeSupport193_suffix_decode_002 : PackedRawNatGrowth.readList 13 335 ridgeSupport193_rest_002 =
    (ridgeSupport193_suffix_002, ridgeSupport193_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 303
    ridgeSupport193_rest_002 ridgeSupport193_rest_003 ridgeSupport193_rest_013
    ridgeSupport193_002 ridgeSupport193_suffix_003 ridgeSupport193_002_decode ridgeSupport193_suffix_decode_003
theorem ridgeSupport193_suffix_decode_001 : PackedRawNatGrowth.readList 13 367 ridgeSupport193_rest_001 =
    (ridgeSupport193_suffix_001, ridgeSupport193_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 335
    ridgeSupport193_rest_001 ridgeSupport193_rest_002 ridgeSupport193_rest_013
    ridgeSupport193_001 ridgeSupport193_suffix_002 ridgeSupport193_001_decode ridgeSupport193_suffix_decode_002
theorem ridgeSupport193_suffix_decode_000 : PackedRawNatGrowth.readList 13 399 ridgeSupport193_rest_000 =
    (ridgeSupport193_suffix_000, ridgeSupport193_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 367
    ridgeSupport193_rest_000 ridgeSupport193_rest_001 ridgeSupport193_rest_013
    ridgeSupport193_000 ridgeSupport193_suffix_001 ridgeSupport193_000_decode ridgeSupport193_suffix_decode_001
theorem ridgeSupport193_eq : candidateRows 193 = ridgeSupport193_suffix_000 := by
  change candidateSupports 193 = ridgeSupport193_suffix_000
  rw [ridgeSupport193_source]
  exact congrArg Prod.fst ridgeSupport193_suffix_decode_000
theorem ridgeTest_large_193 : ridgeTest 193 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport193_eq]
    simp only [ridgeSupport193_suffix_000, ridgeSupport193_suffix_001, ridgeSupport193_suffix_002, ridgeSupport193_suffix_003, ridgeSupport193_suffix_004, ridgeSupport193_suffix_005, ridgeSupport193_suffix_006, ridgeSupport193_suffix_007, ridgeSupport193_suffix_008, ridgeSupport193_suffix_009, ridgeSupport193_suffix_010, ridgeSupport193_suffix_011, ridgeSupport193_suffix_012, ridgeSupport193_suffix_013, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport193_000_mask, ridgeSupport193_001_mask, ridgeSupport193_002_mask, ridgeSupport193_003_mask, ridgeSupport193_004_mask, ridgeSupport193_005_mask, ridgeSupport193_006_mask, ridgeSupport193_007_mask, ridgeSupport193_008_mask, ridgeSupport193_009_mask, ridgeSupport193_010_mask, ridgeSupport193_011_mask, ridgeSupport193_012_mask]
    decide +kernel
  · rw [ridgeSupport193_eq]
    simp only [ridgeSupport193_suffix_000, ridgeSupport193_suffix_001, ridgeSupport193_suffix_002, ridgeSupport193_suffix_003, ridgeSupport193_suffix_004, ridgeSupport193_suffix_005, ridgeSupport193_suffix_006, ridgeSupport193_suffix_007, ridgeSupport193_suffix_008, ridgeSupport193_suffix_009, ridgeSupport193_suffix_010, ridgeSupport193_suffix_011, ridgeSupport193_suffix_012, ridgeSupport193_suffix_013, List.all_append, List.all_nil, ridgeSupport193_000_checked, ridgeSupport193_001_checked, ridgeSupport193_002_checked, ridgeSupport193_003_checked, ridgeSupport193_004_checked, ridgeSupport193_005_checked, ridgeSupport193_006_checked, ridgeSupport193_007_checked, ridgeSupport193_008_checked, ridgeSupport193_009_checked, ridgeSupport193_010_checked, ridgeSupport193_011_checked, ridgeSupport193_012_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase02
