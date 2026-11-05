module
prelude
public import RootedSixBase02GrowthCacheRidgeSupport577Part000
public import RootedSixBase02GrowthCacheRidgeSupport577Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase02
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport577_suffix_decode_013 : PackedRawNatGrowth.readList 13 0 ridgeSupport577_rest_013 =
    (ridgeSupport577_suffix_013, ridgeSupport577_rest_013) := by rfl
theorem ridgeSupport577_suffix_decode_012 : PackedRawNatGrowth.readList 13 15 ridgeSupport577_rest_012 =
    (ridgeSupport577_suffix_012, ridgeSupport577_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 13 15 0
    ridgeSupport577_rest_012 ridgeSupport577_rest_013 ridgeSupport577_rest_013
    ridgeSupport577_012 ridgeSupport577_suffix_013 ridgeSupport577_012_decode ridgeSupport577_suffix_decode_013
theorem ridgeSupport577_suffix_decode_011 : PackedRawNatGrowth.readList 13 47 ridgeSupport577_rest_011 =
    (ridgeSupport577_suffix_011, ridgeSupport577_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 15
    ridgeSupport577_rest_011 ridgeSupport577_rest_012 ridgeSupport577_rest_013
    ridgeSupport577_011 ridgeSupport577_suffix_012 ridgeSupport577_011_decode ridgeSupport577_suffix_decode_012
theorem ridgeSupport577_suffix_decode_010 : PackedRawNatGrowth.readList 13 79 ridgeSupport577_rest_010 =
    (ridgeSupport577_suffix_010, ridgeSupport577_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 47
    ridgeSupport577_rest_010 ridgeSupport577_rest_011 ridgeSupport577_rest_013
    ridgeSupport577_010 ridgeSupport577_suffix_011 ridgeSupport577_010_decode ridgeSupport577_suffix_decode_011
theorem ridgeSupport577_suffix_decode_009 : PackedRawNatGrowth.readList 13 111 ridgeSupport577_rest_009 =
    (ridgeSupport577_suffix_009, ridgeSupport577_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 79
    ridgeSupport577_rest_009 ridgeSupport577_rest_010 ridgeSupport577_rest_013
    ridgeSupport577_009 ridgeSupport577_suffix_010 ridgeSupport577_009_decode ridgeSupport577_suffix_decode_010
theorem ridgeSupport577_suffix_decode_008 : PackedRawNatGrowth.readList 13 143 ridgeSupport577_rest_008 =
    (ridgeSupport577_suffix_008, ridgeSupport577_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 111
    ridgeSupport577_rest_008 ridgeSupport577_rest_009 ridgeSupport577_rest_013
    ridgeSupport577_008 ridgeSupport577_suffix_009 ridgeSupport577_008_decode ridgeSupport577_suffix_decode_009
theorem ridgeSupport577_suffix_decode_007 : PackedRawNatGrowth.readList 13 175 ridgeSupport577_rest_007 =
    (ridgeSupport577_suffix_007, ridgeSupport577_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 143
    ridgeSupport577_rest_007 ridgeSupport577_rest_008 ridgeSupport577_rest_013
    ridgeSupport577_007 ridgeSupport577_suffix_008 ridgeSupport577_007_decode ridgeSupport577_suffix_decode_008
theorem ridgeSupport577_suffix_decode_006 : PackedRawNatGrowth.readList 13 207 ridgeSupport577_rest_006 =
    (ridgeSupport577_suffix_006, ridgeSupport577_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 175
    ridgeSupport577_rest_006 ridgeSupport577_rest_007 ridgeSupport577_rest_013
    ridgeSupport577_006 ridgeSupport577_suffix_007 ridgeSupport577_006_decode ridgeSupport577_suffix_decode_007
theorem ridgeSupport577_suffix_decode_005 : PackedRawNatGrowth.readList 13 239 ridgeSupport577_rest_005 =
    (ridgeSupport577_suffix_005, ridgeSupport577_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 207
    ridgeSupport577_rest_005 ridgeSupport577_rest_006 ridgeSupport577_rest_013
    ridgeSupport577_005 ridgeSupport577_suffix_006 ridgeSupport577_005_decode ridgeSupport577_suffix_decode_006
theorem ridgeSupport577_suffix_decode_004 : PackedRawNatGrowth.readList 13 271 ridgeSupport577_rest_004 =
    (ridgeSupport577_suffix_004, ridgeSupport577_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 239
    ridgeSupport577_rest_004 ridgeSupport577_rest_005 ridgeSupport577_rest_013
    ridgeSupport577_004 ridgeSupport577_suffix_005 ridgeSupport577_004_decode ridgeSupport577_suffix_decode_005
theorem ridgeSupport577_suffix_decode_003 : PackedRawNatGrowth.readList 13 303 ridgeSupport577_rest_003 =
    (ridgeSupport577_suffix_003, ridgeSupport577_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 271
    ridgeSupport577_rest_003 ridgeSupport577_rest_004 ridgeSupport577_rest_013
    ridgeSupport577_003 ridgeSupport577_suffix_004 ridgeSupport577_003_decode ridgeSupport577_suffix_decode_004
theorem ridgeSupport577_suffix_decode_002 : PackedRawNatGrowth.readList 13 335 ridgeSupport577_rest_002 =
    (ridgeSupport577_suffix_002, ridgeSupport577_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 303
    ridgeSupport577_rest_002 ridgeSupport577_rest_003 ridgeSupport577_rest_013
    ridgeSupport577_002 ridgeSupport577_suffix_003 ridgeSupport577_002_decode ridgeSupport577_suffix_decode_003
theorem ridgeSupport577_suffix_decode_001 : PackedRawNatGrowth.readList 13 367 ridgeSupport577_rest_001 =
    (ridgeSupport577_suffix_001, ridgeSupport577_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 335
    ridgeSupport577_rest_001 ridgeSupport577_rest_002 ridgeSupport577_rest_013
    ridgeSupport577_001 ridgeSupport577_suffix_002 ridgeSupport577_001_decode ridgeSupport577_suffix_decode_002
theorem ridgeSupport577_suffix_decode_000 : PackedRawNatGrowth.readList 13 399 ridgeSupport577_rest_000 =
    (ridgeSupport577_suffix_000, ridgeSupport577_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 367
    ridgeSupport577_rest_000 ridgeSupport577_rest_001 ridgeSupport577_rest_013
    ridgeSupport577_000 ridgeSupport577_suffix_001 ridgeSupport577_000_decode ridgeSupport577_suffix_decode_001
theorem ridgeSupport577_eq : candidateRows 577 = ridgeSupport577_suffix_000 := by
  change candidateSupports 577 = ridgeSupport577_suffix_000
  rw [ridgeSupport577_source]
  exact congrArg Prod.fst ridgeSupport577_suffix_decode_000
theorem ridgeTest_large_577 : ridgeTest 577 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport577_eq]
    simp only [ridgeSupport577_suffix_000, ridgeSupport577_suffix_001, ridgeSupport577_suffix_002, ridgeSupport577_suffix_003, ridgeSupport577_suffix_004, ridgeSupport577_suffix_005, ridgeSupport577_suffix_006, ridgeSupport577_suffix_007, ridgeSupport577_suffix_008, ridgeSupport577_suffix_009, ridgeSupport577_suffix_010, ridgeSupport577_suffix_011, ridgeSupport577_suffix_012, ridgeSupport577_suffix_013, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport577_000_mask, ridgeSupport577_001_mask, ridgeSupport577_002_mask, ridgeSupport577_003_mask, ridgeSupport577_004_mask, ridgeSupport577_005_mask, ridgeSupport577_006_mask, ridgeSupport577_007_mask, ridgeSupport577_008_mask, ridgeSupport577_009_mask, ridgeSupport577_010_mask, ridgeSupport577_011_mask, ridgeSupport577_012_mask]
    decide +kernel
  · rw [ridgeSupport577_eq]
    simp only [ridgeSupport577_suffix_000, ridgeSupport577_suffix_001, ridgeSupport577_suffix_002, ridgeSupport577_suffix_003, ridgeSupport577_suffix_004, ridgeSupport577_suffix_005, ridgeSupport577_suffix_006, ridgeSupport577_suffix_007, ridgeSupport577_suffix_008, ridgeSupport577_suffix_009, ridgeSupport577_suffix_010, ridgeSupport577_suffix_011, ridgeSupport577_suffix_012, ridgeSupport577_suffix_013, List.all_append, List.all_nil, ridgeSupport577_000_checked, ridgeSupport577_001_checked, ridgeSupport577_002_checked, ridgeSupport577_003_checked, ridgeSupport577_004_checked, ridgeSupport577_005_checked, ridgeSupport577_006_checked, ridgeSupport577_007_checked, ridgeSupport577_008_checked, ridgeSupport577_009_checked, ridgeSupport577_010_checked, ridgeSupport577_011_checked, ridgeSupport577_012_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase02
