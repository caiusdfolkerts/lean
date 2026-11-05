module
prelude
public import RootedSixBase02GrowthCacheRidgeSupport800Part000
public import RootedSixBase02GrowthCacheRidgeSupport800Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase02
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport800_suffix_decode_013 : PackedRawNatGrowth.readList 13 0 ridgeSupport800_rest_013 =
    (ridgeSupport800_suffix_013, ridgeSupport800_rest_013) := by rfl
theorem ridgeSupport800_suffix_decode_012 : PackedRawNatGrowth.readList 13 15 ridgeSupport800_rest_012 =
    (ridgeSupport800_suffix_012, ridgeSupport800_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 13 15 0
    ridgeSupport800_rest_012 ridgeSupport800_rest_013 ridgeSupport800_rest_013
    ridgeSupport800_012 ridgeSupport800_suffix_013 ridgeSupport800_012_decode ridgeSupport800_suffix_decode_013
theorem ridgeSupport800_suffix_decode_011 : PackedRawNatGrowth.readList 13 47 ridgeSupport800_rest_011 =
    (ridgeSupport800_suffix_011, ridgeSupport800_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 15
    ridgeSupport800_rest_011 ridgeSupport800_rest_012 ridgeSupport800_rest_013
    ridgeSupport800_011 ridgeSupport800_suffix_012 ridgeSupport800_011_decode ridgeSupport800_suffix_decode_012
theorem ridgeSupport800_suffix_decode_010 : PackedRawNatGrowth.readList 13 79 ridgeSupport800_rest_010 =
    (ridgeSupport800_suffix_010, ridgeSupport800_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 47
    ridgeSupport800_rest_010 ridgeSupport800_rest_011 ridgeSupport800_rest_013
    ridgeSupport800_010 ridgeSupport800_suffix_011 ridgeSupport800_010_decode ridgeSupport800_suffix_decode_011
theorem ridgeSupport800_suffix_decode_009 : PackedRawNatGrowth.readList 13 111 ridgeSupport800_rest_009 =
    (ridgeSupport800_suffix_009, ridgeSupport800_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 79
    ridgeSupport800_rest_009 ridgeSupport800_rest_010 ridgeSupport800_rest_013
    ridgeSupport800_009 ridgeSupport800_suffix_010 ridgeSupport800_009_decode ridgeSupport800_suffix_decode_010
theorem ridgeSupport800_suffix_decode_008 : PackedRawNatGrowth.readList 13 143 ridgeSupport800_rest_008 =
    (ridgeSupport800_suffix_008, ridgeSupport800_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 111
    ridgeSupport800_rest_008 ridgeSupport800_rest_009 ridgeSupport800_rest_013
    ridgeSupport800_008 ridgeSupport800_suffix_009 ridgeSupport800_008_decode ridgeSupport800_suffix_decode_009
theorem ridgeSupport800_suffix_decode_007 : PackedRawNatGrowth.readList 13 175 ridgeSupport800_rest_007 =
    (ridgeSupport800_suffix_007, ridgeSupport800_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 143
    ridgeSupport800_rest_007 ridgeSupport800_rest_008 ridgeSupport800_rest_013
    ridgeSupport800_007 ridgeSupport800_suffix_008 ridgeSupport800_007_decode ridgeSupport800_suffix_decode_008
theorem ridgeSupport800_suffix_decode_006 : PackedRawNatGrowth.readList 13 207 ridgeSupport800_rest_006 =
    (ridgeSupport800_suffix_006, ridgeSupport800_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 175
    ridgeSupport800_rest_006 ridgeSupport800_rest_007 ridgeSupport800_rest_013
    ridgeSupport800_006 ridgeSupport800_suffix_007 ridgeSupport800_006_decode ridgeSupport800_suffix_decode_007
theorem ridgeSupport800_suffix_decode_005 : PackedRawNatGrowth.readList 13 239 ridgeSupport800_rest_005 =
    (ridgeSupport800_suffix_005, ridgeSupport800_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 207
    ridgeSupport800_rest_005 ridgeSupport800_rest_006 ridgeSupport800_rest_013
    ridgeSupport800_005 ridgeSupport800_suffix_006 ridgeSupport800_005_decode ridgeSupport800_suffix_decode_006
theorem ridgeSupport800_suffix_decode_004 : PackedRawNatGrowth.readList 13 271 ridgeSupport800_rest_004 =
    (ridgeSupport800_suffix_004, ridgeSupport800_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 239
    ridgeSupport800_rest_004 ridgeSupport800_rest_005 ridgeSupport800_rest_013
    ridgeSupport800_004 ridgeSupport800_suffix_005 ridgeSupport800_004_decode ridgeSupport800_suffix_decode_005
theorem ridgeSupport800_suffix_decode_003 : PackedRawNatGrowth.readList 13 303 ridgeSupport800_rest_003 =
    (ridgeSupport800_suffix_003, ridgeSupport800_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 271
    ridgeSupport800_rest_003 ridgeSupport800_rest_004 ridgeSupport800_rest_013
    ridgeSupport800_003 ridgeSupport800_suffix_004 ridgeSupport800_003_decode ridgeSupport800_suffix_decode_004
theorem ridgeSupport800_suffix_decode_002 : PackedRawNatGrowth.readList 13 335 ridgeSupport800_rest_002 =
    (ridgeSupport800_suffix_002, ridgeSupport800_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 303
    ridgeSupport800_rest_002 ridgeSupport800_rest_003 ridgeSupport800_rest_013
    ridgeSupport800_002 ridgeSupport800_suffix_003 ridgeSupport800_002_decode ridgeSupport800_suffix_decode_003
theorem ridgeSupport800_suffix_decode_001 : PackedRawNatGrowth.readList 13 367 ridgeSupport800_rest_001 =
    (ridgeSupport800_suffix_001, ridgeSupport800_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 335
    ridgeSupport800_rest_001 ridgeSupport800_rest_002 ridgeSupport800_rest_013
    ridgeSupport800_001 ridgeSupport800_suffix_002 ridgeSupport800_001_decode ridgeSupport800_suffix_decode_002
theorem ridgeSupport800_suffix_decode_000 : PackedRawNatGrowth.readList 13 399 ridgeSupport800_rest_000 =
    (ridgeSupport800_suffix_000, ridgeSupport800_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 367
    ridgeSupport800_rest_000 ridgeSupport800_rest_001 ridgeSupport800_rest_013
    ridgeSupport800_000 ridgeSupport800_suffix_001 ridgeSupport800_000_decode ridgeSupport800_suffix_decode_001
theorem ridgeSupport800_eq : candidateRows 800 = ridgeSupport800_suffix_000 := by
  change candidateSupports 800 = ridgeSupport800_suffix_000
  rw [ridgeSupport800_source]
  exact congrArg Prod.fst ridgeSupport800_suffix_decode_000
theorem ridgeTest_large_800 : ridgeTest 800 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport800_eq]
    simp only [ridgeSupport800_suffix_000, ridgeSupport800_suffix_001, ridgeSupport800_suffix_002, ridgeSupport800_suffix_003, ridgeSupport800_suffix_004, ridgeSupport800_suffix_005, ridgeSupport800_suffix_006, ridgeSupport800_suffix_007, ridgeSupport800_suffix_008, ridgeSupport800_suffix_009, ridgeSupport800_suffix_010, ridgeSupport800_suffix_011, ridgeSupport800_suffix_012, ridgeSupport800_suffix_013, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport800_000_mask, ridgeSupport800_001_mask, ridgeSupport800_002_mask, ridgeSupport800_003_mask, ridgeSupport800_004_mask, ridgeSupport800_005_mask, ridgeSupport800_006_mask, ridgeSupport800_007_mask, ridgeSupport800_008_mask, ridgeSupport800_009_mask, ridgeSupport800_010_mask, ridgeSupport800_011_mask, ridgeSupport800_012_mask]
    decide +kernel
  · rw [ridgeSupport800_eq]
    simp only [ridgeSupport800_suffix_000, ridgeSupport800_suffix_001, ridgeSupport800_suffix_002, ridgeSupport800_suffix_003, ridgeSupport800_suffix_004, ridgeSupport800_suffix_005, ridgeSupport800_suffix_006, ridgeSupport800_suffix_007, ridgeSupport800_suffix_008, ridgeSupport800_suffix_009, ridgeSupport800_suffix_010, ridgeSupport800_suffix_011, ridgeSupport800_suffix_012, ridgeSupport800_suffix_013, List.all_append, List.all_nil, ridgeSupport800_000_checked, ridgeSupport800_001_checked, ridgeSupport800_002_checked, ridgeSupport800_003_checked, ridgeSupport800_004_checked, ridgeSupport800_005_checked, ridgeSupport800_006_checked, ridgeSupport800_007_checked, ridgeSupport800_008_checked, ridgeSupport800_009_checked, ridgeSupport800_010_checked, ridgeSupport800_011_checked, ridgeSupport800_012_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase02
