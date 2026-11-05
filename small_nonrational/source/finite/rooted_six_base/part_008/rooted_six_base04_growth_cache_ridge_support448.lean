module
prelude
public import RootedSixBase04GrowthCacheRidgeSupport448Part000
public import RootedSixBase04GrowthCacheRidgeSupport448Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase04
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport448_suffix_decode_015 : PackedRawNatGrowth.readList 12 0 ridgeSupport448_rest_015 =
    (ridgeSupport448_suffix_015, ridgeSupport448_rest_015) := by rfl
theorem ridgeSupport448_suffix_decode_014 : PackedRawNatGrowth.readList 12 15 ridgeSupport448_rest_014 =
    (ridgeSupport448_suffix_014, ridgeSupport448_rest_015) :=
  PackedRawNatGrowth.readList_append_of_eq 12 15 0
    ridgeSupport448_rest_014 ridgeSupport448_rest_015 ridgeSupport448_rest_015
    ridgeSupport448_014 ridgeSupport448_suffix_015 ridgeSupport448_014_decode ridgeSupport448_suffix_decode_015
theorem ridgeSupport448_suffix_decode_013 : PackedRawNatGrowth.readList 12 47 ridgeSupport448_rest_013 =
    (ridgeSupport448_suffix_013, ridgeSupport448_rest_015) :=
  PackedRawNatGrowth.readList_append_of_eq 12 32 15
    ridgeSupport448_rest_013 ridgeSupport448_rest_014 ridgeSupport448_rest_015
    ridgeSupport448_013 ridgeSupport448_suffix_014 ridgeSupport448_013_decode ridgeSupport448_suffix_decode_014
theorem ridgeSupport448_suffix_decode_012 : PackedRawNatGrowth.readList 12 79 ridgeSupport448_rest_012 =
    (ridgeSupport448_suffix_012, ridgeSupport448_rest_015) :=
  PackedRawNatGrowth.readList_append_of_eq 12 32 47
    ridgeSupport448_rest_012 ridgeSupport448_rest_013 ridgeSupport448_rest_015
    ridgeSupport448_012 ridgeSupport448_suffix_013 ridgeSupport448_012_decode ridgeSupport448_suffix_decode_013
theorem ridgeSupport448_suffix_decode_011 : PackedRawNatGrowth.readList 12 111 ridgeSupport448_rest_011 =
    (ridgeSupport448_suffix_011, ridgeSupport448_rest_015) :=
  PackedRawNatGrowth.readList_append_of_eq 12 32 79
    ridgeSupport448_rest_011 ridgeSupport448_rest_012 ridgeSupport448_rest_015
    ridgeSupport448_011 ridgeSupport448_suffix_012 ridgeSupport448_011_decode ridgeSupport448_suffix_decode_012
theorem ridgeSupport448_suffix_decode_010 : PackedRawNatGrowth.readList 12 143 ridgeSupport448_rest_010 =
    (ridgeSupport448_suffix_010, ridgeSupport448_rest_015) :=
  PackedRawNatGrowth.readList_append_of_eq 12 32 111
    ridgeSupport448_rest_010 ridgeSupport448_rest_011 ridgeSupport448_rest_015
    ridgeSupport448_010 ridgeSupport448_suffix_011 ridgeSupport448_010_decode ridgeSupport448_suffix_decode_011
theorem ridgeSupport448_suffix_decode_009 : PackedRawNatGrowth.readList 12 175 ridgeSupport448_rest_009 =
    (ridgeSupport448_suffix_009, ridgeSupport448_rest_015) :=
  PackedRawNatGrowth.readList_append_of_eq 12 32 143
    ridgeSupport448_rest_009 ridgeSupport448_rest_010 ridgeSupport448_rest_015
    ridgeSupport448_009 ridgeSupport448_suffix_010 ridgeSupport448_009_decode ridgeSupport448_suffix_decode_010
theorem ridgeSupport448_suffix_decode_008 : PackedRawNatGrowth.readList 12 207 ridgeSupport448_rest_008 =
    (ridgeSupport448_suffix_008, ridgeSupport448_rest_015) :=
  PackedRawNatGrowth.readList_append_of_eq 12 32 175
    ridgeSupport448_rest_008 ridgeSupport448_rest_009 ridgeSupport448_rest_015
    ridgeSupport448_008 ridgeSupport448_suffix_009 ridgeSupport448_008_decode ridgeSupport448_suffix_decode_009
theorem ridgeSupport448_suffix_decode_007 : PackedRawNatGrowth.readList 12 239 ridgeSupport448_rest_007 =
    (ridgeSupport448_suffix_007, ridgeSupport448_rest_015) :=
  PackedRawNatGrowth.readList_append_of_eq 12 32 207
    ridgeSupport448_rest_007 ridgeSupport448_rest_008 ridgeSupport448_rest_015
    ridgeSupport448_007 ridgeSupport448_suffix_008 ridgeSupport448_007_decode ridgeSupport448_suffix_decode_008
theorem ridgeSupport448_suffix_decode_006 : PackedRawNatGrowth.readList 12 271 ridgeSupport448_rest_006 =
    (ridgeSupport448_suffix_006, ridgeSupport448_rest_015) :=
  PackedRawNatGrowth.readList_append_of_eq 12 32 239
    ridgeSupport448_rest_006 ridgeSupport448_rest_007 ridgeSupport448_rest_015
    ridgeSupport448_006 ridgeSupport448_suffix_007 ridgeSupport448_006_decode ridgeSupport448_suffix_decode_007
theorem ridgeSupport448_suffix_decode_005 : PackedRawNatGrowth.readList 12 303 ridgeSupport448_rest_005 =
    (ridgeSupport448_suffix_005, ridgeSupport448_rest_015) :=
  PackedRawNatGrowth.readList_append_of_eq 12 32 271
    ridgeSupport448_rest_005 ridgeSupport448_rest_006 ridgeSupport448_rest_015
    ridgeSupport448_005 ridgeSupport448_suffix_006 ridgeSupport448_005_decode ridgeSupport448_suffix_decode_006
theorem ridgeSupport448_suffix_decode_004 : PackedRawNatGrowth.readList 12 335 ridgeSupport448_rest_004 =
    (ridgeSupport448_suffix_004, ridgeSupport448_rest_015) :=
  PackedRawNatGrowth.readList_append_of_eq 12 32 303
    ridgeSupport448_rest_004 ridgeSupport448_rest_005 ridgeSupport448_rest_015
    ridgeSupport448_004 ridgeSupport448_suffix_005 ridgeSupport448_004_decode ridgeSupport448_suffix_decode_005
theorem ridgeSupport448_suffix_decode_003 : PackedRawNatGrowth.readList 12 367 ridgeSupport448_rest_003 =
    (ridgeSupport448_suffix_003, ridgeSupport448_rest_015) :=
  PackedRawNatGrowth.readList_append_of_eq 12 32 335
    ridgeSupport448_rest_003 ridgeSupport448_rest_004 ridgeSupport448_rest_015
    ridgeSupport448_003 ridgeSupport448_suffix_004 ridgeSupport448_003_decode ridgeSupport448_suffix_decode_004
theorem ridgeSupport448_suffix_decode_002 : PackedRawNatGrowth.readList 12 399 ridgeSupport448_rest_002 =
    (ridgeSupport448_suffix_002, ridgeSupport448_rest_015) :=
  PackedRawNatGrowth.readList_append_of_eq 12 32 367
    ridgeSupport448_rest_002 ridgeSupport448_rest_003 ridgeSupport448_rest_015
    ridgeSupport448_002 ridgeSupport448_suffix_003 ridgeSupport448_002_decode ridgeSupport448_suffix_decode_003
theorem ridgeSupport448_suffix_decode_001 : PackedRawNatGrowth.readList 12 431 ridgeSupport448_rest_001 =
    (ridgeSupport448_suffix_001, ridgeSupport448_rest_015) :=
  PackedRawNatGrowth.readList_append_of_eq 12 32 399
    ridgeSupport448_rest_001 ridgeSupport448_rest_002 ridgeSupport448_rest_015
    ridgeSupport448_001 ridgeSupport448_suffix_002 ridgeSupport448_001_decode ridgeSupport448_suffix_decode_002
theorem ridgeSupport448_suffix_decode_000 : PackedRawNatGrowth.readList 12 463 ridgeSupport448_rest_000 =
    (ridgeSupport448_suffix_000, ridgeSupport448_rest_015) :=
  PackedRawNatGrowth.readList_append_of_eq 12 32 431
    ridgeSupport448_rest_000 ridgeSupport448_rest_001 ridgeSupport448_rest_015
    ridgeSupport448_000 ridgeSupport448_suffix_001 ridgeSupport448_000_decode ridgeSupport448_suffix_decode_001
theorem ridgeSupport448_eq : candidateRows 448 = ridgeSupport448_suffix_000 := by
  change candidateSupports 448 = ridgeSupport448_suffix_000
  rw [ridgeSupport448_source]
  exact congrArg Prod.fst ridgeSupport448_suffix_decode_000
theorem ridgeTest_large_448 : ridgeTest 448 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport448_eq]
    simp only [ridgeSupport448_suffix_000, ridgeSupport448_suffix_001, ridgeSupport448_suffix_002, ridgeSupport448_suffix_003, ridgeSupport448_suffix_004, ridgeSupport448_suffix_005, ridgeSupport448_suffix_006, ridgeSupport448_suffix_007, ridgeSupport448_suffix_008, ridgeSupport448_suffix_009, ridgeSupport448_suffix_010, ridgeSupport448_suffix_011, ridgeSupport448_suffix_012, ridgeSupport448_suffix_013, ridgeSupport448_suffix_014, ridgeSupport448_suffix_015, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport448_000_mask, ridgeSupport448_001_mask, ridgeSupport448_002_mask, ridgeSupport448_003_mask, ridgeSupport448_004_mask, ridgeSupport448_005_mask, ridgeSupport448_006_mask, ridgeSupport448_007_mask, ridgeSupport448_008_mask, ridgeSupport448_009_mask, ridgeSupport448_010_mask, ridgeSupport448_011_mask, ridgeSupport448_012_mask, ridgeSupport448_013_mask, ridgeSupport448_014_mask]
    decide +kernel
  · rw [ridgeSupport448_eq]
    simp only [ridgeSupport448_suffix_000, ridgeSupport448_suffix_001, ridgeSupport448_suffix_002, ridgeSupport448_suffix_003, ridgeSupport448_suffix_004, ridgeSupport448_suffix_005, ridgeSupport448_suffix_006, ridgeSupport448_suffix_007, ridgeSupport448_suffix_008, ridgeSupport448_suffix_009, ridgeSupport448_suffix_010, ridgeSupport448_suffix_011, ridgeSupport448_suffix_012, ridgeSupport448_suffix_013, ridgeSupport448_suffix_014, ridgeSupport448_suffix_015, List.all_append, List.all_nil, ridgeSupport448_000_checked, ridgeSupport448_001_checked, ridgeSupport448_002_checked, ridgeSupport448_003_checked, ridgeSupport448_004_checked, ridgeSupport448_005_checked, ridgeSupport448_006_checked, ridgeSupport448_007_checked, ridgeSupport448_008_checked, ridgeSupport448_009_checked, ridgeSupport448_010_checked, ridgeSupport448_011_checked, ridgeSupport448_012_checked, ridgeSupport448_013_checked, ridgeSupport448_014_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase04
