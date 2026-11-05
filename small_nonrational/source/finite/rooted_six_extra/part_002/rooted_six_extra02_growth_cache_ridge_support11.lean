module
prelude
public import RootedSixExtra02GrowthCacheRidgeSupport11Part000
public import RootedSixExtra02GrowthCacheRidgeSupport11Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra02
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport11_suffix_decode_016 : PackedRawNatGrowth.readList 13 0 ridgeSupport11_rest_016 =
    (ridgeSupport11_suffix_016, ridgeSupport11_rest_016) := by rfl
theorem ridgeSupport11_suffix_decode_015 : PackedRawNatGrowth.readList 13 5 ridgeSupport11_rest_015 =
    (ridgeSupport11_suffix_015, ridgeSupport11_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 13 5 0
    ridgeSupport11_rest_015 ridgeSupport11_rest_016 ridgeSupport11_rest_016
    ridgeSupport11_015 ridgeSupport11_suffix_016 ridgeSupport11_015_decode ridgeSupport11_suffix_decode_016
theorem ridgeSupport11_suffix_decode_014 : PackedRawNatGrowth.readList 13 37 ridgeSupport11_rest_014 =
    (ridgeSupport11_suffix_014, ridgeSupport11_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 5
    ridgeSupport11_rest_014 ridgeSupport11_rest_015 ridgeSupport11_rest_016
    ridgeSupport11_014 ridgeSupport11_suffix_015 ridgeSupport11_014_decode ridgeSupport11_suffix_decode_015
theorem ridgeSupport11_suffix_decode_013 : PackedRawNatGrowth.readList 13 69 ridgeSupport11_rest_013 =
    (ridgeSupport11_suffix_013, ridgeSupport11_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 37
    ridgeSupport11_rest_013 ridgeSupport11_rest_014 ridgeSupport11_rest_016
    ridgeSupport11_013 ridgeSupport11_suffix_014 ridgeSupport11_013_decode ridgeSupport11_suffix_decode_014
theorem ridgeSupport11_suffix_decode_012 : PackedRawNatGrowth.readList 13 101 ridgeSupport11_rest_012 =
    (ridgeSupport11_suffix_012, ridgeSupport11_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 69
    ridgeSupport11_rest_012 ridgeSupport11_rest_013 ridgeSupport11_rest_016
    ridgeSupport11_012 ridgeSupport11_suffix_013 ridgeSupport11_012_decode ridgeSupport11_suffix_decode_013
theorem ridgeSupport11_suffix_decode_011 : PackedRawNatGrowth.readList 13 133 ridgeSupport11_rest_011 =
    (ridgeSupport11_suffix_011, ridgeSupport11_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 101
    ridgeSupport11_rest_011 ridgeSupport11_rest_012 ridgeSupport11_rest_016
    ridgeSupport11_011 ridgeSupport11_suffix_012 ridgeSupport11_011_decode ridgeSupport11_suffix_decode_012
theorem ridgeSupport11_suffix_decode_010 : PackedRawNatGrowth.readList 13 165 ridgeSupport11_rest_010 =
    (ridgeSupport11_suffix_010, ridgeSupport11_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 133
    ridgeSupport11_rest_010 ridgeSupport11_rest_011 ridgeSupport11_rest_016
    ridgeSupport11_010 ridgeSupport11_suffix_011 ridgeSupport11_010_decode ridgeSupport11_suffix_decode_011
theorem ridgeSupport11_suffix_decode_009 : PackedRawNatGrowth.readList 13 197 ridgeSupport11_rest_009 =
    (ridgeSupport11_suffix_009, ridgeSupport11_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 165
    ridgeSupport11_rest_009 ridgeSupport11_rest_010 ridgeSupport11_rest_016
    ridgeSupport11_009 ridgeSupport11_suffix_010 ridgeSupport11_009_decode ridgeSupport11_suffix_decode_010
theorem ridgeSupport11_suffix_decode_008 : PackedRawNatGrowth.readList 13 229 ridgeSupport11_rest_008 =
    (ridgeSupport11_suffix_008, ridgeSupport11_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 197
    ridgeSupport11_rest_008 ridgeSupport11_rest_009 ridgeSupport11_rest_016
    ridgeSupport11_008 ridgeSupport11_suffix_009 ridgeSupport11_008_decode ridgeSupport11_suffix_decode_009
theorem ridgeSupport11_suffix_decode_007 : PackedRawNatGrowth.readList 13 261 ridgeSupport11_rest_007 =
    (ridgeSupport11_suffix_007, ridgeSupport11_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 229
    ridgeSupport11_rest_007 ridgeSupport11_rest_008 ridgeSupport11_rest_016
    ridgeSupport11_007 ridgeSupport11_suffix_008 ridgeSupport11_007_decode ridgeSupport11_suffix_decode_008
theorem ridgeSupport11_suffix_decode_006 : PackedRawNatGrowth.readList 13 293 ridgeSupport11_rest_006 =
    (ridgeSupport11_suffix_006, ridgeSupport11_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 261
    ridgeSupport11_rest_006 ridgeSupport11_rest_007 ridgeSupport11_rest_016
    ridgeSupport11_006 ridgeSupport11_suffix_007 ridgeSupport11_006_decode ridgeSupport11_suffix_decode_007
theorem ridgeSupport11_suffix_decode_005 : PackedRawNatGrowth.readList 13 325 ridgeSupport11_rest_005 =
    (ridgeSupport11_suffix_005, ridgeSupport11_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 293
    ridgeSupport11_rest_005 ridgeSupport11_rest_006 ridgeSupport11_rest_016
    ridgeSupport11_005 ridgeSupport11_suffix_006 ridgeSupport11_005_decode ridgeSupport11_suffix_decode_006
theorem ridgeSupport11_suffix_decode_004 : PackedRawNatGrowth.readList 13 357 ridgeSupport11_rest_004 =
    (ridgeSupport11_suffix_004, ridgeSupport11_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 325
    ridgeSupport11_rest_004 ridgeSupport11_rest_005 ridgeSupport11_rest_016
    ridgeSupport11_004 ridgeSupport11_suffix_005 ridgeSupport11_004_decode ridgeSupport11_suffix_decode_005
theorem ridgeSupport11_suffix_decode_003 : PackedRawNatGrowth.readList 13 389 ridgeSupport11_rest_003 =
    (ridgeSupport11_suffix_003, ridgeSupport11_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 357
    ridgeSupport11_rest_003 ridgeSupport11_rest_004 ridgeSupport11_rest_016
    ridgeSupport11_003 ridgeSupport11_suffix_004 ridgeSupport11_003_decode ridgeSupport11_suffix_decode_004
theorem ridgeSupport11_suffix_decode_002 : PackedRawNatGrowth.readList 13 421 ridgeSupport11_rest_002 =
    (ridgeSupport11_suffix_002, ridgeSupport11_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 389
    ridgeSupport11_rest_002 ridgeSupport11_rest_003 ridgeSupport11_rest_016
    ridgeSupport11_002 ridgeSupport11_suffix_003 ridgeSupport11_002_decode ridgeSupport11_suffix_decode_003
theorem ridgeSupport11_suffix_decode_001 : PackedRawNatGrowth.readList 13 453 ridgeSupport11_rest_001 =
    (ridgeSupport11_suffix_001, ridgeSupport11_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 421
    ridgeSupport11_rest_001 ridgeSupport11_rest_002 ridgeSupport11_rest_016
    ridgeSupport11_001 ridgeSupport11_suffix_002 ridgeSupport11_001_decode ridgeSupport11_suffix_decode_002
theorem ridgeSupport11_suffix_decode_000 : PackedRawNatGrowth.readList 13 485 ridgeSupport11_rest_000 =
    (ridgeSupport11_suffix_000, ridgeSupport11_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 453
    ridgeSupport11_rest_000 ridgeSupport11_rest_001 ridgeSupport11_rest_016
    ridgeSupport11_000 ridgeSupport11_suffix_001 ridgeSupport11_000_decode ridgeSupport11_suffix_decode_001
theorem ridgeSupport11_eq : candidateRows 11 = ridgeSupport11_suffix_000 := by
  change candidateSupports 11 = ridgeSupport11_suffix_000
  rw [ridgeSupport11_source]
  exact congrArg Prod.fst ridgeSupport11_suffix_decode_000
theorem ridgeTest_large_11 : ridgeTest 11 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport11_eq]
    simp only [ridgeSupport11_suffix_000, ridgeSupport11_suffix_001, ridgeSupport11_suffix_002, ridgeSupport11_suffix_003, ridgeSupport11_suffix_004, ridgeSupport11_suffix_005, ridgeSupport11_suffix_006, ridgeSupport11_suffix_007, ridgeSupport11_suffix_008, ridgeSupport11_suffix_009, ridgeSupport11_suffix_010, ridgeSupport11_suffix_011, ridgeSupport11_suffix_012, ridgeSupport11_suffix_013, ridgeSupport11_suffix_014, ridgeSupport11_suffix_015, ridgeSupport11_suffix_016, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport11_000_mask, ridgeSupport11_001_mask, ridgeSupport11_002_mask, ridgeSupport11_003_mask, ridgeSupport11_004_mask, ridgeSupport11_005_mask, ridgeSupport11_006_mask, ridgeSupport11_007_mask, ridgeSupport11_008_mask, ridgeSupport11_009_mask, ridgeSupport11_010_mask, ridgeSupport11_011_mask, ridgeSupport11_012_mask, ridgeSupport11_013_mask, ridgeSupport11_014_mask, ridgeSupport11_015_mask]
    decide +kernel
  · rw [ridgeSupport11_eq]
    simp only [ridgeSupport11_suffix_000, ridgeSupport11_suffix_001, ridgeSupport11_suffix_002, ridgeSupport11_suffix_003, ridgeSupport11_suffix_004, ridgeSupport11_suffix_005, ridgeSupport11_suffix_006, ridgeSupport11_suffix_007, ridgeSupport11_suffix_008, ridgeSupport11_suffix_009, ridgeSupport11_suffix_010, ridgeSupport11_suffix_011, ridgeSupport11_suffix_012, ridgeSupport11_suffix_013, ridgeSupport11_suffix_014, ridgeSupport11_suffix_015, ridgeSupport11_suffix_016, List.all_append, List.all_nil, ridgeSupport11_000_checked, ridgeSupport11_001_checked, ridgeSupport11_002_checked, ridgeSupport11_003_checked, ridgeSupport11_004_checked, ridgeSupport11_005_checked, ridgeSupport11_006_checked, ridgeSupport11_007_checked, ridgeSupport11_008_checked, ridgeSupport11_009_checked, ridgeSupport11_010_checked, ridgeSupport11_011_checked, ridgeSupport11_012_checked, ridgeSupport11_013_checked, ridgeSupport11_014_checked, ridgeSupport11_015_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixExtra02
