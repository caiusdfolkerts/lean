module
prelude
public import RootedSixBase02GrowthCacheRidgeSupport200Part000
public import RootedSixBase02GrowthCacheRidgeSupport200Part001
public import RootedSixBase02GrowthCacheRidgeSupport200Part002
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase02
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport200_suffix_decode_017 : PackedRawNatGrowth.readList 13 0 ridgeSupport200_rest_017 =
    (ridgeSupport200_suffix_017, ridgeSupport200_rest_017) := by rfl
theorem ridgeSupport200_suffix_decode_016 : PackedRawNatGrowth.readList 13 30 ridgeSupport200_rest_016 =
    (ridgeSupport200_suffix_016, ridgeSupport200_rest_017) :=
  PackedRawNatGrowth.readList_append_of_eq 13 30 0
    ridgeSupport200_rest_016 ridgeSupport200_rest_017 ridgeSupport200_rest_017
    ridgeSupport200_016 ridgeSupport200_suffix_017 ridgeSupport200_016_decode ridgeSupport200_suffix_decode_017
theorem ridgeSupport200_suffix_decode_015 : PackedRawNatGrowth.readList 13 62 ridgeSupport200_rest_015 =
    (ridgeSupport200_suffix_015, ridgeSupport200_rest_017) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 30
    ridgeSupport200_rest_015 ridgeSupport200_rest_016 ridgeSupport200_rest_017
    ridgeSupport200_015 ridgeSupport200_suffix_016 ridgeSupport200_015_decode ridgeSupport200_suffix_decode_016
theorem ridgeSupport200_suffix_decode_014 : PackedRawNatGrowth.readList 13 94 ridgeSupport200_rest_014 =
    (ridgeSupport200_suffix_014, ridgeSupport200_rest_017) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 62
    ridgeSupport200_rest_014 ridgeSupport200_rest_015 ridgeSupport200_rest_017
    ridgeSupport200_014 ridgeSupport200_suffix_015 ridgeSupport200_014_decode ridgeSupport200_suffix_decode_015
theorem ridgeSupport200_suffix_decode_013 : PackedRawNatGrowth.readList 13 126 ridgeSupport200_rest_013 =
    (ridgeSupport200_suffix_013, ridgeSupport200_rest_017) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 94
    ridgeSupport200_rest_013 ridgeSupport200_rest_014 ridgeSupport200_rest_017
    ridgeSupport200_013 ridgeSupport200_suffix_014 ridgeSupport200_013_decode ridgeSupport200_suffix_decode_014
theorem ridgeSupport200_suffix_decode_012 : PackedRawNatGrowth.readList 13 158 ridgeSupport200_rest_012 =
    (ridgeSupport200_suffix_012, ridgeSupport200_rest_017) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 126
    ridgeSupport200_rest_012 ridgeSupport200_rest_013 ridgeSupport200_rest_017
    ridgeSupport200_012 ridgeSupport200_suffix_013 ridgeSupport200_012_decode ridgeSupport200_suffix_decode_013
theorem ridgeSupport200_suffix_decode_011 : PackedRawNatGrowth.readList 13 190 ridgeSupport200_rest_011 =
    (ridgeSupport200_suffix_011, ridgeSupport200_rest_017) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 158
    ridgeSupport200_rest_011 ridgeSupport200_rest_012 ridgeSupport200_rest_017
    ridgeSupport200_011 ridgeSupport200_suffix_012 ridgeSupport200_011_decode ridgeSupport200_suffix_decode_012
theorem ridgeSupport200_suffix_decode_010 : PackedRawNatGrowth.readList 13 222 ridgeSupport200_rest_010 =
    (ridgeSupport200_suffix_010, ridgeSupport200_rest_017) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 190
    ridgeSupport200_rest_010 ridgeSupport200_rest_011 ridgeSupport200_rest_017
    ridgeSupport200_010 ridgeSupport200_suffix_011 ridgeSupport200_010_decode ridgeSupport200_suffix_decode_011
theorem ridgeSupport200_suffix_decode_009 : PackedRawNatGrowth.readList 13 254 ridgeSupport200_rest_009 =
    (ridgeSupport200_suffix_009, ridgeSupport200_rest_017) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 222
    ridgeSupport200_rest_009 ridgeSupport200_rest_010 ridgeSupport200_rest_017
    ridgeSupport200_009 ridgeSupport200_suffix_010 ridgeSupport200_009_decode ridgeSupport200_suffix_decode_010
theorem ridgeSupport200_suffix_decode_008 : PackedRawNatGrowth.readList 13 286 ridgeSupport200_rest_008 =
    (ridgeSupport200_suffix_008, ridgeSupport200_rest_017) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 254
    ridgeSupport200_rest_008 ridgeSupport200_rest_009 ridgeSupport200_rest_017
    ridgeSupport200_008 ridgeSupport200_suffix_009 ridgeSupport200_008_decode ridgeSupport200_suffix_decode_009
theorem ridgeSupport200_suffix_decode_007 : PackedRawNatGrowth.readList 13 318 ridgeSupport200_rest_007 =
    (ridgeSupport200_suffix_007, ridgeSupport200_rest_017) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 286
    ridgeSupport200_rest_007 ridgeSupport200_rest_008 ridgeSupport200_rest_017
    ridgeSupport200_007 ridgeSupport200_suffix_008 ridgeSupport200_007_decode ridgeSupport200_suffix_decode_008
theorem ridgeSupport200_suffix_decode_006 : PackedRawNatGrowth.readList 13 350 ridgeSupport200_rest_006 =
    (ridgeSupport200_suffix_006, ridgeSupport200_rest_017) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 318
    ridgeSupport200_rest_006 ridgeSupport200_rest_007 ridgeSupport200_rest_017
    ridgeSupport200_006 ridgeSupport200_suffix_007 ridgeSupport200_006_decode ridgeSupport200_suffix_decode_007
theorem ridgeSupport200_suffix_decode_005 : PackedRawNatGrowth.readList 13 382 ridgeSupport200_rest_005 =
    (ridgeSupport200_suffix_005, ridgeSupport200_rest_017) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 350
    ridgeSupport200_rest_005 ridgeSupport200_rest_006 ridgeSupport200_rest_017
    ridgeSupport200_005 ridgeSupport200_suffix_006 ridgeSupport200_005_decode ridgeSupport200_suffix_decode_006
theorem ridgeSupport200_suffix_decode_004 : PackedRawNatGrowth.readList 13 414 ridgeSupport200_rest_004 =
    (ridgeSupport200_suffix_004, ridgeSupport200_rest_017) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 382
    ridgeSupport200_rest_004 ridgeSupport200_rest_005 ridgeSupport200_rest_017
    ridgeSupport200_004 ridgeSupport200_suffix_005 ridgeSupport200_004_decode ridgeSupport200_suffix_decode_005
theorem ridgeSupport200_suffix_decode_003 : PackedRawNatGrowth.readList 13 446 ridgeSupport200_rest_003 =
    (ridgeSupport200_suffix_003, ridgeSupport200_rest_017) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 414
    ridgeSupport200_rest_003 ridgeSupport200_rest_004 ridgeSupport200_rest_017
    ridgeSupport200_003 ridgeSupport200_suffix_004 ridgeSupport200_003_decode ridgeSupport200_suffix_decode_004
theorem ridgeSupport200_suffix_decode_002 : PackedRawNatGrowth.readList 13 478 ridgeSupport200_rest_002 =
    (ridgeSupport200_suffix_002, ridgeSupport200_rest_017) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 446
    ridgeSupport200_rest_002 ridgeSupport200_rest_003 ridgeSupport200_rest_017
    ridgeSupport200_002 ridgeSupport200_suffix_003 ridgeSupport200_002_decode ridgeSupport200_suffix_decode_003
theorem ridgeSupport200_suffix_decode_001 : PackedRawNatGrowth.readList 13 510 ridgeSupport200_rest_001 =
    (ridgeSupport200_suffix_001, ridgeSupport200_rest_017) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 478
    ridgeSupport200_rest_001 ridgeSupport200_rest_002 ridgeSupport200_rest_017
    ridgeSupport200_001 ridgeSupport200_suffix_002 ridgeSupport200_001_decode ridgeSupport200_suffix_decode_002
theorem ridgeSupport200_suffix_decode_000 : PackedRawNatGrowth.readList 13 542 ridgeSupport200_rest_000 =
    (ridgeSupport200_suffix_000, ridgeSupport200_rest_017) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 510
    ridgeSupport200_rest_000 ridgeSupport200_rest_001 ridgeSupport200_rest_017
    ridgeSupport200_000 ridgeSupport200_suffix_001 ridgeSupport200_000_decode ridgeSupport200_suffix_decode_001
theorem ridgeSupport200_eq : candidateRows 200 = ridgeSupport200_suffix_000 := by
  change candidateSupports 200 = ridgeSupport200_suffix_000
  rw [ridgeSupport200_source]
  exact congrArg Prod.fst ridgeSupport200_suffix_decode_000
theorem ridgeTest_large_200 : ridgeTest 200 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport200_eq]
    simp only [ridgeSupport200_suffix_000, ridgeSupport200_suffix_001, ridgeSupport200_suffix_002, ridgeSupport200_suffix_003, ridgeSupport200_suffix_004, ridgeSupport200_suffix_005, ridgeSupport200_suffix_006, ridgeSupport200_suffix_007, ridgeSupport200_suffix_008, ridgeSupport200_suffix_009, ridgeSupport200_suffix_010, ridgeSupport200_suffix_011, ridgeSupport200_suffix_012, ridgeSupport200_suffix_013, ridgeSupport200_suffix_014, ridgeSupport200_suffix_015, ridgeSupport200_suffix_016, ridgeSupport200_suffix_017, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport200_000_mask, ridgeSupport200_001_mask, ridgeSupport200_002_mask, ridgeSupport200_003_mask, ridgeSupport200_004_mask, ridgeSupport200_005_mask, ridgeSupport200_006_mask, ridgeSupport200_007_mask, ridgeSupport200_008_mask, ridgeSupport200_009_mask, ridgeSupport200_010_mask, ridgeSupport200_011_mask, ridgeSupport200_012_mask, ridgeSupport200_013_mask, ridgeSupport200_014_mask, ridgeSupport200_015_mask, ridgeSupport200_016_mask]
    decide +kernel
  · rw [ridgeSupport200_eq]
    simp only [ridgeSupport200_suffix_000, ridgeSupport200_suffix_001, ridgeSupport200_suffix_002, ridgeSupport200_suffix_003, ridgeSupport200_suffix_004, ridgeSupport200_suffix_005, ridgeSupport200_suffix_006, ridgeSupport200_suffix_007, ridgeSupport200_suffix_008, ridgeSupport200_suffix_009, ridgeSupport200_suffix_010, ridgeSupport200_suffix_011, ridgeSupport200_suffix_012, ridgeSupport200_suffix_013, ridgeSupport200_suffix_014, ridgeSupport200_suffix_015, ridgeSupport200_suffix_016, ridgeSupport200_suffix_017, List.all_append, List.all_nil, ridgeSupport200_000_checked, ridgeSupport200_001_checked, ridgeSupport200_002_checked, ridgeSupport200_003_checked, ridgeSupport200_004_checked, ridgeSupport200_005_checked, ridgeSupport200_006_checked, ridgeSupport200_007_checked, ridgeSupport200_008_checked, ridgeSupport200_009_checked, ridgeSupport200_010_checked, ridgeSupport200_011_checked, ridgeSupport200_012_checked, ridgeSupport200_013_checked, ridgeSupport200_014_checked, ridgeSupport200_015_checked, ridgeSupport200_016_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase02
