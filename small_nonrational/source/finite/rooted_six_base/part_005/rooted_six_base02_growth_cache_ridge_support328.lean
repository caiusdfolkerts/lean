module
prelude
public import RootedSixBase02GrowthCacheRidgeSupport328Part000
public import RootedSixBase02GrowthCacheRidgeSupport328Part001
public import RootedSixBase02GrowthCacheRidgeSupport328Part002
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase02
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport328_suffix_decode_017 : PackedRawNatGrowth.readList 13 0 ridgeSupport328_rest_017 =
    (ridgeSupport328_suffix_017, ridgeSupport328_rest_017) := by rfl
theorem ridgeSupport328_suffix_decode_016 : PackedRawNatGrowth.readList 13 30 ridgeSupport328_rest_016 =
    (ridgeSupport328_suffix_016, ridgeSupport328_rest_017) :=
  PackedRawNatGrowth.readList_append_of_eq 13 30 0
    ridgeSupport328_rest_016 ridgeSupport328_rest_017 ridgeSupport328_rest_017
    ridgeSupport328_016 ridgeSupport328_suffix_017 ridgeSupport328_016_decode ridgeSupport328_suffix_decode_017
theorem ridgeSupport328_suffix_decode_015 : PackedRawNatGrowth.readList 13 62 ridgeSupport328_rest_015 =
    (ridgeSupport328_suffix_015, ridgeSupport328_rest_017) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 30
    ridgeSupport328_rest_015 ridgeSupport328_rest_016 ridgeSupport328_rest_017
    ridgeSupport328_015 ridgeSupport328_suffix_016 ridgeSupport328_015_decode ridgeSupport328_suffix_decode_016
theorem ridgeSupport328_suffix_decode_014 : PackedRawNatGrowth.readList 13 94 ridgeSupport328_rest_014 =
    (ridgeSupport328_suffix_014, ridgeSupport328_rest_017) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 62
    ridgeSupport328_rest_014 ridgeSupport328_rest_015 ridgeSupport328_rest_017
    ridgeSupport328_014 ridgeSupport328_suffix_015 ridgeSupport328_014_decode ridgeSupport328_suffix_decode_015
theorem ridgeSupport328_suffix_decode_013 : PackedRawNatGrowth.readList 13 126 ridgeSupport328_rest_013 =
    (ridgeSupport328_suffix_013, ridgeSupport328_rest_017) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 94
    ridgeSupport328_rest_013 ridgeSupport328_rest_014 ridgeSupport328_rest_017
    ridgeSupport328_013 ridgeSupport328_suffix_014 ridgeSupport328_013_decode ridgeSupport328_suffix_decode_014
theorem ridgeSupport328_suffix_decode_012 : PackedRawNatGrowth.readList 13 158 ridgeSupport328_rest_012 =
    (ridgeSupport328_suffix_012, ridgeSupport328_rest_017) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 126
    ridgeSupport328_rest_012 ridgeSupport328_rest_013 ridgeSupport328_rest_017
    ridgeSupport328_012 ridgeSupport328_suffix_013 ridgeSupport328_012_decode ridgeSupport328_suffix_decode_013
theorem ridgeSupport328_suffix_decode_011 : PackedRawNatGrowth.readList 13 190 ridgeSupport328_rest_011 =
    (ridgeSupport328_suffix_011, ridgeSupport328_rest_017) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 158
    ridgeSupport328_rest_011 ridgeSupport328_rest_012 ridgeSupport328_rest_017
    ridgeSupport328_011 ridgeSupport328_suffix_012 ridgeSupport328_011_decode ridgeSupport328_suffix_decode_012
theorem ridgeSupport328_suffix_decode_010 : PackedRawNatGrowth.readList 13 222 ridgeSupport328_rest_010 =
    (ridgeSupport328_suffix_010, ridgeSupport328_rest_017) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 190
    ridgeSupport328_rest_010 ridgeSupport328_rest_011 ridgeSupport328_rest_017
    ridgeSupport328_010 ridgeSupport328_suffix_011 ridgeSupport328_010_decode ridgeSupport328_suffix_decode_011
theorem ridgeSupport328_suffix_decode_009 : PackedRawNatGrowth.readList 13 254 ridgeSupport328_rest_009 =
    (ridgeSupport328_suffix_009, ridgeSupport328_rest_017) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 222
    ridgeSupport328_rest_009 ridgeSupport328_rest_010 ridgeSupport328_rest_017
    ridgeSupport328_009 ridgeSupport328_suffix_010 ridgeSupport328_009_decode ridgeSupport328_suffix_decode_010
theorem ridgeSupport328_suffix_decode_008 : PackedRawNatGrowth.readList 13 286 ridgeSupport328_rest_008 =
    (ridgeSupport328_suffix_008, ridgeSupport328_rest_017) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 254
    ridgeSupport328_rest_008 ridgeSupport328_rest_009 ridgeSupport328_rest_017
    ridgeSupport328_008 ridgeSupport328_suffix_009 ridgeSupport328_008_decode ridgeSupport328_suffix_decode_009
theorem ridgeSupport328_suffix_decode_007 : PackedRawNatGrowth.readList 13 318 ridgeSupport328_rest_007 =
    (ridgeSupport328_suffix_007, ridgeSupport328_rest_017) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 286
    ridgeSupport328_rest_007 ridgeSupport328_rest_008 ridgeSupport328_rest_017
    ridgeSupport328_007 ridgeSupport328_suffix_008 ridgeSupport328_007_decode ridgeSupport328_suffix_decode_008
theorem ridgeSupport328_suffix_decode_006 : PackedRawNatGrowth.readList 13 350 ridgeSupport328_rest_006 =
    (ridgeSupport328_suffix_006, ridgeSupport328_rest_017) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 318
    ridgeSupport328_rest_006 ridgeSupport328_rest_007 ridgeSupport328_rest_017
    ridgeSupport328_006 ridgeSupport328_suffix_007 ridgeSupport328_006_decode ridgeSupport328_suffix_decode_007
theorem ridgeSupport328_suffix_decode_005 : PackedRawNatGrowth.readList 13 382 ridgeSupport328_rest_005 =
    (ridgeSupport328_suffix_005, ridgeSupport328_rest_017) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 350
    ridgeSupport328_rest_005 ridgeSupport328_rest_006 ridgeSupport328_rest_017
    ridgeSupport328_005 ridgeSupport328_suffix_006 ridgeSupport328_005_decode ridgeSupport328_suffix_decode_006
theorem ridgeSupport328_suffix_decode_004 : PackedRawNatGrowth.readList 13 414 ridgeSupport328_rest_004 =
    (ridgeSupport328_suffix_004, ridgeSupport328_rest_017) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 382
    ridgeSupport328_rest_004 ridgeSupport328_rest_005 ridgeSupport328_rest_017
    ridgeSupport328_004 ridgeSupport328_suffix_005 ridgeSupport328_004_decode ridgeSupport328_suffix_decode_005
theorem ridgeSupport328_suffix_decode_003 : PackedRawNatGrowth.readList 13 446 ridgeSupport328_rest_003 =
    (ridgeSupport328_suffix_003, ridgeSupport328_rest_017) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 414
    ridgeSupport328_rest_003 ridgeSupport328_rest_004 ridgeSupport328_rest_017
    ridgeSupport328_003 ridgeSupport328_suffix_004 ridgeSupport328_003_decode ridgeSupport328_suffix_decode_004
theorem ridgeSupport328_suffix_decode_002 : PackedRawNatGrowth.readList 13 478 ridgeSupport328_rest_002 =
    (ridgeSupport328_suffix_002, ridgeSupport328_rest_017) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 446
    ridgeSupport328_rest_002 ridgeSupport328_rest_003 ridgeSupport328_rest_017
    ridgeSupport328_002 ridgeSupport328_suffix_003 ridgeSupport328_002_decode ridgeSupport328_suffix_decode_003
theorem ridgeSupport328_suffix_decode_001 : PackedRawNatGrowth.readList 13 510 ridgeSupport328_rest_001 =
    (ridgeSupport328_suffix_001, ridgeSupport328_rest_017) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 478
    ridgeSupport328_rest_001 ridgeSupport328_rest_002 ridgeSupport328_rest_017
    ridgeSupport328_001 ridgeSupport328_suffix_002 ridgeSupport328_001_decode ridgeSupport328_suffix_decode_002
theorem ridgeSupport328_suffix_decode_000 : PackedRawNatGrowth.readList 13 542 ridgeSupport328_rest_000 =
    (ridgeSupport328_suffix_000, ridgeSupport328_rest_017) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 510
    ridgeSupport328_rest_000 ridgeSupport328_rest_001 ridgeSupport328_rest_017
    ridgeSupport328_000 ridgeSupport328_suffix_001 ridgeSupport328_000_decode ridgeSupport328_suffix_decode_001
theorem ridgeSupport328_eq : candidateRows 328 = ridgeSupport328_suffix_000 := by
  change candidateSupports 328 = ridgeSupport328_suffix_000
  rw [ridgeSupport328_source]
  exact congrArg Prod.fst ridgeSupport328_suffix_decode_000
theorem ridgeTest_large_328 : ridgeTest 328 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport328_eq]
    simp only [ridgeSupport328_suffix_000, ridgeSupport328_suffix_001, ridgeSupport328_suffix_002, ridgeSupport328_suffix_003, ridgeSupport328_suffix_004, ridgeSupport328_suffix_005, ridgeSupport328_suffix_006, ridgeSupport328_suffix_007, ridgeSupport328_suffix_008, ridgeSupport328_suffix_009, ridgeSupport328_suffix_010, ridgeSupport328_suffix_011, ridgeSupport328_suffix_012, ridgeSupport328_suffix_013, ridgeSupport328_suffix_014, ridgeSupport328_suffix_015, ridgeSupport328_suffix_016, ridgeSupport328_suffix_017, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport328_000_mask, ridgeSupport328_001_mask, ridgeSupport328_002_mask, ridgeSupport328_003_mask, ridgeSupport328_004_mask, ridgeSupport328_005_mask, ridgeSupport328_006_mask, ridgeSupport328_007_mask, ridgeSupport328_008_mask, ridgeSupport328_009_mask, ridgeSupport328_010_mask, ridgeSupport328_011_mask, ridgeSupport328_012_mask, ridgeSupport328_013_mask, ridgeSupport328_014_mask, ridgeSupport328_015_mask, ridgeSupport328_016_mask]
    decide +kernel
  · rw [ridgeSupport328_eq]
    simp only [ridgeSupport328_suffix_000, ridgeSupport328_suffix_001, ridgeSupport328_suffix_002, ridgeSupport328_suffix_003, ridgeSupport328_suffix_004, ridgeSupport328_suffix_005, ridgeSupport328_suffix_006, ridgeSupport328_suffix_007, ridgeSupport328_suffix_008, ridgeSupport328_suffix_009, ridgeSupport328_suffix_010, ridgeSupport328_suffix_011, ridgeSupport328_suffix_012, ridgeSupport328_suffix_013, ridgeSupport328_suffix_014, ridgeSupport328_suffix_015, ridgeSupport328_suffix_016, ridgeSupport328_suffix_017, List.all_append, List.all_nil, ridgeSupport328_000_checked, ridgeSupport328_001_checked, ridgeSupport328_002_checked, ridgeSupport328_003_checked, ridgeSupport328_004_checked, ridgeSupport328_005_checked, ridgeSupport328_006_checked, ridgeSupport328_007_checked, ridgeSupport328_008_checked, ridgeSupport328_009_checked, ridgeSupport328_010_checked, ridgeSupport328_011_checked, ridgeSupport328_012_checked, ridgeSupport328_013_checked, ridgeSupport328_014_checked, ridgeSupport328_015_checked, ridgeSupport328_016_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase02
